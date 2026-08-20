{-# OPTIONS --safe #-}

module Recursive.Corollaries where

open import Data.Empty using (⊥)
open import Recursive.Prelude using (_≡_)
open import Data.List.Base using ([])
open import Data.Product using (Σ-syntax ; _×_ ; _,_)

open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Evaluation
open import Recursive.Derivability
open import Recursive.Minimal using (derivableToMinimal)
open import Recursive.Inversion using (minimalTyEqHead ; TyHead ; tyHead)
open import Recursive.FullCanonicalForm

-- Valentini 3.10.8, restricted to the Treg fragment:
-- every closed derivable term has a canonical value.
evaluationTerm :
  {t : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t A)
  -> Σ[ g ∈ RawTerm ] t =>e g
evaluationTerm d with fullCanonicalFormTheorem d
... | g , ev , _ =
  g , ev

-- Valentini 3.10.7, for the Sigma type former present in Treg.
-- We return the evaluated pair and the derivable component typings; the
-- equivalence between the original term and the pair is included because the
-- full canonical-form theorem gives it for free.
sigmaExistential :
  {A B : RawType} {c : RawTerm}
  -> Derivable (hasTy [] c (tySigma A B))
  -> Σ[ a ∈ RawTerm ] Σ[ b ∈ RawTerm ]
       (c =>e tmPair a b)
     × Derivable (hasTy [] a A)
     × Derivable (hasTy [] b (subTy (singleSubst a) B))
     × Derivable (termEq [] c (tmPair a b) (tySigma A B))
sigmaExistential {A = A} {B = B} d with fullCanonicalFormTheorem d
... | tmPair a b , ev , canPairTm da db _ , ceq =
  a , b , ev , da , db , ceq

-- The general non-collapse statement: judgemental type equality never
-- relates types with different outermost formers, in any context and
-- for all five formers.  The named corollaries below are instances;
-- this is the statement the paper's "more generally" clause makes.

typeEqSameHead :
  {gamma : Ctx} {A B : RawType}
  -> Derivable (typeEq gamma A B)
  -> tyHead A ≡ tyHead B
typeEqSameHead d = minimalTyEqHead (derivableToMinimal d)

-- Treg has no empty type N0, so Valentini 3.10.5 cannot be stated literally.
-- The corresponding consistency statement for this fragment is non-collapse:
-- judgemental equality cannot identify distinct canonical type constructors.
topNotSigma :
  {A B : RawType}
  -> Derivable (typeEq [] tyTop (tySigma A B))
  -> ⊥
topNotSigma d with minimalTyEqHead (derivableToMinimal d)
... | ()

topNotEq :
  {A : RawType} {a b : RawTerm}
  -> Derivable (typeEq [] tyTop (tyEq A a b))
  -> ⊥
topNotEq d with minimalTyEqHead (derivableToMinimal d)
... | ()

topNotQtr :
  {A : RawType}
  -> Derivable (typeEq [] tyTop (tyQtr A))
  -> ⊥
topNotQtr d with minimalTyEqHead (derivableToMinimal d)
... | ()

sigmaNotTop :
  {A B : RawType}
  -> Derivable (typeEq [] (tySigma A B) tyTop)
  -> ⊥
sigmaNotTop d with minimalTyEqHead (derivableToMinimal d)
... | ()

eqNotTop :
  {A : RawType} {a b : RawTerm}
  -> Derivable (typeEq [] (tyEq A a b) tyTop)
  -> ⊥
eqNotTop d with minimalTyEqHead (derivableToMinimal d)
... | ()

qtrNotTop :
  {A : RawType}
  -> Derivable (typeEq [] (tyQtr A) tyTop)
  -> ⊥
qtrNotTop d with minimalTyEqHead (derivableToMinimal d)
... | ()

-- Strict type-syntax non-collapse, in the paper's terminology: Top and
-- Sigma(Top, Top) are isomorphic in every model -- a terminal object and a
-- product of two terminal objects -- yet the syntax does not identify them.
-- NOT consistency in the usual sense: pure Treg has no empty type and every
-- closed type is inhabited, so there is no false proposition to exhibit.
-- The statement with propositional content is noEqProofDistinctNumerals,
-- which needs Nat.
tregNonCollapse :
  Derivable (typeEq [] tyTop (tySigma tyTop tyTop))
  -> ⊥
tregNonCollapse = topNotSigma

natNoConfusion :
  Derivable (termEq [] tmZero (tmSuc tmZero) tyNat)
  -> ⊥
natNoConfusion d with fullCanonicalFormTheorem d
... | _ , _ , evalZero , evalSucV , () , _ , _

-- ── Canonicity, clause by clause ─────────────────────────────────
--
-- The judgemental-equality reading of the canonical form theorem at
-- each former: the theorem's derivable-equality field, specialised by
-- the type's canonical shape.  The N clauses live in
-- Recursive.Numerals (numeralForm, numeralDistinct).

canonicityTop :
  {t : RawTerm}
  -> Derivable (hasTy [] t tyTop)
  -> Derivable (termEq [] t tmStar tyTop)
canonicityTop d with fullCanonicalTerm d
... | _ , _ , canStarTm , dEq = dEq

canonicitySigma :
  {t : RawTerm} {A B : RawType}
  -> Derivable (hasTy [] t (tySigma A B))
  -> Σ[ a ∈ RawTerm ] Σ[ b ∈ RawTerm ]
       Derivable (termEq [] t (tmPair a b) (tySigma A B))
     × Derivable (hasTy [] a A)
     × Derivable (hasTy [] b (subTy (singleSubst a) B))
canonicitySigma d with fullCanonicalTerm d
... | _ , _ , canPairTm da db _ , dEq =
  _ , _ , dEq , da , db

canonicityEq :
  {p : RawTerm} {A : RawType} {a b : RawTerm}
  -> Derivable (hasTy [] p (tyEq A a b))
  -> Derivable (termEq [] p tmRefl (tyEq A a b))
canonicityEq d with fullCanonicalTerm d
... | _ , _ , canReflTm _ , dEq = dEq

canonicityQtr :
  {t : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t (tyQtr A))
  -> Σ[ a ∈ RawTerm ]
       Derivable (termEq [] t (tmClass a) (tyQtr A))
     × Derivable (hasTy [] a A)
canonicityQtr d with fullCanonicalTerm d
... | _ , _ , canClassTm da , dEq =
  _ , dEq , da
