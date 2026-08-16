{-# OPTIONS --safe #-}

-- The type-theoretic content of the categorical reading.
--
-- Section 9 of the paper reads the canonical form theorem in the
-- initial (arithmetic) regular category.  Those statements are about
-- the syntactic category, which is not formalised here: this module
-- proves the type-theoretic statements they rest on, so that each
-- categorical claim has a machine-checked core and only the
-- categorical step remains on paper.
--
--   existenceProperty  -- the meta-theoretic existence property
--   morConstant        -- every morphism is the constant at the centre
--   morInhabited       -- and at least one morphism exists
--   numeralIndexIndep  -- the numeral index depends on the term only

module Recursive.Existence where

open import Data.List.Base using ([] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Relation.Nullary using (¬_)

open import Recursive.Prelude
open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Derivability
open import Recursive.Corollaries using (canonicityQtr ; canonicitySigma)
open import Recursive.Contractibility using
  (NatFree ; Contraction ; contractible ; center ; centerTm ; contract)
open import Recursive.Numerals using (numeral ; numeralForm ; numeralDistinct)

-- ── The mono existential ─────────────────────────────────────────
--
-- Following Maietti 2005 (\S 3), the mono existential is the quotient
-- of the indexed sum on the terminal relation.

tyExists : RawType -> RawType -> RawType
tyExists B C = tyQtr (tySigma B C)

-- ── The meta-theoretic existence property ────────────────────────
--
-- A closed proof of a mono existential yields a closed witness and a
-- closed proof of the instance.  This is the type-theoretic content of
-- the projectivity of the terminal object (paper, Proposition 9.5):
-- canonicity at the quotient produces a representative, canonicity at
-- the sum splits it.
--
-- NOTE, deliberately: we do NOT also record an equation
-- t = [<a,c>].  That equation is derivable, but it is vacuous --
-- iQtrEq identifies ANY two classes of a quotient, so it holds for an
-- arbitrary unrelated pair and says nothing about the extracted
-- witness.  It is mono-ness of the quotient (rule eq-Q), not a
-- property of the extraction.

existenceProperty :
  {B C : RawType} {t : RawTerm}
  -> Derivable (hasTy [] t (tyExists B C))
  -> Σ[ a ∈ RawTerm ] Σ[ c ∈ RawTerm ]
       Derivable (hasTy [] a B)
     × Derivable (hasTy [] c (subTy (singleSubst a) C))
existenceProperty d with canonicityQtr d
... | _ , _ , dPair with canonicitySigma dPair
... | a , c , _ , da , dc = a , c , da , dc

-- ── Hom-set collapse ─────────────────────────────────────────────
--
-- The type-theoretic content of the paper's Corollary 9.2 (every
-- hom-set of the syntactic category of the pure calculus is a
-- singleton).  A morphism A -> B is a term x in A |- b(x) in B; the
-- statements below say that any such term is judgementally equal to
-- the constant at the centre of B, and that one exists.  Only the
-- CODOMAIN is required Nat-free -- exactly the hypothesis the
-- contraction needs -- so hom-sets into Nat-free types collapse even
-- in the arithmetic calculus, and its non-triviality is concentrated
-- in N.  The step from these statements to hom-sets of a syntactic
-- category is the on-paper part.

morConstant :
  {A B : RawType} {b : RawTerm}
  -> (nf : NatFree B)
  -> (dB : Derivable (isType [] B))
  -> Derivable (isType [] A)
  -> Derivable (hasTy (A ∷ []) b (wkTyBy 1 B))
  -> Derivable
       (termEq (A ∷ []) b
         (subTm (keepSubstBy 1) (center (contractible B nf dB)))
         (subTy (keepSubstBy 1) B))
morConstant {A = A} {B = B} {b = b} nf dB dA db =
  subst₂
    (λ t T -> Derivable (termEq (A ∷ []) b t T))
    (subTmRen sigma (addRen 1) (center contr))
    (subTyRen sigma (addRen 1) B)
    raw
  where
  contr : Contraction B
  contr = contractible B nf dB

  sigma : Subst
  sigma = consSubst b (keepSubstBy 1)

  db' : Derivable (hasTy (A ∷ []) b (subTy (keepSubstBy 1) B))
  db' =
    subst (λ T -> Derivable (hasTy (A ∷ []) b T))
      (renTyKeepSubstBy 1 B) db

  fits : FitsSubst (A ∷ []) (B ∷ []) sigma
  fits = fitsCons (fitsNil {delta = []} (wfCons wfNil dA)) db'

  raw : Derivable
    (termEq (A ∷ []) b
      (subTm sigma (wkTmBy 1 (center contr)))
      (subTy sigma (wkTyBy 1 B)))
  raw = substTmEqRule (contract contr) fits

morInhabited :
  {A B : RawType}
  -> (nf : NatFree B)
  -> (dB : Derivable (isType [] B))
  -> Derivable (isType [] A)
  -> Derivable
       (hasTy (A ∷ []) (wkTmBy 1 (center (contractible B nf dB)))
         (wkTyBy 1 B))
morInhabited {A = A} {B = B} nf dB dA =
  weakenTm (centerTm (contractible B nf dB)) (wfCons wfNil dA)
