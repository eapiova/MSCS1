{-# OPTIONS --safe #-}

module Tait.Corollaries where

open import Data.Empty using (⊥)
open import Data.List.Base using ([])
open import Data.Product using (Σ-syntax ; _×_ ; _,_)

open import Tait.Syntax
open import Tait.Context
open import Tait.Substitution
open import Tait.Evaluation
open import Tait.Derivability
open import Tait.Minimal using (derivableToMinimal)
open import Tait.Inversion using (minimalTyEqHead)
open import Tait.FullCanonicalForm

-- Valentini 3.10.8, restricted to the Treg fragment:
-- every closed derivable type/term has a canonical value.
evaluationType :
  {A : RawType}
  -> Derivable (isType [] A)
  -> Σ[ G ∈ RawType ] A =>t G
evaluationType d with fullCanonicalFormTheorem d
... | G , ev , _ =
  G , ev

evaluationTerm :
  {t : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t A)
  -> Σ[ g ∈ RawTerm ] t =>e g
evaluationTerm d with fullCanonicalFormTheorem d
... | g , _ , ev , _ =
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
... | tmPair a b , .(tySigma A B) , ev , evalSigma , canPairTm da db _ , ceq , _ =
  a , b , ev , da , db , ceq

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

-- A compact named consistency corollary: Top is not definitionally equal to
-- the inhabited Sigma(Top, Top) type.
tregConsistent :
  Derivable (typeEq [] tyTop (tySigma tyTop tyTop))
  -> ⊥
tregConsistent = topNotSigma
