{-# OPTIONS --safe #-}

-- Evaluation-core control for the paper's architecture comparison.
--
-- The four canonical readout functions mirror Inductive.MainTheorem.
-- On the common Treg fragment, canonicalFormTheorem is the recursive
-- counterpart of Inductive.CompTheorem.canonicalFormTheorem.
--
-- Recursive.FullCanonicalForm strictly strengthens this result with
-- canonical-shape witnesses and derivable equalities. This module is
-- retained to separate encoding architecture from statement strength.

module Recursive.CanonicalForm where

open import Recursive.Prelude
open import Data.List.Base using ([] ; _∷_)
open import Data.Product using (Σ-syntax ; _×_ ; _,_)
open import Data.Unit using (⊤ ; tt)

open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Evaluation
open import Recursive.Derivability
open import Recursive.Computable
open import Recursive.Fundamental

CanonicalForm : JForm -> Type
CanonicalForm (isType [] A) = ⊤
CanonicalForm (hasTy [] t A) =
  Σ[ g ∈ RawTerm ] t =>e g
CanonicalForm (typeEq [] A B) = ⊤
CanonicalForm (termEq [] t u A) =
  Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] (t =>e g) × (u =>e h)
CanonicalForm (isType (_ ∷ _) A) = ⊤
CanonicalForm (hasTy (_ ∷ _) t A) = ⊤
CanonicalForm (typeEq (_ ∷ _) A B) = ⊤
CanonicalForm (termEq (_ ∷ _) t u A) = ⊤


canonicalType : {A : RawType}
  -> Derivable (isType [] A)
  -> ⊤
canonicalType _ = tt

canonicalTypeEq : {A B : RawType}
  -> Derivable (typeEq [] A B)
  -> ⊤
canonicalTypeEq _ = tt

canonicalTerm : {t : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t A)
  -> Σ[ g ∈ RawTerm ] t =>e g
canonicalTerm d =
  let g , evt , cg = computableResult (fundTmClosed d) in
  g , evt

canonicalTermEq : {t u : RawTerm} {A : RawType}
  -> Derivable (termEq [] t u A)
  -> Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] (t =>e g) × (u =>e h)
canonicalTermEq {A = tyTop} d =
  let evt , evu = fundTmEqClosed d in
  tmStar , tmStar , evt , evu
canonicalTermEq {A = tySigma A B} d =
  let a , b , c , e , evt , evu , eqA , eqB , tyB =
        computableTmEqSigma-elim (fundTmEqClosed d)
  in
  tmPair a b , tmPair c e , evt , evu
canonicalTermEq {A = tyEq A a b} d =
  let evt , evu , eqab = computableTmEqEqForm-elim (fundTmEqClosed d) in
  tmRefl , tmRefl , evt , evu
canonicalTermEq {A = tyQtr A} d =
  let p , q , evt , evu , epp , eqq = computableTmEqQtr-elim (fundTmEqClosed d) in
  tmClass p , tmClass q , evt , evu
canonicalTermEq {A = tyNat} d with fundTmEqClosed d
... | cZeroVEq evt evu =
  tmZero , tmZero , evt , evu
... | cSucVEq {k = k} {k' = k'} evt evu _ =
  tmSuc k , tmSuc k' , evt , evu

canonicalFormTheorem : {J : JForm} -> Derivable J -> CanonicalForm J
canonicalFormTheorem {J = isType [] A} d = canonicalType d
canonicalFormTheorem {J = hasTy [] t A} d = canonicalTerm d
canonicalFormTheorem {J = typeEq [] A B} d = canonicalTypeEq d
canonicalFormTheorem {J = termEq [] t u A} d = canonicalTermEq d
canonicalFormTheorem {J = isType (_ ∷ _) A} d = tt
canonicalFormTheorem {J = hasTy (_ ∷ _) t A} d = tt
canonicalFormTheorem {J = typeEq (_ ∷ _) A B} d = tt
canonicalFormTheorem {J = termEq (_ ∷ _) t u A} d = tt
