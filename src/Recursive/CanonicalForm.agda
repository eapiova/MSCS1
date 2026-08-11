{-# OPTIONS --safe #-}

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
CanonicalForm (isType [] A) =
  Σ[ G ∈ RawType ] (A =>t G) × Derivable (typeEq [] A G)
CanonicalForm (hasTy [] t A) =
  Σ[ g ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (A =>t G)
CanonicalForm (typeEq [] A B) =
  Σ[ G ∈ RawType ] Σ[ H ∈ RawType ] (A =>t G) × (B =>t H)
CanonicalForm (termEq [] t u A) =
  Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] Σ[ G ∈ RawType ]
    (t =>e g) × (u =>e h) × (A =>t G)
CanonicalForm (isType (_ ∷ _) A) = ⊤
CanonicalForm (hasTy (_ ∷ _) t A) = ⊤
CanonicalForm (typeEq (_ ∷ _) A B) = ⊤
CanonicalForm (termEq (_ ∷ _) t u A) = ⊤

typeEval : (A : RawType) -> A =>t A
typeEval tyTop = evalTop
typeEval (tySigma A B) = evalSigma
typeEval (tyEq A a b) = evalEq
typeEval (tyQtr A) = evalQtr
typeEval tyNat = evalNat

canonicalType : {A : RawType}
  -> Derivable (isType [] A)
  -> Σ[ G ∈ RawType ] (A =>t G) × Derivable (typeEq [] A G)
canonicalType {A = A} d = A , typeEval A , reflTy d

canonicalTypeEq : {A B : RawType}
  -> Derivable (typeEq [] A B)
  -> Σ[ G ∈ RawType ] Σ[ H ∈ RawType ] (A =>t G) × (B =>t H)
canonicalTypeEq {A = A} {B = B} d = A , B , typeEval A , typeEval B

canonicalTerm : {t : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t A)
  -> Σ[ g ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (A =>t G)
canonicalTerm {A = A} d =
  let g , evt , cg = computableResult (fundTmClosed d) in
  g , A , evt , typeEval A

canonicalTermEq : {t u : RawTerm} {A : RawType}
  -> Derivable (termEq [] t u A)
  -> Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] Σ[ G ∈ RawType ]
       (t =>e g) × (u =>e h) × (A =>t G)
canonicalTermEq {A = tyTop} d =
  let evt , evu = fundTmEqClosed d in
  tmStar , tmStar , tyTop , evt , evu , evalTop
canonicalTermEq {A = tySigma A B} d =
  let a , b , c , e , evt , evu , eqA , eqB , tyB =
        computableTmEqSigma-elim (fundTmEqClosed d)
  in
  tmPair a b , tmPair c e , tySigma A B , evt , evu , evalSigma
canonicalTermEq {A = tyEq A a b} d =
  let evt , evu , eqab = computableTmEqEqForm-elim (fundTmEqClosed d) in
  tmRefl , tmRefl , tyEq A a b , evt , evu , evalEq
canonicalTermEq {A = tyQtr A} d =
  let p , q , evt , evu , epp , eqq = computableTmEqQtr-elim (fundTmEqClosed d) in
  tmClass p , tmClass q , tyQtr A , evt , evu , evalQtr
canonicalTermEq {A = tyNat} d with fundTmEqClosed d
... | cZeroVEq evt evu =
  tmZero , tmZero , tyNat , evt , evu , evalNat
... | cSucVEq {k = k} {k' = k'} evt evu _ =
  tmSuc k , tmSuc k' , tyNat , evt , evu , evalNat

canonicalFormTheorem : {J : JForm} -> Derivable J -> CanonicalForm J
canonicalFormTheorem {J = isType [] A} d = canonicalType d
canonicalFormTheorem {J = hasTy [] t A} d = canonicalTerm d
canonicalFormTheorem {J = typeEq [] A B} d = canonicalTypeEq d
canonicalFormTheorem {J = termEq [] t u A} d = canonicalTermEq d
canonicalFormTheorem {J = isType (_ ∷ _) A} d = tt
canonicalFormTheorem {J = hasTy (_ ∷ _) t A} d = tt
canonicalFormTheorem {J = typeEq (_ ∷ _) A B} d = tt
canonicalFormTheorem {J = termEq (_ ∷ _) t u A} d = tt
