{-# OPTIONS --safe #-}

module Tait.Minimal.Base where

open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to length++)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.Properties using (+-suc) renaming (+-identityʳ to +-zero)

open import Tait.Prelude
open import Tait.Syntax
open import Tait.Context
open import Tait.Substitution
open import Tait.Evaluation
open import Tait.Derivability
open import Tait.Presupposition using
  ( keepSubstCtx ; keepSubstCtx-subTy ; singleSubstCtx ; singleSubstCtx-subTy
  ; singleSubstCtx-subTm ; singleSubstCtx-apply
  ; sigmaCompSubCtx ; sigmaCompSubCtx-subTy ; sigmaCompSubCtx-subTm
  ; headSubstCtx ; headSubstCtx-subTy )

lengthSnoc : (delta : Ctx) (A : RawType)
  -> length (delta ++ (A ∷ [])) ≡ suc (length delta)
lengthSnoc delta A =
  length++ delta {ys = A ∷ []} ∙ +-suc (length delta) zero ∙ cong suc (+-zero (length delta))

renJTo : Ctx -> Ren -> JForm -> JForm
renJTo gamma rho (isType _ A) =
  isType gamma (renTy rho A)
renJTo gamma rho (typeEq _ A B) =
  typeEq gamma (renTy rho A) (renTy rho B)
renJTo gamma rho (hasTy _ t A) =
  hasTy gamma (renTm rho t) (renTy rho A)
renJTo gamma rho (termEq _ t u A) =
  termEq gamma (renTm rho t) (renTm rho u) (renTy rho A)

subJTo : Ctx -> Subst -> JForm -> JForm
subJTo gamma sigma (isType _ A) =
  isType gamma (subTy sigma A)
subJTo gamma sigma (typeEq _ A B) =
  typeEq gamma (subTy sigma A) (subTy sigma B)
subJTo gamma sigma (hasTy _ t A) =
  hasTy gamma (subTm sigma t) (subTy sigma A)
subJTo gamma sigma (termEq _ t u A) =
  termEq gamma (subTm sigma t) (subTm sigma u) (subTy sigma A)

renTySkip : (rho : Ren) (A : RawType)
  -> renTy (compRen sucRen rho) A ≡ wkTyBy 1 (renTy rho A)
renTySkip rho A =
  sym (renTyComp sucRen rho A)

renTyKeepWk1 : (rho : Ren) (A : RawType)
  -> renTy (raiseRen rho) (wkTyBy 1 A) ≡ wkTyBy 1 (renTy rho A)
renTyKeepWk1 rho A =
  renTyComp (raiseRen rho) sucRen A
  ∙ cong (λ theta -> renTy theta A) (sym (shiftCompRen rho))
  ∙ sym (renTyComp sucRen rho A)

renTmKeepWk1 : (rho : Ren) (t : RawTerm)
  -> renTm (raiseRen rho) (wkTmBy 1 t) ≡ wkTmBy 1 (renTm rho t)
renTmKeepWk1 rho t =
  renTmComp (raiseRen rho) sucRen t
  ∙ cong (λ theta -> renTm theta t) (sym (shiftCompRen rho))
  ∙ sym (renTmComp sucRen rho t)

raiseRenIdBy : {rho : Ren}
  -> ((n : ℕ) -> applyRen rho n ≡ n)
  -> (n : ℕ) -> applyRen (raiseRen rho) n ≡ n
raiseRenIdBy h zero = refl
raiseRenIdBy {rho = rho} h (suc n) =
  applyRen-raise-suc rho n ∙ cong suc (h n)

mutual
  renTyIdBy : {rho : Ren}
    -> ((n : ℕ) -> applyRen rho n ≡ n)
    -> (A : RawType) -> renTy rho A ≡ A
  renTyIdBy h tyTop = refl
  renTyIdBy {rho = rho} h (tySigma A B) =
    cong₂ tySigma (renTyIdBy h A) (renTyIdBy (raiseRenIdBy {rho = rho} h) B)
  renTyIdBy h (tyEq A a b) =
    cong₃ tyEq (renTyIdBy h A) (renTmIdBy h a) (renTmIdBy h b)
  renTyIdBy h (tyQtr A) =
    cong tyQtr (renTyIdBy h A)

  renTmIdBy : {rho : Ren}
    -> ((n : ℕ) -> applyRen rho n ≡ n)
    -> (t : RawTerm) -> renTm rho t ≡ t
  renTmIdBy h (var n) = cong var (h n)
  renTmIdBy h tmStar = refl
  renTmIdBy h (tmPair a b) =
    cong₂ tmPair (renTmIdBy h a) (renTmIdBy h b)
  renTmIdBy {rho = rho} h (tmElSigma d m) =
    cong₂ tmElSigma
      (renTmIdBy h d)
      (renTmIdBy
        (raiseRenIdBy {rho = raiseRen rho} (raiseRenIdBy {rho = rho} h))
        m)
  renTmIdBy h tmRefl = refl
  renTmIdBy h (tmEq A a) =
    cong₂ tmEq (renTyIdBy h A) (renTmIdBy h a)
  renTmIdBy h (tmClass a) =
    cong tmClass (renTmIdBy h a)
  renTmIdBy {rho = rho} h (tmElQtr l p) =
    cong₂ tmElQtr (renTmIdBy (raiseRenIdBy {rho = rho} h) l) (renTmIdBy h p)

dropSucRen : (k : ℕ) -> dropRen k sucRen ≡ addRen (suc k)
dropSucRen zero = refl
dropSucRen (suc k) = refl

wkTyBy-suc : (k : ℕ) (A : RawType)
  -> wkTyBy 1 (wkTyBy k A) ≡ wkTyBy (suc k) A
wkTyBy-suc k A =
  renTyComp sucRen (addRen k) A
  ∙ cong (λ theta -> renTy theta A) (dropSucRen k)

subTyConsWk1 : (sigma : Subst) (t : RawTerm) (A : RawType)
  -> subTy (consSubst t sigma) (wkTyBy 1 A) ≡ subTy sigma A
subTyConsWk1 sigma t A =
  subTyRen (consSubst t sigma) sucRen A

subTyConsWkSuc : (sigma : Subst) (t : RawTerm) (k : ℕ) (A : RawType)
  -> subTy (consSubst t sigma) (wkTyBy (suc k) A)
       ≡ subTy sigma (wkTyBy k A)
subTyConsWkSuc sigma t k A =
  subTyRen (consSubst t sigma) (addRen (suc k)) A
  ∙ sym (subTyRen sigma (addRen k) A)

renSubSingle-apply : (rho : Ren) (t : RawTerm) (n : ℕ)
  -> applySubst (renSub rho (singleSubst t)) n
       ≡ applySubst (compSubRen (singleSubst (renTm rho t)) (raiseRen rho)) n
renSubSingle-apply rho t zero = refl
renSubSingle-apply rho t (suc n) =
  applySubst-renToSub rho n
  ∙ sym
      (applySubst-compSubRen (singleSubst (renTm rho t)) (compRen sucRen rho) n
       ∙ cong (applySubst (singleSubst (renTm rho t))) (applyRen-compRen sucRen rho n))

renSingleSubstTy : (rho : Ren) (t : RawTerm) (A : RawType)
  -> renTy rho (subTy (singleSubst t) A)
       ≡ subTy (singleSubst (renTm rho t)) (renTy (raiseRen rho) A)
renSingleSubstTy rho t A =
  renTySub rho (singleSubst t) A
  ∙ subTyEq (renSubSingle-apply rho t) A
  ∙ sym (subTyRen (singleSubst (renTm rho t)) (raiseRen rho) A)

renSingleSubstTm : (rho : Ren) (t u : RawTerm)
  -> renTm rho (subTm (singleSubst t) u)
       ≡ subTm (singleSubst (renTm rho t)) (renTm (raiseRen rho) u)
renSingleSubstTm rho t u =
  renTmSub rho (singleSubst t) u
  ∙ subTmEq (renSubSingle-apply rho t) u
  ∙ sym (subTmRen (singleSubst (renTm rho t)) (raiseRen rho) u)

subSubSingle-apply : (sigma : Subst) (t : RawTerm) (n : ℕ)
  -> applySubst (compSub sigma (singleSubst t)) n
       ≡ applySubst
           (compSub (singleSubst (subTm sigma t)) (liftSubst sigma))
           n
subSubSingle-apply sigma t zero = refl
subSubSingle-apply sigma t (suc n) =
  applySubst-compSub sigma idSubst n
  ∙ sym
      (subTmRen (singleSubst (subTm sigma t)) sucRen (applySubst sigma n)
       ∙ subTmId (applySubst sigma n))
  ∙ cong (subTm (singleSubst (subTm sigma t)))
      (sym (applySubst-renSub sucRen sigma n))
  ∙ sym
      (applySubst-compSub
        (singleSubst (subTm sigma t))
        (renSub sucRen sigma)
        n)

subSingleSubstTy : (sigma : Subst) (t : RawTerm) (A : RawType)
  -> subTy sigma (subTy (singleSubst t) A)
       ≡ subTy (singleSubst (subTm sigma t)) (subTy (liftSubst sigma) A)
subSingleSubstTy sigma t A =
  subTyComp sigma (singleSubst t) A
  ∙ subTyEq (subSubSingle-apply sigma t) A
  ∙ sym (subTyComp (singleSubst (subTm sigma t)) (liftSubst sigma) A)

subSingleSubstTm : (sigma : Subst) (t u : RawTerm)
  -> subTm sigma (subTm (singleSubst t) u)
       ≡ subTm (singleSubst (subTm sigma t)) (subTm (liftSubst sigma) u)
subSingleSubstTm sigma t u =
  subTmComp sigma (singleSubst t) u
  ∙ subTmEq (subSubSingle-apply sigma t) u
  ∙ sym (subTmComp (singleSubst (subTm sigma t)) (liftSubst sigma) u)

private
  subSubSigmaMot-apply : (sigma : Subst) (n : ℕ)
    -> applySubst (compSub (liftSubst (liftSubst sigma)) sigmaMotSub) n
         ≡ applySubst (compSub sigmaMotSub (liftSubst sigma)) n
  subSubSigmaMot-apply sigma zero = refl
  subSubSigmaMot-apply sigma (suc n) =
    applySubst-compSub (liftSubst (liftSubst sigma)) sigmaMotSub (suc n)
    ∙ liftSubst-apply-suc (liftSubst sigma) (suc n)
    ∙ cong (renTm sucRen) (liftSubst-apply-suc sigma n)
    ∙ renTmComp sucRen sucRen (applySubst sigma n)
    ∙ renTmKeepSubstBy 2 (applySubst sigma n)
    ∙ sym (subTmRen sigmaMotSub sucRen (applySubst sigma n))
    ∙ cong (subTm sigmaMotSub) (sym (liftSubst-apply-suc sigma n))
    ∙ sym (applySubst-compSub sigmaMotSub (liftSubst sigma) (suc n))

  subSubQtrBranch-apply : (sigma : Subst) (n : ℕ)
    -> applySubst (compSub (liftSubst sigma) qtrBranchSub) n
         ≡ applySubst (compSub qtrBranchSub (liftSubst sigma)) n
  subSubQtrBranch-apply sigma zero = refl
  subSubQtrBranch-apply sigma (suc n) =
    applySubst-compSub (liftSubst sigma) qtrBranchSub (suc n)
    ∙ liftSubst-apply-suc sigma n
    ∙ renTmKeepSubstBy 1 (applySubst sigma n)
    ∙ sym (subTmRen qtrBranchSub sucRen (applySubst sigma n))
    ∙ cong (subTm qtrBranchSub) (sym (liftSubst-apply-suc sigma n))
    ∙ sym (applySubst-compSub qtrBranchSub (liftSubst sigma) (suc n))

  subSubQtrCoh-apply : (sigma : Subst) (n : ℕ)
    -> applySubst (compSub (liftSubst (liftSubst sigma)) qtrCohSub) n
         ≡ applySubst (compSub qtrCohSub (liftSubst sigma)) n
  subSubQtrCoh-apply sigma zero = refl
  subSubQtrCoh-apply sigma (suc n) =
    applySubst-compSub (liftSubst (liftSubst sigma)) qtrCohSub (suc n)
    ∙ liftSubst-apply-suc (liftSubst sigma) (suc n)
    ∙ cong (renTm sucRen) (liftSubst-apply-suc sigma n)
    ∙ renTmComp sucRen sucRen (applySubst sigma n)
    ∙ renTmKeepSubstBy 2 (applySubst sigma n)
    ∙ sym (subTmRen qtrCohSub sucRen (applySubst sigma n))
    ∙ cong (subTm qtrCohSub) (sym (liftSubst-apply-suc sigma n))
    ∙ sym (applySubst-compSub qtrCohSub (liftSubst sigma) (suc n))

subSigmaBranchTy : (sigma : Subst) (M : RawType)
  -> subTy (liftSubst (liftSubst sigma)) (sigmaBranchTy M)
       ≡ sigmaBranchTy (subTy (liftSubst sigma) M)
subSigmaBranchTy sigma M =
  subTyComp (liftSubst (liftSubst sigma)) sigmaMotSub M
  ∙ subTyEq (subSubSigmaMot-apply sigma) M
  ∙ sym (subTyComp sigmaMotSub (liftSubst sigma) M)

subQtrBranchTy : (sigma : Subst) (L : RawType)
  -> subTy (liftSubst sigma) (qtrBranchTy L)
       ≡ qtrBranchTy (subTy (liftSubst sigma) L)
subQtrBranchTy sigma L =
  subTyComp (liftSubst sigma) qtrBranchSub L
  ∙ subTyEq (subSubQtrBranch-apply sigma) L
  ∙ sym (subTyComp qtrBranchSub (liftSubst sigma) L)

subQtrCohTy : (sigma : Subst) (L : RawType)
  -> subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)
       ≡ qtrCohTy (subTy (liftSubst sigma) L)
subQtrCohTy sigma L =
  subTyComp (liftSubst (liftSubst sigma)) qtrCohSub L
  ∙ subTyEq (subSubQtrCoh-apply sigma) L
  ∙ sym (subTyComp qtrCohSub (liftSubst sigma) L)

renSubSigmaComp-apply : (rho : Ren) (b c : RawTerm) (n : ℕ)
  -> applySubst (renSub rho (sigmaCompSub b c)) n
       ≡ applySubst
           (compSubRen
             (sigmaCompSub (renTm rho b) (renTm rho c))
             (raiseRen (raiseRen rho)))
           n
renSubSigmaComp-apply rho b c zero = refl
renSubSigmaComp-apply rho b c (suc zero) = refl
renSubSigmaComp-apply rho b c (suc (suc n)) =
  applySubst-renToSub rho n
  ∙ sym
      (applySubst-compSubRen
        (sigmaCompSub (renTm rho b) (renTm rho c))
        (compRen sucRen (compRen sucRen rho))
        n
       ∙ cong
           (applySubst (sigmaCompSub (renTm rho b) (renTm rho c)))
           (applyRen-compRen sucRen (compRen sucRen rho) n
            ∙ cong suc (applyRen-compRen sucRen rho n)))

renSigmaCompSubTm : (rho : Ren) (b c m : RawTerm)
  -> renTm rho (subTm (sigmaCompSub b c) m)
       ≡ subTm
           (sigmaCompSub (renTm rho b) (renTm rho c))
           (renTm (raiseRen (raiseRen rho)) m)
renSigmaCompSubTm rho b c m =
  renTmSub rho (sigmaCompSub b c) m
  ∙ subTmEq (renSubSigmaComp-apply rho b c) m
  ∙ sym
      (subTmRen
        (sigmaCompSub (renTm rho b) (renTm rho c))
        (raiseRen (raiseRen rho))
        m)

renSubQtrComp-apply : (rho : Ren) (a : RawTerm) (n : ℕ)
  -> applySubst (renSub rho (qtrCompSub a)) n
       ≡ applySubst
           (compSubRen (qtrCompSub (renTm rho a)) (raiseRen rho))
           n
renSubQtrComp-apply rho a zero = refl
renSubQtrComp-apply rho a (suc n) =
  applySubst-renToSub rho n
  ∙ sym
      (applySubst-compSubRen (qtrCompSub (renTm rho a)) (compRen sucRen rho) n
       ∙ cong (applySubst (qtrCompSub (renTm rho a))) (applyRen-compRen sucRen rho n))

renQtrCompSubTm : (rho : Ren) (a l : RawTerm)
  -> renTm rho (subTm (qtrCompSub a) l)
       ≡ subTm (qtrCompSub (renTm rho a)) (renTm (raiseRen rho) l)
renQtrCompSubTm rho a l =
  renTmSub rho (qtrCompSub a) l
  ∙ subTmEq (renSubQtrComp-apply rho a) l
  ∙ sym (subTmRen (qtrCompSub (renTm rho a)) (raiseRen rho) l)

renSubSigmaMot-apply : (rho : Ren) (n : ℕ)
  -> applySubst (renSub (raiseRen (raiseRen rho)) sigmaMotSub) n
       ≡ applySubst (compSubRen sigmaMotSub (raiseRen rho)) n
renSubSigmaMot-apply rho zero = refl
renSubSigmaMot-apply rho (suc n) =
  applySubst-renSub (raiseRen (raiseRen rho)) sigmaMotSub (suc n)
  ∙ cong var
      (applyRen-raise-suc (raiseRen rho) (suc n)
       ∙ cong suc (applyRen-raise-suc rho n))
  ∙ sym
      (applySubst-compSubRen sigmaMotSub (raiseRen rho) (suc n)
       ∙ cong (applySubst sigmaMotSub) (applyRen-raise-suc rho n))

renSigmaBranchTy : (rho : Ren) (M : RawType)
  -> renTy (raiseRen (raiseRen rho)) (sigmaBranchTy M)
       ≡ sigmaBranchTy (renTy (raiseRen rho) M)
renSigmaBranchTy rho M =
  renTySub (raiseRen (raiseRen rho)) sigmaMotSub M
  ∙ subTyEq (renSubSigmaMot-apply rho) M
  ∙ sym (subTyRen sigmaMotSub (raiseRen rho) M)

renSubQtrBranch-apply : (rho : Ren) (n : ℕ)
  -> applySubst (renSub (raiseRen rho) qtrBranchSub) n
       ≡ applySubst (compSubRen qtrBranchSub (raiseRen rho)) n
renSubQtrBranch-apply rho zero = refl
renSubQtrBranch-apply rho (suc n) =
  applySubst-renSub (raiseRen rho) qtrBranchSub (suc n)
  ∙ cong var (applyRen-raise-suc rho n)
  ∙ sym
      (applySubst-compSubRen qtrBranchSub (raiseRen rho) (suc n)
       ∙ cong (applySubst qtrBranchSub) (applyRen-raise-suc rho n))

renQtrBranchTy : (rho : Ren) (L : RawType)
  -> renTy (raiseRen rho) (qtrBranchTy L)
       ≡ qtrBranchTy (renTy (raiseRen rho) L)
renQtrBranchTy rho L =
  renTySub (raiseRen rho) qtrBranchSub L
  ∙ subTyEq (renSubQtrBranch-apply rho) L
  ∙ sym (subTyRen qtrBranchSub (raiseRen rho) L)

renSubQtrCoh-apply : (rho : Ren) (n : ℕ)
  -> applySubst (renSub (raiseRen (raiseRen rho)) qtrCohSub) n
       ≡ applySubst (compSubRen qtrCohSub (raiseRen rho)) n
renSubQtrCoh-apply rho zero = refl
renSubQtrCoh-apply rho (suc n) =
  applySubst-renSub (raiseRen (raiseRen rho)) qtrCohSub (suc n)
  ∙ cong var
      (applyRen-raise-suc (raiseRen rho) (suc n)
       ∙ cong suc (applyRen-raise-suc rho n))
  ∙ sym
      (applySubst-compSubRen qtrCohSub (raiseRen rho) (suc n)
       ∙ cong (applySubst qtrCohSub) (applyRen-raise-suc rho n))

renQtrCohTy : (rho : Ren) (L : RawType)
  -> renTy (raiseRen (raiseRen rho)) (qtrCohTy L)
       ≡ qtrCohTy (renTy (raiseRen rho) L)
renQtrCohTy rho L =
  renTySub (raiseRen (raiseRen rho)) qtrCohSub L
  ∙ subTyEq (renSubQtrCoh-apply rho) L
  ∙ sym (subTyRen qtrCohSub (raiseRen rho) L)

renQtrCohLeftTm : (rho : Ren) (l : RawTerm)
  -> renTm (raiseRen (raiseRen rho)) (wkTmBy 1 l)
       ≡ wkTmBy 1 (renTm (raiseRen rho) l)
renQtrCohLeftTm rho l =
  renTmKeepWk1 (raiseRen rho) l

qtrSecondBranchRenComm-apply : (rho : Ren) (n : ℕ)
  -> applyRen (compRen (raiseRen (raiseRen rho)) qtrSecondBranchRen) n
       ≡ applyRen (compRen qtrSecondBranchRen (raiseRen rho)) n
qtrSecondBranchRenComm-apply rho zero = refl
qtrSecondBranchRenComm-apply rho (suc n) =
  applyRen-compRen (raiseRen (raiseRen rho)) qtrSecondBranchRen (suc n)
  ∙ applyRen-raise-suc (raiseRen rho) (suc n)
  ∙ cong suc (applyRen-raise-suc rho n)
  ∙ sym (cong (applyRen qtrSecondBranchRen) (applyRen-raise-suc rho n))
  ∙ sym (applyRen-compRen qtrSecondBranchRen (raiseRen rho) (suc n))

renQtrCohRightTm : (rho : Ren) (l : RawTerm)
  -> renTm (raiseRen (raiseRen rho)) (renTm qtrSecondBranchRen l)
       ≡ renTm qtrSecondBranchRen (renTm (raiseRen rho) l)
renQtrCohRightTm rho l =
  renTmComp (raiseRen (raiseRen rho)) qtrSecondBranchRen l
  ∙ renTmEq (qtrSecondBranchRenComm-apply rho) l
  ∙ sym (renTmComp qtrSecondBranchRen (raiseRen rho) l)

mutual
  data Minimal : JForm -> Type where
    minVarStar : {gamma delta : Ctx} {A : RawType}
      -> MinCtxWF (delta ++ (A ∷ gamma))
      -> Minimal (isType gamma A)
      -> Minimal
           (hasTy (delta ++ (A ∷ gamma)) (var (length delta)) (wkTyBy (suc (length delta)) A))

    minReflTy : {gamma : Ctx} {A : RawType}
      -> Minimal (isType gamma A)
      -> Minimal (typeEq gamma A A)

    minReflTm : {gamma : Ctx} {t : RawTerm} {A : RawType}
      -> Minimal (hasTy gamma t A)
      -> Minimal (termEq gamma t t A)

    minSymTy : {gamma : Ctx} {A B : RawType}
      -> Minimal (typeEq gamma A B)
      -> Minimal (isType gamma B)
      -> Minimal (typeEq gamma B A)

    minSymTm : {gamma : Ctx} {t u : RawTerm} {A : RawType}
      -> Minimal (termEq gamma t u A)
      -> Minimal (hasTy gamma u A)
      -> Minimal (isType gamma A)
      -> Minimal (termEq gamma u t A)

    minTransTy : {gamma : Ctx} {A B C : RawType}
      -> Minimal (typeEq gamma A B)
      -> Minimal (typeEq gamma B C)
      -> Minimal (typeEq gamma A C)

    minTransTm : {gamma : Ctx} {t u v : RawTerm} {A : RawType}
      -> Minimal (termEq gamma t u A)
      -> Minimal (termEq gamma u v A)
      -> Minimal (termEq gamma t v A)

    minConv : {gamma : Ctx} {t : RawTerm} {A B : RawType}
      -> Minimal (hasTy gamma t A)
      -> Minimal (typeEq gamma A B)
      -> Minimal (hasTy gamma t B)

    minConvEq : {gamma : Ctx} {t u : RawTerm} {A B : RawType}
      -> Minimal (termEq gamma t u A)
      -> Minimal (typeEq gamma A B)
      -> Minimal (termEq gamma t u B)

    minFTop : {gamma : Ctx}
      -> MinCtxWF gamma
      -> Minimal (isType gamma tyTop)

    minITop : {gamma : Ctx}
      -> MinCtxWF gamma
      -> Minimal (hasTy gamma tmStar tyTop)

    minCTop : {gamma : Ctx} {t : RawTerm}
      -> Minimal (hasTy gamma t tyTop)
      -> Minimal (termEq gamma t tmStar tyTop)

    minFSigma : {gamma : Ctx} {A B : RawType}
      -> Minimal (isType gamma A)
      -> Minimal (isType (A ∷ gamma) B)
      -> Minimal (isType gamma (tySigma A B))

    minFSigmaEq : {gamma : Ctx} {A B C D : RawType}
      -> Minimal (typeEq gamma A C)
      -> Minimal (isType (A ∷ gamma) B)
      -> Minimal (typeEq (A ∷ gamma) B D)
      -> Minimal (isType gamma (tySigma C D))
      -> Minimal (typeEq gamma (tySigma A B) (tySigma C D))

    minISigma : {gamma : Ctx} {a b : RawTerm} {A B : RawType}
      -> Minimal (hasTy gamma a A)
      -> Minimal (hasTy gamma b (subTy (singleSubst a) B))
      -> Minimal (isType gamma (tySigma A B))
      -> Minimal (hasTy gamma (tmPair a b) (tySigma A B))

    minISigmaEq : {gamma : Ctx} {a b c d : RawTerm} {A B : RawType}
      -> Minimal (termEq gamma a c A)
      -> Minimal (termEq gamma b d (subTy (singleSubst a) B))
      -> Minimal (isType gamma A)
      -> Minimal (isType (A ∷ gamma) B)
      -> Minimal (termEq gamma (tmPair a b) (tmPair c d) (tySigma A B))

    minESigma : {gamma : Ctx} {A B M : RawType} {d m : RawTerm}
      -> Minimal (isType ((tySigma A B) ∷ gamma) M)
      -> Minimal (hasTy gamma d (tySigma A B))
      -> Minimal (isType gamma (tySigma A B))
      -> Minimal (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M))
      -> Minimal (isType gamma (subTy (singleSubst d) M))
      -> Minimal (hasTy gamma (tmElSigma d m) (subTy (singleSubst d) M))

    minESigmaEq : {gamma : Ctx} {A B M : RawType} {d d' m m' : RawTerm}
      -> Minimal (isType ((tySigma A B) ∷ gamma) M)
      -> Minimal (termEq gamma d d' (tySigma A B))
      -> Minimal (isType gamma (tySigma A B))
      -> Minimal (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M))
      -> Minimal (termEq (B ∷ A ∷ gamma) m m' (sigmaBranchTy M))
      -> Minimal (isType gamma (subTy (singleSubst d) M))
      -> Minimal
           (termEq gamma (tmElSigma d m) (tmElSigma d' m') (subTy (singleSubst d) M))

    minCSigma : {gamma : Ctx} {A B M : RawType} {b c m : RawTerm}
      -> Minimal (isType ((tySigma A B) ∷ gamma) M)
      -> Minimal (isType gamma (tySigma A B))
      -> Minimal (hasTy gamma b A)
      -> Minimal (hasTy gamma c (subTy (singleSubst b) B))
      -> Minimal (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M))
      -> Minimal (isType gamma (subTy (singleSubst (tmPair b c)) M))
      -> Minimal
           (termEq gamma (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
             (subTy (singleSubst (tmPair b c)) M))

    minFEq : {gamma : Ctx} {A : RawType} {a b : RawTerm}
      -> Minimal (isType gamma A)
      -> Minimal (hasTy gamma a A)
      -> Minimal (hasTy gamma b A)
      -> Minimal (isType gamma (tyEq A a b))

    minFEqEq : {gamma : Ctx} {A C : RawType} {a b c d : RawTerm}
      -> Minimal (typeEq gamma A C)
      -> Minimal (termEq gamma a c A)
      -> Minimal (termEq gamma b d A)
      -> Minimal (isType gamma (tyEq C c d))
      -> Minimal (typeEq gamma (tyEq A a b) (tyEq C c d))

    minIEq : {gamma : Ctx} {A : RawType} {a : RawTerm}
      -> Minimal (hasTy gamma a A)
      -> Minimal (hasTy gamma tmRefl (tyEq A a a))

    minIEqEq : {gamma : Ctx} {A : RawType} {a b : RawTerm}
      -> Minimal (termEq gamma a b A)
      -> Minimal (termEq gamma tmRefl tmRefl (tyEq A a a))

    minEEqStar : {gamma : Ctx} {A : RawType} {a b p : RawTerm}
      -> Minimal (hasTy gamma p (tyEq A a b))
      -> Minimal (isType gamma A)
      -> Minimal (hasTy gamma a A)
      -> Minimal (hasTy gamma b A)
      -> Minimal (termEq gamma a b A)

    minCEq : {gamma : Ctx} {A : RawType} {a b p : RawTerm}
      -> Minimal (hasTy gamma p (tyEq A a b))
      -> Minimal (isType gamma A)
      -> Minimal (hasTy gamma a A)
      -> Minimal (hasTy gamma b A)
      -> Minimal (termEq gamma p tmRefl (tyEq A a b))

    minFQtr : {gamma : Ctx} {A : RawType}
      -> Minimal (isType gamma A)
      -> Minimal (isType gamma (tyQtr A))

    minFQtrEq : {gamma : Ctx} {A B : RawType}
      -> Minimal (typeEq gamma A B)
      -> Minimal (typeEq gamma (tyQtr A) (tyQtr B))

    minIQtr : {gamma : Ctx} {A : RawType} {a : RawTerm}
      -> Minimal (hasTy gamma a A)
      -> Minimal (hasTy gamma (tmClass a) (tyQtr A))

    minIQtrEq : {gamma : Ctx} {A : RawType} {a b : RawTerm}
      -> Minimal (hasTy gamma a A)
      -> Minimal (hasTy gamma b A)
      -> Minimal (termEq gamma (tmClass a) (tmClass b) (tyQtr A))

    minEQtr : {gamma : Ctx} {A L : RawType} {l p : RawTerm}
      -> Minimal (isType ((tyQtr A) ∷ gamma) L)
      -> Minimal (hasTy gamma p (tyQtr A))
      -> Minimal (isType gamma A)
      -> Minimal (isType (A ∷ gamma) (qtrBranchTy L))
      -> Minimal (hasTy (A ∷ gamma) l (qtrBranchTy L))
      -> Minimal (isType (A ∷ gamma) (wkTyBy 1 A))
      -> Minimal
           (termEq (wkTyBy 1 A ∷ A ∷ gamma)
             (wkTmBy 1 l)
             (renTm qtrSecondBranchRen l)
             (qtrCohTy L))
      -> Minimal (isType gamma (subTy (singleSubst p) L))
      -> Minimal (hasTy gamma (tmElQtr l p) (subTy (singleSubst p) L))

    minEQtrEq : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm}
      -> Minimal (isType ((tyQtr A) ∷ gamma) L)
      -> Minimal (termEq gamma p p' (tyQtr A))
      -> Minimal (isType gamma A)
      -> Minimal (isType (A ∷ gamma) (qtrBranchTy L))
      -> Minimal (hasTy (A ∷ gamma) l (qtrBranchTy L))
      -> Minimal (hasTy (A ∷ gamma) l' (qtrBranchTy L))
      -> Minimal (termEq (A ∷ gamma) l l' (qtrBranchTy L))
      -> Minimal (isType (A ∷ gamma) (wkTyBy 1 A))
      -> Minimal
           (termEq (wkTyBy 1 A ∷ A ∷ gamma)
             (wkTmBy 1 l)
             (renTm qtrSecondBranchRen l)
             (qtrCohTy L))
      -> Minimal
           (termEq (wkTyBy 1 A ∷ A ∷ gamma)
             (wkTmBy 1 l')
             (renTm qtrSecondBranchRen l')
             (qtrCohTy L))
      -> Minimal (isType gamma (subTy (singleSubst p) L))
      -> Minimal (termEq gamma (tmElQtr l p) (tmElQtr l' p') (subTy (singleSubst p) L))

    minCQtr : {gamma : Ctx} {A L : RawType} {a l : RawTerm}
      -> Minimal (isType ((tyQtr A) ∷ gamma) L)
      -> Minimal (hasTy gamma a A)
      -> Minimal (isType gamma A)
      -> Minimal (isType (A ∷ gamma) (qtrBranchTy L))
      -> Minimal (hasTy (A ∷ gamma) l (qtrBranchTy L))
      -> Minimal (isType (A ∷ gamma) (wkTyBy 1 A))
      -> Minimal
           (termEq (wkTyBy 1 A ∷ A ∷ gamma)
             (wkTmBy 1 l)
             (renTm qtrSecondBranchRen l)
             (qtrCohTy L))
      -> Minimal (isType gamma (subTy (singleSubst (tmClass a)) L))
      -> Minimal
           (termEq gamma (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
             (subTy (singleSubst (tmClass a)) L))

  data MinCtxWF : Ctx -> Type where
    minWfNil : MinCtxWF []
    minWfCons : {gamma : Ctx} {A : RawType}
      -> MinCtxWF gamma
      -> Minimal (isType gamma A)
      -> MinCtxWF (A ∷ gamma)

  data MinFitsSubst : Ctx -> Ctx -> Subst -> Type where
    minFitsNil : {gamma : Ctx} {sigma : Subst}
      -> MinCtxWF gamma
      -> MinFitsSubst gamma [] sigma
    minFitsCons : {gamma delta : Ctx} {sigma : Subst} {A : RawType} {t : RawTerm}
      -> MinFitsSubst gamma delta sigma
      -> Minimal (hasTy gamma t (subTy sigma A))
      -> MinFitsSubst gamma (A ∷ delta) (consSubst t sigma)

  data MinFitsEqSubst : Ctx -> Ctx -> Subst -> Subst -> Type where
    minFitsEqNil : {gamma : Ctx} {sigma tau : Subst}
      -> MinCtxWF gamma
      -> MinFitsEqSubst gamma [] sigma tau
    minFitsEqCons : {gamma delta : Ctx} {sigma tau : Subst} {A : RawType} {t u : RawTerm}
      -> MinFitsEqSubst gamma delta sigma tau
      -> Minimal (termEq gamma t u (subTy sigma A))
      -> Minimal (hasTy gamma u (subTy tau A))
      -> Minimal (hasTy gamma u (subTy sigma A))
      -> MinFitsEqSubst gamma (A ∷ delta) (consSubst t sigma) (consSubst u tau)

  data RenFits : Ctx -> Ctx -> Ren -> Type where
    renFitsNil : {gamma : Ctx} {rho : Ren}
      -> MinCtxWF gamma
      -> RenFits gamma [] rho
    renFitsKeep : {gamma delta : Ctx} {rho : Ren} {A : RawType}
      -> RenFits gamma delta rho
      -> Minimal (isType gamma (renTy rho A))
      -> RenFits (renTy rho A ∷ gamma) (A ∷ delta) (raiseRen rho)
    renFitsSkip : {gamma delta : Ctx} {rho : Ren} {B : RawType}
      -> RenFits gamma delta rho
      -> Minimal (isType gamma B)
      -> RenFits (B ∷ gamma) delta (compRen sucRen rho)

renFitsCastTarget : {gamma gamma' delta : Ctx} {rho : Ren}
  -> gamma ≡ gamma'
  -> RenFits gamma delta rho
  -> RenFits gamma' delta rho
renFitsCastTarget refl fits = fits

record RenFitsTo (target source : Ctx) (rho : Ren) : Type where
  constructor renFitsTo
  field
    actualRen : Ren
    actualFits : RenFits target source actualRen
    actualEq : (n : ℕ) -> applyRen actualRen n ≡ applyRen rho n

renFitsIdTo : {gamma : Ctx}
  -> MinCtxWF gamma
  -> RenFitsTo gamma gamma idRen
renFitsIdTo minWfNil =
  renFitsTo idRen (renFitsNil minWfNil) (λ n -> refl)
renFitsIdTo {gamma = A ∷ gamma} (minWfCons wf dA) with renFitsIdTo wf
... | renFitsTo rho fits rhoId =
  renFitsTo
    (raiseRen rho)
    (renFitsCastTarget
      (cong (λ T -> T ∷ gamma) rhoAId)
      (renFitsKeep fits dARen))
    (raiseRenIdBy {rho = rho} rhoId)
  where
  rhoAId : renTy rho A ≡ A
  rhoAId = renTyIdBy rhoId A

  dARen : Minimal (isType gamma (renTy rho A))
  dARen =
    subst
      (λ T -> Minimal (isType gamma T))
      (sym rhoAId)
      dA

renFitsWeakenTo : (delta : Ctx) {gamma : Ctx}
  -> MinCtxWF (delta ++ gamma)
  -> RenFitsTo (delta ++ gamma) gamma (addRen (length delta))
renFitsWeakenTo [] wf =
  renFitsIdTo wf
renFitsWeakenTo (B ∷ delta) (minWfCons wf dB) with renFitsWeakenTo delta wf
... | renFitsTo rho fits rhoShift =
  renFitsTo
    (compRen sucRen rho)
    (renFitsSkip fits dB)
    (λ n -> applyRen-compRen sucRen rho n ∙ cong suc (rhoShift n))

minFitsSubstCtxWF : {gamma delta : Ctx} {sigma : Subst}
  -> MinFitsSubst gamma delta sigma
  -> MinCtxWF gamma
minFitsSubstCtxWF (minFitsNil wf) = wf
minFitsSubstCtxWF (minFitsCons fits _) = minFitsSubstCtxWF fits

minFitsEqSubstCtxWF : {gamma delta : Ctx} {sigma tau : Subst}
  -> MinFitsEqSubst gamma delta sigma tau
  -> MinCtxWF gamma
minFitsEqSubstCtxWF (minFitsEqNil wf) = wf
minFitsEqSubstCtxWF (minFitsEqCons fits _ _ _) = minFitsEqSubstCtxWF fits

minFitsLookup : (delta : Ctx)
  -> {target gamma : Ctx} {sigma : Subst} {A : RawType}
  -> MinFitsSubst target (delta ++ (A ∷ gamma)) sigma
  -> Minimal
       (hasTy target
         (applySubst sigma (length delta))
         (subTy sigma (wkTyBy (suc (length delta)) A)))
minFitsLookup [] (minFitsCons {sigma = sigma} {t = t} _ dt) =
  subst
    (λ T -> Minimal (hasTy _ _ T))
    (sym (subTyConsWk1 sigma t _))
    dt
minFitsLookup (B ∷ delta) (minFitsCons {sigma = sigma} {t = t} fits _) =
  subst
    (λ T -> Minimal (hasTy _ _ T))
    (sym (subTyConsWkSuc sigma t (suc (length delta)) _))
    (minFitsLookup delta fits)

minCtxSuffixWF : {delta gamma : Ctx}
  -> MinCtxWF (delta ++ gamma)
  -> MinCtxWF gamma
minCtxSuffixWF {delta = []} wf = wf
minCtxSuffixWF {delta = _ ∷ delta} (minWfCons wf _) =
  minCtxSuffixWF {delta = delta} wf

minCtxSuffixTy : {delta gamma : Ctx} {A : RawType}
  -> MinCtxWF (delta ++ (A ∷ gamma))
  -> Minimal (isType gamma A)
minCtxSuffixTy {delta = []} (minWfCons _ dA) = dA
minCtxSuffixTy {delta = _ ∷ delta} (minWfCons wf _) =
  minCtxSuffixTy {delta = delta} wf

minDerivToCtxWF : {J : JForm}
  -> Minimal J
  -> MinCtxWF (ctxOf J)
minDerivToCtxWF (minVarStar wf _) = wf
minDerivToCtxWF (minReflTy d) = minDerivToCtxWF d
minDerivToCtxWF (minReflTm d) = minDerivToCtxWF d
minDerivToCtxWF (minSymTy d _) = minDerivToCtxWF d
minDerivToCtxWF (minSymTm d _ _) = minDerivToCtxWF d
minDerivToCtxWF (minTransTy d _) = minDerivToCtxWF d
minDerivToCtxWF (minTransTm d _) = minDerivToCtxWF d
minDerivToCtxWF (minConv d _) = minDerivToCtxWF d
minDerivToCtxWF (minConvEq d _) = minDerivToCtxWF d
minDerivToCtxWF (minFTop wf) = wf
minDerivToCtxWF (minITop wf) = wf
minDerivToCtxWF (minCTop d) = minDerivToCtxWF d
minDerivToCtxWF (minFSigma d _) = minDerivToCtxWF d
minDerivToCtxWF (minFSigmaEq d _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minISigma d _ _) = minDerivToCtxWF d
minDerivToCtxWF (minISigmaEq d _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minESigma _ d _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minESigmaEq _ d _ _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minCSigma _ _ d _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minFEq d _ _) = minDerivToCtxWF d
minDerivToCtxWF (minFEqEq d _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minIEq d) = minDerivToCtxWF d
minDerivToCtxWF (minIEqEq d) = minDerivToCtxWF d
minDerivToCtxWF (minEEqStar d _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minCEq d _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minFQtr d) = minDerivToCtxWF d
minDerivToCtxWF (minFQtrEq d) = minDerivToCtxWF d
minDerivToCtxWF (minIQtr d) = minDerivToCtxWF d
minDerivToCtxWF (minIQtrEq d _) = minDerivToCtxWF d
minDerivToCtxWF (minEQtr _ d _ _ _ _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minEQtrEq _ d _ _ _ _ _ _ _ _ _) = minDerivToCtxWF d
minDerivToCtxWF (minCQtr _ d _ _ _ _ _ _) = minDerivToCtxWF d

mutual
  minAssocTyLeft : {gamma : Ctx} {A B : RawType}
    -> Minimal (typeEq gamma A B)
    -> Minimal (isType gamma A)
  minAssocTyLeft (minReflTy d) = d
  minAssocTyLeft (minSymTy _ dB) = dB
  minAssocTyLeft (minTransTy d _) = minAssocTyLeft d
  minAssocTyLeft (minFSigmaEq dAC dB _ _) =
    minFSigma (minAssocTyLeft dAC) dB
  minAssocTyLeft (minFEqEq dAC dac dbd _) =
    minFEq (minAssocTyLeft dAC) (minAssocTmLeft dac) (minAssocTmLeft dbd)
  minAssocTyLeft (minFQtrEq d) =
    minFQtr (minAssocTyLeft d)

  minAssocTyRight : {gamma : Ctx} {A B : RawType}
    -> Minimal (typeEq gamma A B)
    -> Minimal (isType gamma B)
  minAssocTyRight (minReflTy d) = d
  minAssocTyRight (minSymTy d _) = minAssocTyLeft d
  minAssocTyRight (minTransTy _ d) = minAssocTyRight d
  minAssocTyRight (minFSigmaEq _ _ _ dRight) = dRight
  minAssocTyRight (minFEqEq _ _ _ dRight) = dRight
  minAssocTyRight (minFQtrEq d) =
    minFQtr (minAssocTyRight d)

  minAssocTmLeft : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Minimal (termEq gamma t u A)
    -> Minimal (hasTy gamma t A)
  minAssocTmLeft (minReflTm d) = d
  minAssocTmLeft (minSymTm _ du _) = du
  minAssocTmLeft (minTransTm d _) = minAssocTmLeft d
  minAssocTmLeft (minConvEq d dAB) =
    minConv (minAssocTmLeft d) dAB
  minAssocTmLeft (minCTop d) = d
  minAssocTmLeft (minISigmaEq dac dbd dA dB) =
    minISigma (minAssocTmLeft dac) (minAssocTmLeft dbd) (minFSigma dA dB)
  minAssocTmLeft (minESigmaEq dM dd dSigma dm _ dTy) =
    minESigma dM (minAssocTmLeft dd) dSigma dm dTy
  minAssocTmLeft (minCSigma dM dSigma db dc dm dTy) =
    minESigma dM (minISigma db dc dSigma) dSigma dm dTy
  minAssocTmLeft (minIEqEq d) =
    minIEq (minAssocTmLeft d)
  minAssocTmLeft (minEEqStar _ _ da _) = da
  minAssocTmLeft (minCEq p _ _ _) = p
  minAssocTmLeft (minIQtrEq da _) =
    minIQtr da
  minAssocTmLeft (minEQtrEq dL dp dA dBranch dl _ _ dWkA coh _ dTy) =
    minEQtr dL (minAssocTmLeft dp) dA dBranch dl dWkA coh dTy
  minAssocTmLeft (minCQtr dL da dA dBranch dl dWkA coh dTy) =
    minEQtr dL (minIQtr da) dA dBranch dl dWkA coh dTy

minSigmaLeft : {gamma : Ctx} {A B : RawType}
  -> Minimal (isType gamma (tySigma A B))
  -> Minimal (isType gamma A)
minSigmaLeft (minFSigma dA _) = dA

minSigmaRight : {gamma : Ctx} {A B : RawType}
  -> Minimal (isType gamma (tySigma A B))
  -> Minimal (isType (A ∷ gamma) B)
minSigmaRight (minFSigma _ dB) = dB

minQtrInner : {gamma : Ctx} {A : RawType}
  -> Minimal (isType gamma (tyQtr A))
  -> Minimal (isType gamma A)
minQtrInner (minFQtr dA) = dA
