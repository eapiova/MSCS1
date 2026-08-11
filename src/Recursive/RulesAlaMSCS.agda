{-# OPTIONS --safe #-}

module Recursive.RulesAlaMSCS where

open import Recursive.Prelude
open import Data.List.Base using ([] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc)

open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Evaluation using (qtrCompSub)
open import Recursive.Derivability
open import Recursive.Presupposition
open import Recursive.Inversion.Values

-- The wrappers below show the presupposition-enriched rules conservative
-- over the MSCS 2005 one-premise forms; used in the paper's
-- calculus-alignment remark.

qtrBranchSubCtx : Ctx -> Subst
qtrBranchSubCtx gamma =
  consSubst (tmClass (var zero)) (keepSubstCtx 1 gamma)

qtrBranchSubCtx-apply : (gamma : Ctx) (n : ℕ)
  -> applySubst (qtrBranchSubCtx gamma) n ≡ applySubst qtrBranchSub n
qtrBranchSubCtx-apply gamma zero = refl
qtrBranchSubCtx-apply gamma (suc n) = keepSubstCtx-apply 1 gamma n

qtrBranchSubCtx-subTy : (gamma : Ctx) (L : RawType)
  -> subTy (qtrBranchSubCtx gamma) L ≡ qtrBranchTy L
qtrBranchSubCtx-subTy gamma =
  subTyEq (qtrBranchSubCtx-apply gamma)

qtrBranchFits : {gamma : Ctx} {A : RawType}
  -> Derivable (isType gamma A)
  -> FitsSubst (A ∷ gamma) (tyQtr A ∷ gamma) (qtrBranchSubCtx gamma)
qtrBranchFits {gamma = gamma} {A = A} dA =
  fitsCons tail head
  where
  wfA : CtxWF (A ∷ gamma)
  wfA = wfCons (derivToCtxWF dA) dA

  tail : FitsSubst (A ∷ gamma) gamma (keepSubstCtx 1 gamma)
  tail = fitsKeep {delta = A ∷ []} {gamma = gamma} wfA

  varA : Derivable (hasTy (A ∷ gamma) (var zero) (wkTyBy 1 A))
  varA = varStar {delta = []} wfA dA

  head : Derivable
    (hasTy (A ∷ gamma) (tmClass (var zero))
      (subTy (keepSubstCtx 1 gamma) (tyQtr A)))
  head =
    subst
      (λ T -> Derivable (hasTy (A ∷ gamma) (tmClass (var zero)) T))
      (cong tyQtr
        (renTyKeepSubstBy 1 A ∙ sym (keepSubstCtx-subTy 1 gamma A)))
      (iQtr varA)

qtrBranchTyFromMotive : {gamma : Ctx} {A L : RawType}
  -> Derivable (isType (tyQtr A ∷ gamma) L)
  -> Derivable (isType (A ∷ gamma) (qtrBranchTy L))
qtrBranchTyFromMotive {gamma = gamma} {A = A} {L = L} dL =
  subst
    (λ T -> Derivable (isType (A ∷ gamma) T))
    (qtrBranchSubCtx-subTy gamma L)
    (substTyRule dL (qtrBranchFits dA))
  where
  dQtrA : Derivable (isType gamma (tyQtr A))
  dQtrA =
    ctxSuffixTy {delta = []} {gamma = gamma} {A = tyQtr A}
      (derivToCtxWF dL)

  dA : Derivable (isType gamma A)
  dA = innerTy (invQtrTy dQtrA)

eEqStar₁ : {gamma : Ctx} {A : RawType} {a b p : RawTerm}
  -> Derivable (hasTy gamma p (tyEq A a b))
  -> Derivable (termEq gamma a b A)
eEqStar₁ dp =
  eEqStar dp (typeTy prem) (leftTm prem) (rightTm prem)
  where
  prem = invEqTy (assocTmTy (reflTm dp))

cEq₁ : {gamma : Ctx} {A : RawType} {a b p : RawTerm}
  -> Derivable (hasTy gamma p (tyEq A a b))
  -> Derivable (termEq gamma p tmRefl (tyEq A a b))
cEq₁ dp =
  cEq dp (typeTy prem) (leftTm prem) (rightTm prem)
  where
  prem = invEqTy (assocTmTy (reflTm dp))

symTm₁ : {gamma : Ctx} {t u : RawTerm} {A : RawType}
  -> Derivable (termEq gamma t u A)
  -> Derivable (termEq gamma u t A)
symTm₁ dtu =
  symTm dtu (assocTmRight dtu) (assocTmTy dtu)

eQtr₁ : {gamma : Ctx} {A L : RawType} {l p : RawTerm}
  -> Derivable (isType (tyQtr A ∷ gamma) L)
  -> Derivable (hasTy gamma p (tyQtr A))
  -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
  -> Derivable
       (termEq (wkTyBy 1 A ∷ A ∷ gamma)
         (wkTmBy 1 l)
         (renTm qtrSecondBranchRen l)
         (qtrCohTy L))
  -> Derivable (hasTy gamma (tmElQtr l p) (subTy (singleSubst p) L))
eQtr₁ dL dp dl coh =
  eQtr dL dp (qtrBranchTyFromMotive dL) dl coh

eQtrEq₁ : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm}
  -> Derivable (isType (tyQtr A ∷ gamma) L)
  -> Derivable (termEq gamma p p' (tyQtr A))
  -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
  -> Derivable (hasTy (A ∷ gamma) l' (qtrBranchTy L))
  -> Derivable (termEq (A ∷ gamma) l l' (qtrBranchTy L))
  -> Derivable
       (termEq (wkTyBy 1 A ∷ A ∷ gamma)
         (wkTmBy 1 l)
         (renTm qtrSecondBranchRen l)
         (qtrCohTy L))
  -> Derivable
       (termEq (wkTyBy 1 A ∷ A ∷ gamma)
         (wkTmBy 1 l')
         (renTm qtrSecondBranchRen l')
         (qtrCohTy L))
  -> Derivable
       (termEq gamma
         (tmElQtr l p)
         (tmElQtr l' p')
         (subTy (singleSubst p) L))
eQtrEq₁ dL dp dl dl' dll' coh coh' =
  eQtrEq dL dp (qtrBranchTyFromMotive dL) dl dl' dll' coh coh'

cQtr₁ : {gamma : Ctx} {A L : RawType} {a l : RawTerm}
  -> Derivable (isType (tyQtr A ∷ gamma) L)
  -> Derivable (hasTy gamma a A)
  -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
  -> Derivable
       (termEq (wkTyBy 1 A ∷ A ∷ gamma)
         (wkTmBy 1 l)
         (renTm qtrSecondBranchRen l)
         (qtrCohTy L))
  -> Derivable
       (termEq gamma
         (tmElQtr l (tmClass a))
         (subTm (qtrCompSub a) l)
         (subTy (singleSubst (tmClass a)) L))
cQtr₁ dL da dl coh =
  cQtr dL da (qtrBranchTyFromMotive dL) dl coh

wfTop : CtxWF (tyTop ∷ [])
wfTop = wfCons wfNil (fTop wfNil)

wfTopTop : CtxWF (tyTop ∷ tyTop ∷ [])
wfTopTop = wfCons wfTop (fTop wfTop)

closedTop : Derivable (isType [] tyTop)
closedTop = fTop wfNil

closedStar : Derivable (hasTy [] tmStar tyTop)
closedStar = iTop wfNil

closedEqTop : Derivable (isType [] (tyEq tyTop tmStar tmStar))
closedEqTop = fEq closedTop closedStar closedStar

closedReflTop : Derivable (hasTy [] tmRefl (tyEq tyTop tmStar tmStar))
closedReflTop = iEq closedStar

closedQtrTop : Derivable (isType [] (tyQtr tyTop))
closedQtrTop = fQtr closedTop

closedClassStar : Derivable (hasTy [] (tmClass tmStar) (tyQtr tyTop))
closedClassStar = iQtr closedStar

closedQtrMotive : Derivable (isType (tyQtr tyTop ∷ []) tyTop)
closedQtrMotive = fTop (wfCons wfNil closedQtrTop)

closedQtrBranch : Derivable (hasTy (tyTop ∷ []) tmStar (qtrBranchTy tyTop))
closedQtrBranch = iTop wfTop

closedQtrCoh : Derivable
  (termEq (wkTyBy 1 tyTop ∷ tyTop ∷ [])
    (wkTmBy 1 tmStar)
    (renTm qtrSecondBranchRen tmStar)
    (qtrCohTy tyTop))
closedQtrCoh = cTop (iTop wfTopTop)

smoke-eEqStar₁ : Derivable (termEq [] tmStar tmStar tyTop)
smoke-eEqStar₁ = eEqStar₁ closedReflTop

smoke-cEq₁ : Derivable (termEq [] tmRefl tmRefl (tyEq tyTop tmStar tmStar))
smoke-cEq₁ = cEq₁ closedReflTop

smoke-symTm₁ : Derivable (termEq [] tmStar tmStar tyTop)
smoke-symTm₁ = symTm₁ (reflTm closedStar)

smoke-eQtr₁ : Derivable
  (hasTy [] (tmElQtr tmStar (tmClass tmStar))
    (subTy (singleSubst (tmClass tmStar)) tyTop))
smoke-eQtr₁ =
  eQtr₁ closedQtrMotive closedClassStar closedQtrBranch closedQtrCoh

smoke-eQtrEq₁ : Derivable
  (termEq []
    (tmElQtr tmStar (tmClass tmStar))
    (tmElQtr tmStar (tmClass tmStar))
    (subTy (singleSubst (tmClass tmStar)) tyTop))
smoke-eQtrEq₁ =
  eQtrEq₁
    closedQtrMotive
    (reflTm closedClassStar)
    closedQtrBranch
    closedQtrBranch
    (reflTm closedQtrBranch)
    closedQtrCoh
    closedQtrCoh

smoke-cQtr₁ : Derivable
  (termEq []
    (tmElQtr tmStar (tmClass tmStar))
    (subTm (qtrCompSub tmStar) tmStar)
    (subTy (singleSubst (tmClass tmStar)) tyTop))
smoke-cQtr₁ =
  cQtr₁ closedQtrMotive closedStar closedQtrBranch closedQtrCoh
