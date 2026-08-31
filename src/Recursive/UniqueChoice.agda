{-# OPTIONS --safe #-}

-- The mechanisation of Proposition 9.6 of the paper: the rule of unique
-- choice, requested by Maietti.  The construction keeps visible that ucFun
-- needs existence and uniqueness but not propositionality of R, while
-- ucProof is the sole consumer of the propositionality premise.

module Recursive.UniqueChoice where

open import Recursive.Prelude
open import Data.List.Base using ([] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc)

open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Derivability
open import Recursive.Presupposition
open import Recursive.RulesAlaMSCS
open import Recursive.Contractibility using
  ( singleSubst-wkTy ; singleSubst-wkTm
  ; qtrBranch-wkTy ; qtrBranch-wkTm
  ; qtrCoh-wkTy ; qtrCoh-wkTm
  ; sigmaBranch-wkTy ; sigmaBranch-wkTm
  ; sigmaSecondSubst ; sigmaSecondSubst-wkTy
  )
open import Recursive.Inversion.Values using
  ( invSigmaTy ; leftTy ; familyTy )

ucCarrier : RawType -> RawType -> RawType
ucCarrier B R = tySigma B R

ucExists : RawType -> RawType -> RawType
ucExists B R = tyQtr (ucCarrier B R)

ucFstBranch : RawTerm
ucFstBranch = tmElSigma (var zero) (var (suc zero))

ucSndBranch : RawTerm
ucSndBranch = tmElSigma (var zero) (var zero)

ucFunction : RawTerm -> RawTerm
ucFunction t = tmElQtr ucFstBranch t

ucWitness : RawTerm -> RawTerm
ucWitness t = tmElQtr ucSndBranch t

ucFibre : RawType -> RawTerm -> RawType
ucFibre R a = subTy (singleSubst a) R

ucRzRen : Ren
ucRzRen = consRen zero (consRen 3 (shiftRen 4))

ucRz : RawType -> RawType
ucRz R = renTy ucRzRen R

sigmaFst : {gamma : Ctx} {A B : RawType} {d : RawTerm}
  -> Derivable (isType gamma (tySigma A B))
  -> Derivable (hasTy gamma d (tySigma A B))
  -> Derivable (hasTy gamma (tmElSigma d (var (suc zero))) A)
sigmaFst {gamma = gamma} {A = A} {B = B} {d = d} dSigma dd =
  subst
    (λ T -> Derivable (hasTy gamma (tmElSigma d (var (suc zero))) T))
    (singleSubst-wkTy d A)
    (eSigma dM dd dBranch)
  where
  prem = invSigmaTy dSigma

  dA : Derivable (isType gamma A)
  dA = leftTy prem

  dB : Derivable (isType (A ∷ gamma) B)
  dB = familyTy prem

  wfSigma : CtxWF ((tySigma A B) ∷ gamma)
  wfSigma = wfCons (derivToCtxWF dSigma) dSigma

  dM : Derivable (isType ((tySigma A B) ∷ gamma) (wkTyBy 1 A))
  dM = weakenTy dA wfSigma

  wfA : CtxWF (A ∷ gamma)
  wfA = wfCons (derivToCtxWF dSigma) dA

  wfBranch : CtxWF (B ∷ A ∷ gamma)
  wfBranch = wfCons wfA dB

  dVar : Derivable
    (hasTy (B ∷ A ∷ gamma) (var (suc zero)) (wkTyBy 2 A))
  dVar = varStar {delta = B ∷ []} wfBranch dA

  dBranch : Derivable
    (hasTy (B ∷ A ∷ gamma) (var (suc zero))
      (sigmaBranchTy (wkTyBy 1 A)))
  dBranch =
    subst
      (λ T -> Derivable (hasTy (B ∷ A ∷ gamma) (var (suc zero)) T))
      (sym (sigmaBranch-wkTy A))
      dVar

sigmaFstPair : {gamma : Ctx} {A B : RawType} {b c : RawTerm}
  -> Derivable (isType gamma (tySigma A B))
  -> Derivable (hasTy gamma b A)
  -> Derivable (hasTy gamma c (subTy (singleSubst b) B))
  -> Derivable
       (termEq gamma
         (tmElSigma (tmPair b c) (var (suc zero))) b A)
sigmaFstPair {gamma = gamma} {A = A} {B = B} {b = b} {c = c}
  dSigma db dc =
  subst
    (λ T -> Derivable
      (termEq gamma (tmElSigma (tmPair b c) (var (suc zero))) b T))
    (singleSubst-wkTy (tmPair b c) A)
    (cSigma dM dSigma db dc dBranch)
  where
  prem = invSigmaTy dSigma

  dA : Derivable (isType gamma A)
  dA = leftTy prem

  dB : Derivable (isType (A ∷ gamma) B)
  dB = familyTy prem

  wfSigma : CtxWF ((tySigma A B) ∷ gamma)
  wfSigma = wfCons (derivToCtxWF dSigma) dSigma

  dM : Derivable (isType ((tySigma A B) ∷ gamma) (wkTyBy 1 A))
  dM = weakenTy dA wfSigma

  wfA : CtxWF (A ∷ gamma)
  wfA = wfCons (derivToCtxWF dSigma) dA

  wfBranch : CtxWF (B ∷ A ∷ gamma)
  wfBranch = wfCons wfA dB

  dVar : Derivable
    (hasTy (B ∷ A ∷ gamma) (var (suc zero)) (wkTyBy 2 A))
  dVar = varStar {delta = B ∷ []} wfBranch dA

  dBranch : Derivable
    (hasTy (B ∷ A ∷ gamma) (var (suc zero))
      (sigmaBranchTy (wkTyBy 1 A)))
  dBranch =
    subst
      (λ T -> Derivable (hasTy (B ∷ A ∷ gamma) (var (suc zero)) T))
      (sym (sigmaBranch-wkTy A))
      dVar

sigmaBranchFstEq : {gamma : Ctx} {A B : RawType}
  -> Derivable (isType gamma (tySigma A B))
  -> Derivable
       (termEq (B ∷ A ∷ gamma)
         (tmElSigma
           (tmPair (var (suc zero)) (var zero))
           (var (suc zero)))
         (var (suc zero))
         (wkTyBy 2 A))
sigmaBranchFstEq {gamma = gamma} {A = A} {B = B} dSigma =
  sigmaFstPair dNiceSigma varA varB
  where
  prem = invSigmaTy dSigma

  dA : Derivable (isType gamma A)
  dA = leftTy prem

  dB : Derivable (isType (A ∷ gamma) B)
  dB = familyTy prem

  wfA : CtxWF (A ∷ gamma)
  wfA = wfCons (derivToCtxWF dSigma) dA

  wfBranch : CtxWF (B ∷ A ∷ gamma)
  wfBranch = wfCons wfA dB

  dNiceSigma : Derivable
    (isType (B ∷ A ∷ gamma) (wkTyBy 2 (tySigma A B)))
  dNiceSigma = weakenTy {delta = B ∷ A ∷ []} dSigma wfBranch

  dNiceB : Derivable
    (isType (wkTyBy 2 A ∷ B ∷ A ∷ gamma)
      (renTy (raiseRen (addRen 2)) B))
  dNiceB = familyTy (invSigmaTy dNiceSigma)

  varA : Derivable
    (hasTy (B ∷ A ∷ gamma) (var (suc zero)) (wkTyBy 2 A))
  varA = varStar {delta = B ∷ []} wfBranch dA

  varB0 : Derivable
    (hasTy (B ∷ A ∷ gamma) (var zero) (wkTyBy 1 B))
  varB0 = varStar {delta = []} wfBranch dB

  varB : Derivable
    (hasTy (B ∷ A ∷ gamma) (var zero)
      (subTy (singleSubst (var (suc zero)))
        (renTy (raiseRen (addRen 2)) B)))
  varB =
    subst
      (λ T -> Derivable (hasTy (B ∷ A ∷ gamma) (var zero) T))
      (sym
        (subTyRen (singleSubst (var (suc zero)))
          (raiseRen (addRen 2)) B
        ∙ sigmaSecondSubst-wkTy B))
      varB0

sigmaSndMotiveSub : Ctx -> Subst
sigmaSndMotiveSub gamma =
  consSubst ucFstBranch (keepSubstCtx 1 gamma)

sigmaSndMotive : Ctx -> RawType -> RawType
sigmaSndMotive gamma B = subTy (sigmaSndMotiveSub gamma) B

sigmaSndBranchSub : Ctx -> Subst
sigmaSndBranchSub gamma =
  consSubst
    (tmElSigma
      (tmPair (var (suc zero)) (var zero))
      (var (suc zero)))
    (keepSubstCtx 2 gamma)

sigmaSndVarSub : Ctx -> Subst
sigmaSndVarSub gamma =
  consSubst (var (suc zero)) (keepSubstCtx 2 gamma)

sigmaSndMotiveBranchApply : (gamma : Ctx) (n : ℕ)
  -> applySubst (compSub sigmaMotSub (sigmaSndMotiveSub gamma)) n
       ≡ applySubst (sigmaSndBranchSub gamma) n
sigmaSndMotiveBranchApply gamma zero = refl
sigmaSndMotiveBranchApply gamma (suc n) =
  applySubst-compSub sigmaMotSub (keepSubstCtx 1 gamma) n
  ∙ cong (subTm sigmaMotSub) (keepSubstCtx-apply 1 gamma n)
  ∙ sym (keepSubstCtx-apply 2 gamma n)

sigmaSndMotiveBranch : (gamma : Ctx) (B : RawType)
  -> sigmaBranchTy (sigmaSndMotive gamma B)
       ≡ subTy (sigmaSndBranchSub gamma) B
sigmaSndMotiveBranch gamma B =
  subTyComp sigmaMotSub (sigmaSndMotiveSub gamma) B
  ∙ subTyEq (sigmaSndMotiveBranchApply gamma) B

sigmaSndVarApply : (gamma : Ctx) (n : ℕ)
  -> applySubst (sigmaSndVarSub gamma) n
       ≡ applySubst sigmaSecondSubst n
sigmaSndVarApply gamma zero = refl
sigmaSndVarApply gamma (suc n) = keepSubstCtx-apply 2 gamma n

sigmaSndVarTy : (gamma : Ctx) (B : RawType)
  -> subTy (sigmaSndVarSub gamma) B ≡ wkTyBy 1 B
sigmaSndVarTy gamma B =
  subTyEq (sigmaSndVarApply gamma) B
  ∙ sigmaSecondSubst-wkTy B

sigmaSndConclusionApply : (gamma : Ctx) (d : RawTerm) (n : ℕ)
  -> applySubst
       (compSub (singleSubst d) (sigmaSndMotiveSub gamma)) n
       ≡ applySubst
           (singleSubstCtx (tmElSigma d (var (suc zero))) gamma) n
sigmaSndConclusionApply gamma d zero = refl
sigmaSndConclusionApply gamma d (suc n) =
  applySubst-compSub (singleSubst d) (keepSubstCtx 1 gamma) n
  ∙ cong (subTm (singleSubst d)) (keepSubstCtx-apply 1 gamma n)
  ∙ sym (keepSubstCtx-apply 0 gamma n)

sigmaSndConclusion : (gamma : Ctx) (B : RawType) (d : RawTerm)
  -> subTy (singleSubst d) (sigmaSndMotive gamma B)
       ≡ subTy (singleSubst (tmElSigma d (var (suc zero)))) B
sigmaSndConclusion gamma B d =
  subTyComp (singleSubst d) (sigmaSndMotiveSub gamma) B
  ∙ subTyEq (sigmaSndConclusionApply gamma d) B
  ∙ singleSubstCtx-subTy (tmElSigma d (var (suc zero))) gamma B

sigmaSnd : {gamma : Ctx} {A B : RawType} {d : RawTerm}
  -> Derivable (isType gamma (tySigma A B))
  -> Derivable (hasTy gamma d (tySigma A B))
  -> Derivable
       (hasTy gamma (tmElSigma d (var zero))
         (subTy (singleSubst (tmElSigma d (var (suc zero)))) B))
sigmaSnd {gamma = gamma} {A = A} {B = B} {d = d} dSigma dd =
  subst
    (λ T -> Derivable (hasTy gamma (tmElSigma d (var zero)) T))
    (sigmaSndConclusion gamma B d)
    (eSigma dM dd dBranch)
  where
  prem = invSigmaTy dSigma

  dA : Derivable (isType gamma A)
  dA = leftTy prem

  dB : Derivable (isType (A ∷ gamma) B)
  dB = familyTy prem

  wfGamma : CtxWF gamma
  wfGamma = derivToCtxWF dSigma

  wfSigma : CtxWF ((tySigma A B) ∷ gamma)
  wfSigma = wfCons wfGamma dSigma

  dWkSigma : Derivable
    (isType ((tySigma A B) ∷ gamma) (wkTyBy 1 (tySigma A B)))
  dWkSigma = weakenTy dSigma wfSigma

  varSigma : Derivable
    (hasTy ((tySigma A B) ∷ gamma) (var zero)
      (wkTyBy 1 (tySigma A B)))
  varSigma = varStar {delta = []} wfSigma dSigma

  fstSigma : Derivable
    (hasTy ((tySigma A B) ∷ gamma) ucFstBranch (wkTyBy 1 A))
  fstSigma = sigmaFst dWkSigma varSigma

  motiveTail : FitsSubst
    ((tySigma A B) ∷ gamma) gamma (keepSubstCtx 1 gamma)
  motiveTail =
    fitsKeep {delta = tySigma A B ∷ []} {gamma = gamma} wfSigma

  fstForMotive : Derivable
    (hasTy ((tySigma A B) ∷ gamma) ucFstBranch
      (subTy (keepSubstCtx 1 gamma) A))
  fstForMotive =
    subst
      (λ T -> Derivable
        (hasTy ((tySigma A B) ∷ gamma) ucFstBranch T))
      (renTyKeepSubstBy 1 A ∙ sym (keepSubstCtx-subTy 1 gamma A))
      fstSigma

  motiveFits : FitsSubst
    ((tySigma A B) ∷ gamma) (A ∷ gamma) (sigmaSndMotiveSub gamma)
  motiveFits = fitsCons motiveTail fstForMotive

  dM : Derivable
    (isType ((tySigma A B) ∷ gamma) (sigmaSndMotive gamma B))
  dM = substTyRule dB motiveFits

  wfA : CtxWF (A ∷ gamma)
  wfA = wfCons wfGamma dA

  wfBranch : CtxWF (B ∷ A ∷ gamma)
  wfBranch = wfCons wfA dB

  varB0 : Derivable
    (hasTy (B ∷ A ∷ gamma) (var zero) (wkTyBy 1 B))
  varB0 = varStar {delta = []} wfBranch dB

  branchTail : FitsEqSubst
    (B ∷ A ∷ gamma) gamma
    (keepSubstCtx 2 gamma) (keepSubstCtx 2 gamma)
  branchTail =
    fitsEqKeep {delta = B ∷ A ∷ []} {gamma = gamma} wfBranch

  fstEq0 : Derivable
    (termEq (B ∷ A ∷ gamma)
      (tmElSigma
        (tmPair (var (suc zero)) (var zero))
        (var (suc zero)))
      (var (suc zero))
      (wkTyBy 2 A))
  fstEq0 = sigmaBranchFstEq dSigma

  fstEq : Derivable
    (termEq (B ∷ A ∷ gamma)
      (tmElSigma
        (tmPair (var (suc zero)) (var zero))
        (var (suc zero)))
      (var (suc zero))
      (subTy (keepSubstCtx 2 gamma) A))
  fstEq =
    subst
      (λ T -> Derivable
        (termEq (B ∷ A ∷ gamma)
          (tmElSigma
            (tmPair (var (suc zero)) (var zero))
            (var (suc zero)))
          (var (suc zero)) T))
      (renTyKeepSubstBy 2 A ∙ sym (keepSubstCtx-subTy 2 gamma A))
      fstEq0

  branchFitsEq : FitsEqSubst
    (B ∷ A ∷ gamma) (A ∷ gamma)
    (sigmaSndBranchSub gamma) (sigmaSndVarSub gamma)
  branchFitsEq = fitsEqCons branchTail fstEq

  branchTyEq : Derivable
    (typeEq (B ∷ A ∷ gamma)
      (subTy (sigmaSndBranchSub gamma) B)
      (subTy (sigmaSndVarSub gamma) B))
  branchTyEq = eqSubTyRule dB branchFitsEq

  varBAtVarSub : Derivable
    (hasTy (B ∷ A ∷ gamma) (var zero)
      (subTy (sigmaSndVarSub gamma) B))
  varBAtVarSub =
    subst
      (λ T -> Derivable (hasTy (B ∷ A ∷ gamma) (var zero) T))
      (sym (sigmaSndVarTy gamma B))
      varB0

  varBAtBranchSub : Derivable
    (hasTy (B ∷ A ∷ gamma) (var zero)
      (subTy (sigmaSndBranchSub gamma) B))
  varBAtBranchSub =
    conv varBAtVarSub (symTy branchTyEq (assocTyRight branchTyEq))

  dBranch : Derivable
    (hasTy (B ∷ A ∷ gamma) (var zero)
      (sigmaBranchTy (sigmaSndMotive gamma B)))
  dBranch =
    subst
      (λ T -> Derivable (hasTy (B ∷ A ∷ gamma) (var zero) T))
      (sym (sigmaSndMotiveBranch gamma B))
      varBAtBranchSub

ucCohY : RawTerm
ucCohY = wkTmBy 1 ucFstBranch

ucCohU : RawTerm
ucCohU = wkTmBy 1 ucSndBranch

ucCohZ : RawTerm
ucCohZ = renTm qtrSecondBranchRen ucFstBranch

ucCohV : RawTerm
ucCohV = renTm qtrSecondBranchRen ucSndBranch

ucCohBase : RawType -> Subst
ucCohBase A = keepSubstCtx 2 (A ∷ [])

ucCohYSub : RawType -> Subst
ucCohYSub A = consSubst ucCohY (ucCohBase A)

ucCohUSub : RawType -> Subst
ucCohUSub A = consSubst ucCohU (ucCohYSub A)

ucCohZSub : RawType -> Subst
ucCohZSub A = consSubst ucCohZ (ucCohUSub A)

ucCohSub : RawType -> Subst
ucCohSub A = consSubst ucCohV (ucCohZSub A)

ucCohDropUSub : (A : RawType)
  -> compSubRen (ucCohUSub A) (addRen 2) ≡ ucCohBase A
ucCohDropUSub A = refl

ucCohRzSub : (A : RawType)
  -> compSubRen (ucCohZSub A) ucRzRen
       ≡ consSubst ucCohZ (ucCohBase A)
ucCohRzSub A = refl

ucCohFibreApply : (A : RawType) (a : RawTerm) (n : ℕ)
  -> applySubst
       (compSubRen (singleSubst a) (raiseRen (addRen 2))) n
       ≡ applySubst (consSubst a (ucCohBase A)) n
ucCohFibreApply A a zero = refl
ucCohFibreApply A a (suc zero) = refl
ucCohFibreApply A a (suc (suc n)) = refl

ucCohFibreTy : (A R : RawType) (a : RawTerm)
  -> subTy (singleSubst a) (renTy (raiseRen (addRen 2)) R)
       ≡ subTy (consSubst a (ucCohBase A)) R
ucCohFibreTy A R a =
  subTyRen (singleSubst a) (raiseRen (addRen 2)) R
  ∙ subTyEq (ucCohFibreApply A a) R

ucCohBaseTy : (A B : RawType)
  -> subTy (ucCohBase A) B ≡ wkTyBy 2 B
ucCohBaseTy A B =
  keepSubstCtx-subTy 2 (A ∷ []) B
  ∙ sym (renTyKeepSubstBy 2 B)

ucCohDropSub : (A : RawType)
  -> compSubRen (ucCohSub A) (addRen 4) ≡ ucCohBase A
ucCohDropSub A = refl

ucFstCoherence : {A B R : RawType}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> Derivable
       (termEq
         (wkTyBy 1 (ucCarrier B R) ∷ ucCarrier B R ∷ A ∷ [])
         (wkTmBy 1 ucFstBranch)
         (renTm qtrSecondBranchRen ucFstBranch)
         (qtrCohTy (wkTyBy 1 B)))
ucFstCoherence {A = A} {B = B} {R = R} dA dB dR dUniq =
  subst
    (λ T -> Derivable
      (termEq cohCtx ucCohY ucCohZ T))
    resultTyPath
    (substTmEqRule dUniq fitsV)
  where
  C : RawType
  C = ucCarrier B R

  cohCtx : Ctx
  cohCtx = wkTyBy 1 C ∷ C ∷ A ∷ []

  dC : Derivable (isType (A ∷ []) C)
  dC = fSigma dB dR

  wfA : CtxWF (A ∷ [])
  wfA = wfCons wfNil dA

  wfC : CtxWF (C ∷ A ∷ [])
  wfC = wfCons wfA dC

  dWkC : Derivable (isType (C ∷ A ∷ []) (wkTyBy 1 C))
  dWkC = weakenTy {delta = C ∷ []} dC wfC

  wfCoh : CtxWF cohCtx
  wfCoh = wfCons wfC dWkC

  dNiceC : Derivable (isType cohCtx (wkTyBy 2 C))
  dNiceC = weakenTy {delta = wkTyBy 1 C ∷ C ∷ []} dC wfCoh

  varC1 : Derivable (hasTy cohCtx (var (suc zero)) (wkTyBy 2 C))
  varC1 = varStar {gamma = A ∷ []} {delta = wkTyBy 1 C ∷ []} wfCoh dC

  varC0Nested : Derivable
    (hasTy cohCtx (var zero) (wkTyBy 1 (wkTyBy 1 C)))
  varC0Nested = varStar {delta = []} wfCoh dWkC

  varC0 : Derivable (hasTy cohCtx (var zero) (wkTyBy 2 C))
  varC0 =
    subst
      (λ T -> Derivable (hasTy cohCtx (var zero) T))
      (renTyComp (addRen 1) (addRen 1) C)
      varC0Nested

  dY0 : Derivable (hasTy cohCtx ucCohY (wkTyBy 2 B))
  dY0 = sigmaFst dNiceC varC1

  dZ0 : Derivable (hasTy cohCtx ucCohZ (wkTyBy 2 B))
  dZ0 = sigmaFst dNiceC varC0

  dU0 : Derivable
    (hasTy cohCtx ucCohU
      (subTy (singleSubst ucCohY)
        (renTy (raiseRen (addRen 2)) R)))
  dU0 = sigmaSnd dNiceC varC1

  dV0 : Derivable
    (hasTy cohCtx ucCohV
      (subTy (singleSubst ucCohZ)
        (renTy (raiseRen (addRen 2)) R)))
  dV0 = sigmaSnd dNiceC varC0

  baseFits : FitsSubst cohCtx (A ∷ []) (ucCohBase A)
  baseFits =
    fitsKeep {delta = wkTyBy 1 C ∷ C ∷ []} {gamma = A ∷ []} wfCoh

  dY : Derivable
    (hasTy cohCtx ucCohY (subTy (ucCohBase A) B))
  dY =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohY T))
      (sym (ucCohBaseTy A B))
      dY0

  fitsY : FitsSubst cohCtx (B ∷ A ∷ []) (ucCohYSub A)
  fitsY = fitsCons baseFits dY

  dU : Derivable
    (hasTy cohCtx ucCohU (subTy (ucCohYSub A) R))
  dU =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohU T))
      (ucCohFibreTy A R ucCohY)
      dU0

  fitsU : FitsSubst cohCtx (R ∷ B ∷ A ∷ []) (ucCohUSub A)
  fitsU = fitsCons fitsY dU

  zTyPath : subTy (ucCohUSub A) (wkTyBy 2 B) ≡ wkTyBy 2 B
  zTyPath =
    subTyRen (ucCohUSub A) (addRen 2) B
    ∙ cong (λ sigma -> subTy sigma B) (ucCohDropUSub A)
    ∙ ucCohBaseTy A B

  dZ : Derivable
    (hasTy cohCtx ucCohZ (subTy (ucCohUSub A) (wkTyBy 2 B)))
  dZ =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohZ T))
      (sym zTyPath)
      dZ0

  fitsZ : FitsSubst cohCtx
    (wkTyBy 2 B ∷ R ∷ B ∷ A ∷ []) (ucCohZSub A)
  fitsZ = fitsCons fitsU dZ

  rzPath : subTy (ucCohZSub A) (ucRz R)
    ≡ subTy (consSubst ucCohZ (ucCohBase A)) R
  rzPath =
    subTyRen (ucCohZSub A) ucRzRen R
    ∙ cong (λ sigma -> subTy sigma R) (ucCohRzSub A)

  dV : Derivable
    (hasTy cohCtx ucCohV (subTy (ucCohZSub A) (ucRz R)))
  dV =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohV T))
      (ucCohFibreTy A R ucCohZ ∙ sym rzPath)
      dV0

  fitsV : FitsSubst cohCtx
    (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ []) (ucCohSub A)
  fitsV = fitsCons fitsZ dV

  resultTyPath : subTy (ucCohSub A) (wkTyBy 4 B)
    ≡ qtrCohTy (wkTyBy 1 B)
  resultTyPath =
    subTyRen (ucCohSub A) (addRen 4) B
    ∙ cong (λ sigma -> subTy sigma B) (ucCohDropSub A)
    ∙ ucCohBaseTy A B
    ∙ sym (qtrCoh-wkTy B)

ucFun : {A B R : RawType} {t : RawTerm}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable (hasTy (A ∷ []) t (ucExists B R))
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> Derivable (hasTy (A ∷ []) (ucFunction t) B)
ucFun {A = A} {B = B} {R = R} {t = t} dA dB dR dEx dUniq =
  subst
    (λ T -> Derivable (hasTy (A ∷ []) (ucFunction t) T))
    (singleSubst-wkTy t B)
    (eQtr₁ dL dEx dBranch dCoh)
  where
  C : RawType
  C = ucCarrier B R

  Q : RawType
  Q = ucExists B R

  dC : Derivable (isType (A ∷ []) C)
  dC = fSigma dB dR

  dQ : Derivable (isType (A ∷ []) Q)
  dQ = fQtr dC

  wfA : CtxWF (A ∷ [])
  wfA = wfCons wfNil dA

  wfQ : CtxWF (Q ∷ A ∷ [])
  wfQ = wfCons wfA dQ

  dL : Derivable (isType (Q ∷ A ∷ []) (wkTyBy 1 B))
  dL = weakenTy {delta = Q ∷ []} dB wfQ

  wfC : CtxWF (C ∷ A ∷ [])
  wfC = wfCons wfA dC

  dWkC : Derivable (isType (C ∷ A ∷ []) (wkTyBy 1 C))
  dWkC = weakenTy {delta = C ∷ []} dC wfC

  varC : Derivable (hasTy (C ∷ A ∷ []) (var zero) (wkTyBy 1 C))
  varC = varStar {delta = []} wfC dC

  dBranch0 : Derivable
    (hasTy (C ∷ A ∷ []) ucFstBranch (wkTyBy 1 B))
  dBranch0 = sigmaFst dWkC varC

  dBranch : Derivable
    (hasTy (C ∷ A ∷ []) ucFstBranch
      (qtrBranchTy (wkTyBy 1 B)))
  dBranch =
    subst
      (λ T -> Derivable (hasTy (C ∷ A ∷ []) ucFstBranch T))
      (sym (qtrBranch-wkTy B))
      dBranch0

  dCoh : Derivable
    (termEq (wkTyBy 1 C ∷ C ∷ A ∷ [])
      (wkTmBy 1 ucFstBranch)
      (renTm qtrSecondBranchRen ucFstBranch)
      (qtrCohTy (wkTyBy 1 B)))
  dCoh = ucFstCoherence dA dB dR dUniq

ucLiftBase : RawType -> Subst
ucLiftBase A = keepSubstCtx 3 (A ∷ [])

ucLiftYSub : RawType -> Subst
ucLiftYSub A = consSubst ucCohY (ucLiftBase A)

ucLiftUSub : RawType -> Subst
ucLiftUSub A = consSubst ucCohU (ucLiftYSub A)

ucLiftZSub : RawType -> Subst
ucLiftZSub A = consSubst ucCohZ (ucLiftUSub A)

ucLiftSub : RawType -> Subst
ucLiftSub A = consSubst ucCohV (ucLiftZSub A)

ucLiftDropUSub : (A : RawType)
  -> compSubRen (ucLiftUSub A) (addRen 2) ≡ ucLiftBase A
ucLiftDropUSub A = refl

ucLiftRzSub : (A : RawType)
  -> compSubRen (ucLiftZSub A) ucRzRen
       ≡ consSubst ucCohZ (ucLiftBase A)
ucLiftRzSub A = refl

ucLiftDropSub : (A : RawType)
  -> compSubRen (ucLiftSub A) (addRen 4) ≡ ucLiftBase A
ucLiftDropSub A = refl

ucLiftFibreApply : (A : RawType) (a : RawTerm) (n : ℕ)
  -> applySubst
       (compSubRen (singleSubst a) (raiseRen (addRen 3))) n
       ≡ applySubst (consSubst a (ucLiftBase A)) n
ucLiftFibreApply A a zero = refl
ucLiftFibreApply A a (suc zero) = refl
ucLiftFibreApply A a (suc (suc n)) = refl

ucLiftFibreTy : (A R : RawType) (a : RawTerm)
  -> subTy (singleSubst a) (renTy (raiseRen (addRen 3)) R)
       ≡ subTy (consSubst a (ucLiftBase A)) R
ucLiftFibreTy A R a =
  subTyRen (singleSubst a) (raiseRen (addRen 3)) R
  ∙ subTyEq (ucLiftFibreApply A a) R

ucLiftBaseTy : (A B : RawType)
  -> subTy (ucLiftBase A) B ≡ wkTyBy 3 B
ucLiftBaseTy A B =
  keepSubstCtx-subTy 3 (A ∷ []) B
  ∙ sym (renTyKeepSubstBy 3 B)

ucLiftedFstCoherence : {A B R X : RawType}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable (isType (A ∷ []) X)
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> Derivable
       (termEq
         (wkTyBy 1 (wkTyBy 1 (ucCarrier B R))
           ∷ wkTyBy 1 (ucCarrier B R) ∷ X ∷ A ∷ [])
         (wkTmBy 1 ucFstBranch)
         (renTm qtrSecondBranchRen ucFstBranch)
         (qtrCohTy (wkTyBy 1 (wkTyBy 1 B))))
ucLiftedFstCoherence {A = A} {B = B} {R = R} {X = X}
  dA dB dR dX dUniq =
  subst
    (λ T -> Derivable (termEq cohCtx ucCohY ucCohZ T))
    resultTyPath
    (substTmEqRule dUniq fitsV)
  where
  C : RawType
  C = ucCarrier B R

  W : RawType
  W = wkTyBy 1 C

  cohCtx : Ctx
  cohCtx = wkTyBy 1 W ∷ W ∷ X ∷ A ∷ []

  dC : Derivable (isType (A ∷ []) C)
  dC = fSigma dB dR

  wfA : CtxWF (A ∷ [])
  wfA = wfCons wfNil dA

  wfX : CtxWF (X ∷ A ∷ [])
  wfX = wfCons wfA dX

  dW : Derivable (isType (X ∷ A ∷ []) W)
  dW = weakenTy {delta = X ∷ []} dC wfX

  wfW : CtxWF (W ∷ X ∷ A ∷ [])
  wfW = wfCons wfX dW

  dWkW : Derivable (isType (W ∷ X ∷ A ∷ []) (wkTyBy 1 W))
  dWkW = weakenTy {delta = W ∷ []} dW wfW

  wfCoh : CtxWF cohCtx
  wfCoh = wfCons wfW dWkW

  dNiceC : Derivable (isType cohCtx (wkTyBy 3 C))
  dNiceC =
    weakenTy {delta = wkTyBy 1 W ∷ W ∷ X ∷ []} dC wfCoh

  varC1Raw : Derivable
    (hasTy cohCtx (var (suc zero)) (wkTyBy 2 W))
  varC1Raw =
    varStar {gamma = X ∷ A ∷ []} {delta = wkTyBy 1 W ∷ []}
      wfCoh dW

  varC1 : Derivable (hasTy cohCtx (var (suc zero)) (wkTyBy 3 C))
  varC1 =
    subst
      (λ T -> Derivable (hasTy cohCtx (var (suc zero)) T))
      (renTyComp (addRen 2) (addRen 1) C)
      varC1Raw

  varC0Nested : Derivable
    (hasTy cohCtx (var zero) (wkTyBy 1 (wkTyBy 1 W)))
  varC0Nested = varStar {delta = []} wfCoh dWkW

  varC0 : Derivable (hasTy cohCtx (var zero) (wkTyBy 3 C))
  varC0 =
    subst
      (λ T -> Derivable (hasTy cohCtx (var zero) T))
      (renTyComp (addRen 1) (addRen 1) W
       ∙ renTyComp (addRen 2) (addRen 1) C)
      varC0Nested

  dY0 : Derivable (hasTy cohCtx ucCohY (wkTyBy 3 B))
  dY0 = sigmaFst dNiceC varC1

  dZ0 : Derivable (hasTy cohCtx ucCohZ (wkTyBy 3 B))
  dZ0 = sigmaFst dNiceC varC0

  dU0 : Derivable
    (hasTy cohCtx ucCohU
      (subTy (singleSubst ucCohY)
        (renTy (raiseRen (addRen 3)) R)))
  dU0 = sigmaSnd dNiceC varC1

  dV0 : Derivable
    (hasTy cohCtx ucCohV
      (subTy (singleSubst ucCohZ)
        (renTy (raiseRen (addRen 3)) R)))
  dV0 = sigmaSnd dNiceC varC0

  baseFits : FitsSubst cohCtx (A ∷ []) (ucLiftBase A)
  baseFits =
    fitsKeep
      {delta = wkTyBy 1 W ∷ W ∷ X ∷ []}
      {gamma = A ∷ []}
      wfCoh

  dY : Derivable
    (hasTy cohCtx ucCohY (subTy (ucLiftBase A) B))
  dY =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohY T))
      (sym (ucLiftBaseTy A B))
      dY0

  fitsY : FitsSubst cohCtx (B ∷ A ∷ []) (ucLiftYSub A)
  fitsY = fitsCons baseFits dY

  dU : Derivable
    (hasTy cohCtx ucCohU (subTy (ucLiftYSub A) R))
  dU =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohU T))
      (ucLiftFibreTy A R ucCohY)
      dU0

  fitsU : FitsSubst cohCtx (R ∷ B ∷ A ∷ []) (ucLiftUSub A)
  fitsU = fitsCons fitsY dU

  zTyPath : subTy (ucLiftUSub A) (wkTyBy 2 B) ≡ wkTyBy 3 B
  zTyPath =
    subTyRen (ucLiftUSub A) (addRen 2) B
    ∙ cong (λ sigma -> subTy sigma B) (ucLiftDropUSub A)
    ∙ ucLiftBaseTy A B

  dZ : Derivable
    (hasTy cohCtx ucCohZ (subTy (ucLiftUSub A) (wkTyBy 2 B)))
  dZ =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohZ T))
      (sym zTyPath)
      dZ0

  fitsZ : FitsSubst cohCtx
    (wkTyBy 2 B ∷ R ∷ B ∷ A ∷ []) (ucLiftZSub A)
  fitsZ = fitsCons fitsU dZ

  rzPath : subTy (ucLiftZSub A) (ucRz R)
    ≡ subTy (consSubst ucCohZ (ucLiftBase A)) R
  rzPath =
    subTyRen (ucLiftZSub A) ucRzRen R
    ∙ cong (λ sigma -> subTy sigma R) (ucLiftRzSub A)

  dV : Derivable
    (hasTy cohCtx ucCohV (subTy (ucLiftZSub A) (ucRz R)))
  dV =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohV T))
      (ucLiftFibreTy A R ucCohZ ∙ sym rzPath)
      dV0

  fitsV : FitsSubst cohCtx
    (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ []) (ucLiftSub A)
  fitsV = fitsCons fitsZ dV

  resultTyPath : subTy (ucLiftSub A) (wkTyBy 4 B)
    ≡ qtrCohTy (wkTyBy 1 (wkTyBy 1 B))
  resultTyPath =
    subTyRen (ucLiftSub A) (addRen 4) B
    ∙ cong (λ sigma -> subTy sigma B) (ucLiftDropSub A)
    ∙ ucLiftBaseTy A B
    ∙ sym (renTyComp (addRen 2) (addRen 1) B)
    ∙ sym (qtrCoh-wkTy (wkTyBy 1 B))

ucLiftedFst : {A B R X : RawType} {p : RawTerm}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable (isType (A ∷ []) X)
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> Derivable
       (hasTy (X ∷ A ∷ []) p (wkTyBy 1 (ucExists B R)))
  -> Derivable
       (hasTy (X ∷ A ∷ []) (tmElQtr ucFstBranch p) (wkTyBy 1 B))
ucLiftedFst {A = A} {B = B} {R = R} {X = X} {p = p}
  dA dB dR dX dUniq dp =
  subst
    (λ T -> Derivable
      (hasTy (X ∷ A ∷ []) (tmElQtr ucFstBranch p) T))
    (singleSubst-wkTy p (wkTyBy 1 B))
    (eQtr₁ dL dp dBranch dCoh)
  where
  C : RawType
  C = ucCarrier B R

  Q : RawType
  Q = ucExists B R

  W : RawType
  W = wkTyBy 1 C

  dC : Derivable (isType (A ∷ []) C)
  dC = fSigma dB dR

  dQ : Derivable (isType (A ∷ []) Q)
  dQ = fQtr dC

  wfA : CtxWF (A ∷ [])
  wfA = wfCons wfNil dA

  wfX : CtxWF (X ∷ A ∷ [])
  wfX = wfCons wfA dX

  dW : Derivable (isType (X ∷ A ∷ []) W)
  dW = weakenTy {delta = X ∷ []} dC wfX

  dWkQ : Derivable (isType (X ∷ A ∷ []) (wkTyBy 1 Q))
  dWkQ = weakenTy {delta = X ∷ []} dQ wfX

  wfQX : CtxWF (wkTyBy 1 Q ∷ X ∷ A ∷ [])
  wfQX = wfCons wfX dWkQ

  dWkB : Derivable (isType (X ∷ A ∷ []) (wkTyBy 1 B))
  dWkB = weakenTy {delta = X ∷ []} dB wfX

  dL : Derivable
    (isType (wkTyBy 1 Q ∷ X ∷ A ∷ [])
      (wkTyBy 1 (wkTyBy 1 B)))
  dL = weakenTy {delta = wkTyBy 1 Q ∷ []} dWkB wfQX

  wfW : CtxWF (W ∷ X ∷ A ∷ [])
  wfW = wfCons wfX dW

  dWkW : Derivable (isType (W ∷ X ∷ A ∷ []) (wkTyBy 1 W))
  dWkW = weakenTy {delta = W ∷ []} dW wfW

  varW : Derivable (hasTy (W ∷ X ∷ A ∷ []) (var zero) (wkTyBy 1 W))
  varW = varStar {delta = []} wfW dW

  dBranch0 : Derivable
    (hasTy (W ∷ X ∷ A ∷ []) ucFstBranch
      (wkTyBy 1 (wkTyBy 1 B)))
  dBranch0 = sigmaFst dWkW varW

  dBranch : Derivable
    (hasTy (W ∷ X ∷ A ∷ []) ucFstBranch
      (qtrBranchTy (wkTyBy 1 (wkTyBy 1 B))))
  dBranch =
    subst
      (λ T -> Derivable (hasTy (W ∷ X ∷ A ∷ []) ucFstBranch T))
      (sym (qtrBranch-wkTy (wkTyBy 1 B)))
      dBranch0

  dCoh : Derivable
    (termEq (wkTyBy 1 W ∷ W ∷ X ∷ A ∷ [])
      (wkTmBy 1 ucFstBranch)
      (renTm qtrSecondBranchRen ucFstBranch)
      (qtrCohTy (wkTyBy 1 (wkTyBy 1 B))))
  dCoh = ucLiftedFstCoherence dA dB dR dX dUniq

ucGenericFunction : RawTerm
ucGenericFunction = tmElQtr ucFstBranch (var zero)

ucProofMotiveSub : Subst
ucProofMotiveSub =
  consSubst ucGenericFunction (keepSubstBy 1)

ucProofMotive : RawType -> RawType
ucProofMotive R = subTy ucProofMotiveSub R

ucProofMotiveSubFull : RawType -> Subst
ucProofMotiveSubFull A =
  consSubst ucGenericFunction (keepSubstCtx 1 (A ∷ []))

ucProofMotiveSubApply : (A : RawType) (n : ℕ)
  -> applySubst (ucProofMotiveSubFull A) n
       ≡ applySubst ucProofMotiveSub n
ucProofMotiveSubApply A zero = refl
ucProofMotiveSubApply A (suc n) = keepSubstCtx-apply 1 (A ∷ []) n

ucProofMotiveSubTy : (A R : RawType)
  -> subTy (ucProofMotiveSubFull A) R ≡ ucProofMotive R
ucProofMotiveSubTy A R = subTyEq (ucProofMotiveSubApply A) R

ucProofConclusionTy : (R : RawType) (t : RawTerm)
  -> subTy (singleSubst t) (ucProofMotive R)
       ≡ ucFibre R (ucFunction t)
ucProofConclusionTy R t =
  subTyComp (singleSubst t) ucProofMotiveSub R

ucGenericClass : RawTerm
ucGenericClass = tmElQtr ucFstBranch (tmClass (var zero))

ucCohDropUOne : (A : RawType)
  -> compSubRen (ucCohUSub A) (addRen 1) ≡ ucCohYSub A
ucCohDropUOne A = refl

ucPropCohSub : RawType -> Subst
ucPropCohSub A = consSubst ucCohV (ucCohUSub A)

ucPropCohDrop : (A : RawType)
  -> compSubRen (ucPropCohSub A) (addRen 2) ≡ ucCohYSub A
ucPropCohDrop A = refl

ucCohGenericClass : RawTerm
ucCohGenericClass = wkTmBy 1 ucGenericClass

ucProofCohSub : Subst
ucProofCohSub = consSubst ucCohGenericClass (keepSubstBy 2)

ucProofCohSubFull : RawType -> Subst
ucProofCohSubFull A =
  consSubst ucCohGenericClass (ucCohBase A)

ucProofCohSubApply : (A : RawType) (n : ℕ)
  -> applySubst (ucProofCohSubFull A) n
       ≡ applySubst ucProofCohSub n
ucProofCohSubApply A zero = refl
ucProofCohSubApply A (suc n) = keepSubstCtx-apply 2 (A ∷ []) n

ucProofCohSubTy : (A R : RawType)
  -> subTy (ucProofCohSubFull A) R ≡ subTy ucProofCohSub R
ucProofCohSubTy A R = subTyEq (ucProofCohSubApply A) R

ucProofQtrCohTy : (R : RawType)
  -> qtrCohTy (ucProofMotive R) ≡ subTy ucProofCohSub R
ucProofQtrCohTy R = subTyComp qtrCohSub ucProofMotiveSub R

ucProofCoherence : {A B R : RawType}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable
       (termEq (wkTyBy 1 R ∷ R ∷ B ∷ A ∷ [])
         (var 1) (var zero) (wkTyBy 2 R))
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> Derivable
       (termEq
         (wkTyBy 1 (ucCarrier B R) ∷ ucCarrier B R ∷ A ∷ [])
         (wkTmBy 1 ucSndBranch)
         (renTm qtrSecondBranchRen ucSndBranch)
         (qtrCohTy (ucProofMotive R)))
ucProofCoherence {A = A} {B = B} {R = R}
  dA dB dR dProp dUniq =
  subst
    (λ T -> Derivable (termEq cohCtx ucCohU ucCohV T))
    (ucProofCohSubTy A R ∙ sym (ucProofQtrCohTy R))
    dUVAtGeneric
  where
  C : RawType
  C = ucCarrier B R

  cohCtx : Ctx
  cohCtx = wkTyBy 1 C ∷ C ∷ A ∷ []

  dC : Derivable (isType (A ∷ []) C)
  dC = fSigma dB dR

  wfA : CtxWF (A ∷ [])
  wfA = wfCons wfNil dA

  wfC : CtxWF (C ∷ A ∷ [])
  wfC = wfCons wfA dC

  dWkC : Derivable (isType (C ∷ A ∷ []) (wkTyBy 1 C))
  dWkC = weakenTy {delta = C ∷ []} dC wfC

  wfCoh : CtxWF cohCtx
  wfCoh = wfCons wfC dWkC

  dNiceC : Derivable (isType cohCtx (wkTyBy 2 C))
  dNiceC = weakenTy {delta = wkTyBy 1 C ∷ C ∷ []} dC wfCoh

  varC1 : Derivable (hasTy cohCtx (var (suc zero)) (wkTyBy 2 C))
  varC1 = varStar {gamma = A ∷ []} {delta = wkTyBy 1 C ∷ []} wfCoh dC

  varC0Nested : Derivable
    (hasTy cohCtx (var zero) (wkTyBy 1 (wkTyBy 1 C)))
  varC0Nested = varStar {delta = []} wfCoh dWkC

  varC0 : Derivable (hasTy cohCtx (var zero) (wkTyBy 2 C))
  varC0 =
    subst
      (λ T -> Derivable (hasTy cohCtx (var zero) T))
      (renTyComp (addRen 1) (addRen 1) C)
      varC0Nested

  dY0 : Derivable (hasTy cohCtx ucCohY (wkTyBy 2 B))
  dY0 = sigmaFst dNiceC varC1

  dZ0 : Derivable (hasTy cohCtx ucCohZ (wkTyBy 2 B))
  dZ0 = sigmaFst dNiceC varC0

  dU0 : Derivable
    (hasTy cohCtx ucCohU
      (subTy (singleSubst ucCohY)
        (renTy (raiseRen (addRen 2)) R)))
  dU0 = sigmaSnd dNiceC varC1

  dV0 : Derivable
    (hasTy cohCtx ucCohV
      (subTy (singleSubst ucCohZ)
        (renTy (raiseRen (addRen 2)) R)))
  dV0 = sigmaSnd dNiceC varC0

  baseFits : FitsSubst cohCtx (A ∷ []) (ucCohBase A)
  baseFits =
    fitsKeep {delta = wkTyBy 1 C ∷ C ∷ []} {gamma = A ∷ []} wfCoh

  dY : Derivable
    (hasTy cohCtx ucCohY (subTy (ucCohBase A) B))
  dY =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohY T))
      (sym (ucCohBaseTy A B))
      dY0

  fitsY : FitsSubst cohCtx (B ∷ A ∷ []) (ucCohYSub A)
  fitsY = fitsCons baseFits dY

  dU : Derivable
    (hasTy cohCtx ucCohU (subTy (ucCohYSub A) R))
  dU =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohU T))
      (ucCohFibreTy A R ucCohY)
      dU0

  fitsU : FitsSubst cohCtx (R ∷ B ∷ A ∷ []) (ucCohUSub A)
  fitsU = fitsCons fitsY dU

  dZ : Derivable
    (hasTy cohCtx ucCohZ (subTy (ucCohBase A) B))
  dZ =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohZ T))
      (sym (ucCohBaseTy A B))
      dZ0

  dYZ0 : Derivable
    (termEq cohCtx ucCohY ucCohZ (qtrCohTy (wkTyBy 1 B)))
  dYZ0 = ucFstCoherence dA dB dR dUniq

  dYZ : Derivable
    (termEq cohCtx ucCohY ucCohZ (subTy (ucCohBase A) B))
  dYZ =
    subst
      (λ T -> Derivable (termEq cohCtx ucCohY ucCohZ T))
      (qtrCoh-wkTy B ∙ sym (ucCohBaseTy A B))
      dYZ0

  fibreTailEq : FitsEqSubst cohCtx (A ∷ [])
    (ucCohBase A) (ucCohBase A)
  fibreTailEq =
    fitsEqKeep
      {delta = wkTyBy 1 C ∷ C ∷ []}
      {gamma = A ∷ []}
      wfCoh

  yzFitsEq : FitsEqSubst cohCtx (B ∷ A ∷ [])
    (ucCohYSub A) (consSubst ucCohZ (ucCohBase A))
  yzFitsEq = fitsEqCons fibreTailEq dYZ

  yzFibreEq : Derivable
    (typeEq cohCtx
      (subTy (ucCohYSub A) R)
      (subTy (consSubst ucCohZ (ucCohBase A)) R))
  yzFibreEq = eqSubTyRule dR yzFitsEq

  dVRight : Derivable
    (hasTy cohCtx ucCohV
      (subTy (consSubst ucCohZ (ucCohBase A)) R))
  dVRight =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohV T))
      (ucCohFibreTy A R ucCohZ)
      dV0

  dVLeft : Derivable
    (hasTy cohCtx ucCohV (subTy (ucCohYSub A) R))
  dVLeft =
    conv dVRight (symTy yzFibreEq (assocTyRight yzFibreEq))

  vTyPath : subTy (ucCohUSub A) (wkTyBy 1 R)
    ≡ subTy (ucCohYSub A) R
  vTyPath =
    subTyRen (ucCohUSub A) (addRen 1) R
    ∙ cong (λ sigma -> subTy sigma R) (ucCohDropUOne A)

  dVForProp : Derivable
    (hasTy cohCtx ucCohV (subTy (ucCohUSub A) (wkTyBy 1 R)))
  dVForProp =
    subst
      (λ T -> Derivable (hasTy cohCtx ucCohV T))
      (sym vTyPath)
      dVLeft

  propFits : FitsSubst cohCtx
    (wkTyBy 1 R ∷ R ∷ B ∷ A ∷ []) (ucPropCohSub A)
  propFits = fitsCons fitsU dVForProp

  propTyPath : subTy (ucPropCohSub A) (wkTyBy 2 R)
    ≡ subTy (ucCohYSub A) R
  propTyPath =
    subTyRen (ucPropCohSub A) (addRen 2) R
    ∙ cong (λ sigma -> subTy sigma R) (ucPropCohDrop A)

  dUVLeft : Derivable
    (termEq cohCtx ucCohU ucCohV (subTy (ucCohYSub A) R))
  dUVLeft =
    subst
      (λ T -> Derivable (termEq cohCtx ucCohU ucCohV T))
      propTyPath
      (substTmEqRule dProp propFits)

  Q : RawType
  Q = ucExists B R

  W : RawType
  W = wkTyBy 1 C

  dQ : Derivable (isType (A ∷ []) Q)
  dQ = fQtr dC

  dWkQ : Derivable (isType (C ∷ A ∷ []) (wkTyBy 1 Q))
  dWkQ = weakenTy {delta = C ∷ []} dQ wfC

  wfQBranch : CtxWF (wkTyBy 1 Q ∷ C ∷ A ∷ [])
  wfQBranch = wfCons wfC dWkQ

  dWkB : Derivable (isType (C ∷ A ∷ []) (wkTyBy 1 B))
  dWkB = weakenTy {delta = C ∷ []} dB wfC

  dInnerL : Derivable
    (isType (wkTyBy 1 Q ∷ C ∷ A ∷ [])
      (wkTyBy 1 (wkTyBy 1 B)))
  dInnerL = weakenTy {delta = wkTyBy 1 Q ∷ []} dWkB wfQBranch

  wfW : CtxWF (W ∷ C ∷ A ∷ [])
  wfW = wfCons wfC dWkC

  dWkW : Derivable (isType (W ∷ C ∷ A ∷ []) (wkTyBy 1 W))
  dWkW = weakenTy {delta = W ∷ []} dWkC wfW

  varW : Derivable (hasTy (W ∷ C ∷ A ∷ []) (var zero) (wkTyBy 1 W))
  varW = varStar {delta = []} wfW dWkC

  dInnerBranch0 : Derivable
    (hasTy (W ∷ C ∷ A ∷ []) ucFstBranch
      (wkTyBy 1 (wkTyBy 1 B)))
  dInnerBranch0 = sigmaFst dWkW varW

  dInnerBranch : Derivable
    (hasTy (W ∷ C ∷ A ∷ []) ucFstBranch
      (qtrBranchTy (wkTyBy 1 (wkTyBy 1 B))))
  dInnerBranch =
    subst
      (λ T -> Derivable (hasTy (W ∷ C ∷ A ∷ []) ucFstBranch T))
      (sym (qtrBranch-wkTy (wkTyBy 1 B)))
      dInnerBranch0

  dInnerCoh : Derivable
    (termEq (wkTyBy 1 W ∷ W ∷ C ∷ A ∷ [])
      (wkTmBy 1 ucFstBranch)
      (renTm qtrSecondBranchRen ucFstBranch)
      (qtrCohTy (wkTyBy 1 (wkTyBy 1 B))))
  dInnerCoh = ucLiftedFstCoherence dA dB dR dC dUniq

  varC : Derivable (hasTy (C ∷ A ∷ []) (var zero) (wkTyBy 1 C))
  varC = varStar {delta = []} wfC dC

  dBeta0 : Derivable
    (termEq (C ∷ A ∷ []) ucGenericClass ucFstBranch (wkTyBy 1 B))
  dBeta0 =
    subst
      (λ T -> Derivable
        (termEq (C ∷ A ∷ []) ucGenericClass ucFstBranch T))
      (singleSubst-wkTy (tmClass (var zero)) (wkTyBy 1 B))
      (cQtr₁ dInnerL varC dInnerBranch dInnerCoh)

  dBetaNested : Derivable
    (termEq cohCtx ucCohGenericClass ucCohY
      (wkTyBy 1 (wkTyBy 1 B)))
  dBetaNested =
    weakenTmEq {delta = wkTyBy 1 C ∷ []} dBeta0 wfCoh

  dBeta : Derivable
    (termEq cohCtx ucCohGenericClass ucCohY
      (subTy (ucCohBase A) B))
  dBeta =
    subst
      (λ T -> Derivable
        (termEq cohCtx ucCohGenericClass ucCohY T))
      (renTyComp (addRen 1) (addRen 1) B
       ∙ sym (ucCohBaseTy A B))
      dBetaNested

  genericFitsEq : FitsEqSubst cohCtx (B ∷ A ∷ [])
    (ucProofCohSubFull A) (ucCohYSub A)
  genericFitsEq = fitsEqCons fibreTailEq dBeta

  genericFibreEq : Derivable
    (typeEq cohCtx
      (subTy (ucProofCohSubFull A) R)
      (subTy (ucCohYSub A) R))
  genericFibreEq = eqSubTyRule dR genericFitsEq

  dUVAtGeneric : Derivable
    (termEq cohCtx ucCohU ucCohV
      (subTy (ucProofCohSubFull A) R))
  dUVAtGeneric =
    convEq dUVLeft
      (symTy genericFibreEq (assocTyRight genericFibreEq))

ucProofMotiveTy : {A B R : RawType}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> Derivable
       (isType (ucExists B R ∷ A ∷ []) (ucProofMotive R))
ucProofMotiveTy {A = A} {B = B} {R = R} dA dB dR dUniq =
  subst
    (λ T -> Derivable (isType (Q ∷ A ∷ []) T))
    (ucProofMotiveSubTy A R)
    (substTyRule dR motiveFits)
  where
  C : RawType
  C = ucCarrier B R

  Q : RawType
  Q = ucExists B R

  dC : Derivable (isType (A ∷ []) C)
  dC = fSigma dB dR

  dQ : Derivable (isType (A ∷ []) Q)
  dQ = fQtr dC

  wfA : CtxWF (A ∷ [])
  wfA = wfCons wfNil dA

  wfQ : CtxWF (Q ∷ A ∷ [])
  wfQ = wfCons wfA dQ

  varQ : Derivable (hasTy (Q ∷ A ∷ []) (var zero) (wkTyBy 1 Q))
  varQ = varStar {delta = []} wfQ dQ

  dGenericF : Derivable
    (hasTy (Q ∷ A ∷ []) ucGenericFunction (wkTyBy 1 B))
  dGenericF = ucLiftedFst dA dB dR dQ dUniq varQ

  motiveTail : FitsSubst
    (Q ∷ A ∷ []) (A ∷ []) (keepSubstCtx 1 (A ∷ []))
  motiveTail =
    fitsKeep {delta = Q ∷ []} {gamma = A ∷ []} wfQ

  genericFForFits : Derivable
    (hasTy (Q ∷ A ∷ []) ucGenericFunction
      (subTy (keepSubstCtx 1 (A ∷ [])) B))
  genericFForFits =
    subst
      (λ T -> Derivable
        (hasTy (Q ∷ A ∷ []) ucGenericFunction T))
      (renTyKeepSubstBy 1 B
       ∙ sym (keepSubstCtx-subTy 1 (A ∷ []) B))
      dGenericF

  motiveFits : FitsSubst
    (Q ∷ A ∷ []) (B ∷ A ∷ []) (ucProofMotiveSubFull A)
  motiveFits = fitsCons motiveTail genericFForFits

ucProofBranchSub : Subst
ucProofBranchSub = consSubst ucGenericClass (keepSubstBy 1)

ucProofBranchSubFull : RawType -> Subst
ucProofBranchSubFull A =
  consSubst ucGenericClass (keepSubstCtx 1 (A ∷ []))

ucProofBranchSubApply : (A : RawType) (n : ℕ)
  -> applySubst (ucProofBranchSubFull A) n
       ≡ applySubst ucProofBranchSub n
ucProofBranchSubApply A zero = refl
ucProofBranchSubApply A (suc n) = keepSubstCtx-apply 1 (A ∷ []) n

ucProofBranchSubTy : (A R : RawType)
  -> subTy (ucProofBranchSubFull A) R
       ≡ subTy ucProofBranchSub R
ucProofBranchSubTy A R = subTyEq (ucProofBranchSubApply A) R

ucProofQtrBranchTy : (R : RawType)
  -> qtrBranchTy (ucProofMotive R)
       ≡ subTy ucProofBranchSub R
ucProofQtrBranchTy R =
  subTyComp qtrBranchSub ucProofMotiveSub R

ucBranchBase : RawType -> Subst
ucBranchBase A = keepSubstCtx 1 (A ∷ [])

ucBranchFibreApply : (A : RawType) (a : RawTerm) (n : ℕ)
  -> applySubst
       (compSubRen (singleSubst a) (raiseRen (addRen 1))) n
       ≡ applySubst (consSubst a (ucBranchBase A)) n
ucBranchFibreApply A a zero = refl
ucBranchFibreApply A a (suc zero) = refl
ucBranchFibreApply A a (suc (suc n)) = refl

ucBranchFibreTy : (A R : RawType) (a : RawTerm)
  -> subTy (singleSubst a) (renTy (raiseRen (addRen 1)) R)
       ≡ subTy (consSubst a (ucBranchBase A)) R
ucBranchFibreTy A R a =
  subTyRen (singleSubst a) (raiseRen (addRen 1)) R
  ∙ subTyEq (ucBranchFibreApply A a) R

ucProofBranch : {A B R : RawType}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> Derivable
       (hasTy (ucCarrier B R ∷ A ∷ []) ucSndBranch
         (qtrBranchTy (ucProofMotive R)))
ucProofBranch {A = A} {B = B} {R = R} dA dB dR dUniq =
  subst
    (λ T -> Derivable (hasTy (C ∷ A ∷ []) ucSndBranch T))
    (ucProofBranchSubTy A R ∙ sym (ucProofQtrBranchTy R))
    dSndGeneric
  where
  C : RawType
  C = ucCarrier B R

  dC : Derivable (isType (A ∷ []) C)
  dC = fSigma dB dR

  wfA : CtxWF (A ∷ [])
  wfA = wfCons wfNil dA

  wfC : CtxWF (C ∷ A ∷ [])
  wfC = wfCons wfA dC

  dWkC : Derivable (isType (C ∷ A ∷ []) (wkTyBy 1 C))
  dWkC = weakenTy {delta = C ∷ []} dC wfC

  varC : Derivable (hasTy (C ∷ A ∷ []) (var zero) (wkTyBy 1 C))
  varC = varStar {delta = []} wfC dC

  dSnd0 : Derivable
    (hasTy (C ∷ A ∷ []) ucSndBranch
      (subTy (singleSubst ucFstBranch)
        (renTy (raiseRen (addRen 1)) R)))
  dSnd0 = sigmaSnd dWkC varC

  dSndFst : Derivable
    (hasTy (C ∷ A ∷ []) ucSndBranch
      (subTy (consSubst ucFstBranch (ucBranchBase A)) R))
  dSndFst =
    subst
      (λ T -> Derivable (hasTy (C ∷ A ∷ []) ucSndBranch T))
      (ucBranchFibreTy A R ucFstBranch)
      dSnd0

  Q : RawType
  Q = ucExists B R

  W : RawType
  W = wkTyBy 1 C

  dQ : Derivable (isType (A ∷ []) Q)
  dQ = fQtr dC

  dWkQ : Derivable (isType (C ∷ A ∷ []) (wkTyBy 1 Q))
  dWkQ = weakenTy {delta = C ∷ []} dQ wfC

  wfQBranch : CtxWF (wkTyBy 1 Q ∷ C ∷ A ∷ [])
  wfQBranch = wfCons wfC dWkQ

  dWkB : Derivable (isType (C ∷ A ∷ []) (wkTyBy 1 B))
  dWkB = weakenTy {delta = C ∷ []} dB wfC

  dInnerL : Derivable
    (isType (wkTyBy 1 Q ∷ C ∷ A ∷ [])
      (wkTyBy 1 (wkTyBy 1 B)))
  dInnerL = weakenTy {delta = wkTyBy 1 Q ∷ []} dWkB wfQBranch

  wfW : CtxWF (W ∷ C ∷ A ∷ [])
  wfW = wfCons wfC dWkC

  dWkW : Derivable (isType (W ∷ C ∷ A ∷ []) (wkTyBy 1 W))
  dWkW = weakenTy {delta = W ∷ []} dWkC wfW

  varW : Derivable (hasTy (W ∷ C ∷ A ∷ []) (var zero) (wkTyBy 1 W))
  varW = varStar {delta = []} wfW dWkC

  dInnerBranch0 : Derivable
    (hasTy (W ∷ C ∷ A ∷ []) ucFstBranch
      (wkTyBy 1 (wkTyBy 1 B)))
  dInnerBranch0 = sigmaFst dWkW varW

  dInnerBranch : Derivable
    (hasTy (W ∷ C ∷ A ∷ []) ucFstBranch
      (qtrBranchTy (wkTyBy 1 (wkTyBy 1 B))))
  dInnerBranch =
    subst
      (λ T -> Derivable (hasTy (W ∷ C ∷ A ∷ []) ucFstBranch T))
      (sym (qtrBranch-wkTy (wkTyBy 1 B)))
      dInnerBranch0

  dInnerCoh : Derivable
    (termEq (wkTyBy 1 W ∷ W ∷ C ∷ A ∷ [])
      (wkTmBy 1 ucFstBranch)
      (renTm qtrSecondBranchRen ucFstBranch)
      (qtrCohTy (wkTyBy 1 (wkTyBy 1 B))))
  dInnerCoh = ucLiftedFstCoherence dA dB dR dC dUniq

  dBeta0 : Derivable
    (termEq (C ∷ A ∷ []) ucGenericClass ucFstBranch (wkTyBy 1 B))
  dBeta0 =
    subst
      (λ T -> Derivable
        (termEq (C ∷ A ∷ []) ucGenericClass ucFstBranch T))
      (singleSubst-wkTy (tmClass (var zero)) (wkTyBy 1 B))
      (cQtr₁ dInnerL varC dInnerBranch dInnerCoh)

  dBeta : Derivable
    (termEq (C ∷ A ∷ []) ucGenericClass ucFstBranch
      (subTy (ucBranchBase A) B))
  dBeta =
    subst
      (λ T -> Derivable
        (termEq (C ∷ A ∷ []) ucGenericClass ucFstBranch T))
      (renTyKeepSubstBy 1 B
       ∙ sym (keepSubstCtx-subTy 1 (A ∷ []) B))
      dBeta0

  tailEq : FitsEqSubst
    (C ∷ A ∷ []) (A ∷ []) (ucBranchBase A) (ucBranchBase A)
  tailEq =
    fitsEqKeep {delta = C ∷ []} {gamma = A ∷ []} wfC

  fibreFitsEq : FitsEqSubst
    (C ∷ A ∷ []) (B ∷ A ∷ [])
    (ucProofBranchSubFull A)
    (consSubst ucFstBranch (ucBranchBase A))
  fibreFitsEq = fitsEqCons tailEq dBeta

  fibreEq : Derivable
    (typeEq (C ∷ A ∷ [])
      (subTy (ucProofBranchSubFull A) R)
      (subTy (consSubst ucFstBranch (ucBranchBase A)) R))
  fibreEq = eqSubTyRule dR fibreFitsEq

  dSndGeneric : Derivable
    (hasTy (C ∷ A ∷ []) ucSndBranch
      (subTy (ucProofBranchSubFull A) R))
  dSndGeneric =
    conv dSndFst (symTy fibreEq (assocTyRight fibreEq))

ucProof : {A B R : RawType} {t : RawTerm}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable
       (termEq (wkTyBy 1 R ∷ R ∷ B ∷ A ∷ [])
         (var 1) (var zero) (wkTyBy 2 R))
  -> Derivable (hasTy (A ∷ []) t (ucExists B R))
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> Derivable
       (hasTy (A ∷ []) (ucWitness t)
         (ucFibre R (ucFunction t)))
ucProof {A = A} {B = B} {R = R} {t = t}
  dA dB dR dProp dEx dUniq =
  subst
    (λ T -> Derivable (hasTy (A ∷ []) (ucWitness t) T))
    (ucProofConclusionTy R t)
    (eQtr₁
      (ucProofMotiveTy dA dB dR dUniq)
      dEx
      (ucProofBranch dA dB dR dUniq)
      (ucProofCoherence dA dB dR dProp dUniq))

ucUniqueBase : RawType -> Subst
ucUniqueBase A = keepSubstCtx 0 (A ∷ [])

ucUniqueYSub : RawType -> RawTerm -> Subst
ucUniqueYSub A f = consSubst f (ucUniqueBase A)

ucUniqueUSub : RawType -> RawTerm -> RawTerm -> Subst
ucUniqueUSub A f r = consSubst r (ucUniqueYSub A f)

ucUniqueZSub : RawType -> RawTerm -> RawTerm -> RawTerm -> Subst
ucUniqueZSub A f r g = consSubst g (ucUniqueUSub A f r)

ucUniqueSub : RawType -> RawTerm -> RawTerm -> RawTerm -> RawTerm -> Subst
ucUniqueSub A f r g s = consSubst s (ucUniqueZSub A f r g)

ucUniqueDropUSub : (A : RawType) (f r : RawTerm)
  -> compSubRen (ucUniqueUSub A f r) (addRen 2)
       ≡ ucUniqueBase A
ucUniqueDropUSub A f r = refl

ucUniqueRzSub : (A : RawType) (f r g : RawTerm)
  -> compSubRen (ucUniqueZSub A f r g) ucRzRen
       ≡ consSubst g (ucUniqueBase A)
ucUniqueRzSub A f r g = refl

ucUniqueDropSub : (A : RawType) (f r g s : RawTerm)
  -> compSubRen (ucUniqueSub A f r g s) (addRen 4)
       ≡ ucUniqueBase A
ucUniqueDropSub A f r g s = refl

ucUniqueBaseTy : (A B : RawType)
  -> subTy (ucUniqueBase A) B ≡ B
ucUniqueBaseTy A B =
  keepSubstCtx-subTy 0 (A ∷ []) B
  ∙ subTyId B

ucUnique : {A B R : RawType} {t : RawTerm}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable
       (termEq (wkTyBy 1 R ∷ R ∷ B ∷ A ∷ [])
         (var 1) (var zero) (wkTyBy 2 R))
  -> Derivable (hasTy (A ∷ []) t (ucExists B R))
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> {g s : RawTerm}
  -> Derivable (hasTy (A ∷ []) g B)
  -> Derivable (hasTy (A ∷ []) s (ucFibre R g))
  -> Derivable
       (termEq (A ∷ []) (ucFunction t) g B)
ucUnique {A = A} {B = B} {R = R} {t = t}
  dA dB dR dProp dEx dUniq {g = g} {s = s} dg ds =
  subst
    (λ T -> Derivable (termEq (A ∷ []) f g T))
    resultTyPath
    (substTmEqRule dUniq fitsS)
  where
  f : RawTerm
  f = ucFunction t

  r : RawTerm
  r = ucWitness t

  df : Derivable (hasTy (A ∷ []) f B)
  df = ucFun dA dB dR dEx dUniq

  dr : Derivable (hasTy (A ∷ []) r (ucFibre R f))
  dr = ucProof dA dB dR dProp dEx dUniq

  wfA : CtxWF (A ∷ [])
  wfA = wfCons wfNil dA

  baseFits : FitsSubst (A ∷ []) (A ∷ []) (ucUniqueBase A)
  baseFits = fitsKeep {delta = []} {gamma = A ∷ []} wfA

  dfForFits : Derivable
    (hasTy (A ∷ []) f (subTy (ucUniqueBase A) B))
  dfForFits =
    subst
      (λ T -> Derivable (hasTy (A ∷ []) f T))
      (sym (ucUniqueBaseTy A B))
      df

  fitsF : FitsSubst (A ∷ []) (B ∷ A ∷ []) (ucUniqueYSub A f)
  fitsF = fitsCons baseFits dfForFits

  fibreFPath : subTy (ucUniqueYSub A f) R ≡ ucFibre R f
  fibreFPath = singleSubstCtx-subTy f (A ∷ []) R

  drForFits : Derivable
    (hasTy (A ∷ []) r (subTy (ucUniqueYSub A f) R))
  drForFits =
    subst
      (λ T -> Derivable (hasTy (A ∷ []) r T))
      (sym fibreFPath)
      dr

  fitsR : FitsSubst (A ∷ [])
    (R ∷ B ∷ A ∷ []) (ucUniqueUSub A f r)
  fitsR = fitsCons fitsF drForFits

  gTyPath : subTy (ucUniqueUSub A f r) (wkTyBy 2 B) ≡ B
  gTyPath =
    subTyRen (ucUniqueUSub A f r) (addRen 2) B
    ∙ cong (λ sigma -> subTy sigma B) (ucUniqueDropUSub A f r)
    ∙ ucUniqueBaseTy A B

  dgForFits : Derivable
    (hasTy (A ∷ []) g (subTy (ucUniqueUSub A f r) (wkTyBy 2 B)))
  dgForFits =
    subst
      (λ T -> Derivable (hasTy (A ∷ []) g T))
      (sym gTyPath)
      dg

  fitsG : FitsSubst (A ∷ [])
    (wkTyBy 2 B ∷ R ∷ B ∷ A ∷ []) (ucUniqueZSub A f r g)
  fitsG = fitsCons fitsR dgForFits

  sTyPath : subTy (ucUniqueZSub A f r g) (ucRz R)
    ≡ ucFibre R g
  sTyPath =
    subTyRen (ucUniqueZSub A f r g) ucRzRen R
    ∙ cong (λ sigma -> subTy sigma R) (ucUniqueRzSub A f r g)
    ∙ singleSubstCtx-subTy g (A ∷ []) R

  dsForFits : Derivable
    (hasTy (A ∷ []) s (subTy (ucUniqueZSub A f r g) (ucRz R)))
  dsForFits =
    subst
      (λ T -> Derivable (hasTy (A ∷ []) s T))
      (sym sTyPath)
      ds

  fitsS : FitsSubst (A ∷ [])
    (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
    (ucUniqueSub A f r g s)
  fitsS = fitsCons fitsG dsForFits

  resultTyPath : subTy (ucUniqueSub A f r g s) (wkTyBy 4 B) ≡ B
  resultTyPath =
    subTyRen (ucUniqueSub A f r g s) (addRen 4) B
    ∙ cong (λ sigma -> subTy sigma B) (ucUniqueDropSub A f r g s)
    ∙ ucUniqueBaseTy A B

ucLiftedFstClass : {A B R X : RawType} {a : RawTerm}
  -> Derivable (isType [] A)
  -> Derivable (isType (A ∷ []) B)
  -> Derivable (isType (B ∷ A ∷ []) R)
  -> Derivable (isType (A ∷ []) X)
  -> Derivable
       (termEq
         (ucRz R ∷ wkTyBy 2 B ∷ R ∷ B ∷ A ∷ [])
         (var 3) (var 1) (wkTyBy 4 B))
  -> Derivable
       (hasTy (X ∷ A ∷ []) a (wkTyBy 1 (ucCarrier B R)))
  -> Derivable
       (termEq (X ∷ A ∷ [])
         (tmElQtr ucFstBranch (tmClass a))
         (tmElSigma a (var (suc zero)))
         (wkTyBy 1 B))
ucLiftedFstClass {A = A} {B = B} {R = R} {X = X} {a = a}
  dA dB dR dX dUniq da =
  subst
    (λ T -> Derivable
      (termEq (X ∷ A ∷ [])
        (tmElQtr ucFstBranch (tmClass a))
        (tmElSigma a (var (suc zero))) T))
    (singleSubst-wkTy (tmClass a) (wkTyBy 1 B))
    (cQtr₁ dL da dBranch dCoh)
  where
  C : RawType
  C = ucCarrier B R

  Q : RawType
  Q = ucExists B R

  W : RawType
  W = wkTyBy 1 C

  dC : Derivable (isType (A ∷ []) C)
  dC = fSigma dB dR

  dQ : Derivable (isType (A ∷ []) Q)
  dQ = fQtr dC

  wfA : CtxWF (A ∷ [])
  wfA = wfCons wfNil dA

  wfX : CtxWF (X ∷ A ∷ [])
  wfX = wfCons wfA dX

  dW : Derivable (isType (X ∷ A ∷ []) W)
  dW = weakenTy {delta = X ∷ []} dC wfX

  dWkQ : Derivable (isType (X ∷ A ∷ []) (wkTyBy 1 Q))
  dWkQ = weakenTy {delta = X ∷ []} dQ wfX

  wfQX : CtxWF (wkTyBy 1 Q ∷ X ∷ A ∷ [])
  wfQX = wfCons wfX dWkQ

  dWkB : Derivable (isType (X ∷ A ∷ []) (wkTyBy 1 B))
  dWkB = weakenTy {delta = X ∷ []} dB wfX

  dL : Derivable
    (isType (wkTyBy 1 Q ∷ X ∷ A ∷ [])
      (wkTyBy 1 (wkTyBy 1 B)))
  dL = weakenTy {delta = wkTyBy 1 Q ∷ []} dWkB wfQX

  wfW : CtxWF (W ∷ X ∷ A ∷ [])
  wfW = wfCons wfX dW

  dWkW : Derivable (isType (W ∷ X ∷ A ∷ []) (wkTyBy 1 W))
  dWkW = weakenTy {delta = W ∷ []} dW wfW

  varW : Derivable (hasTy (W ∷ X ∷ A ∷ []) (var zero) (wkTyBy 1 W))
  varW = varStar {delta = []} wfW dW

  dBranch0 : Derivable
    (hasTy (W ∷ X ∷ A ∷ []) ucFstBranch
      (wkTyBy 1 (wkTyBy 1 B)))
  dBranch0 = sigmaFst dWkW varW

  dBranch : Derivable
    (hasTy (W ∷ X ∷ A ∷ []) ucFstBranch
      (qtrBranchTy (wkTyBy 1 (wkTyBy 1 B))))
  dBranch =
    subst
      (λ T -> Derivable (hasTy (W ∷ X ∷ A ∷ []) ucFstBranch T))
      (sym (qtrBranch-wkTy (wkTyBy 1 B)))
      dBranch0

  dCoh : Derivable
    (termEq (wkTyBy 1 W ∷ W ∷ X ∷ A ∷ [])
      (wkTmBy 1 ucFstBranch)
      (renTm qtrSecondBranchRen ucFstBranch)
      (qtrCohTy (wkTyBy 1 (wkTyBy 1 B))))
  dCoh = ucLiftedFstCoherence dA dB dR dX dUniq
