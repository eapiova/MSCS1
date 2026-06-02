{-# OPTIONS --safe #-}

module Tait.Minimal.Substitution where

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

open import Tait.Minimal.Base public

open import Tait.Minimal.Renaming public
minSelfTmTy : {gamma : Ctx} {t : RawTerm} {A : RawType}
  -> Minimal (hasTy gamma t A)
  -> Minimal (isType gamma A)
minSelfTmTy {gamma = gamma} {A = A} d with renFitsIdTo (minDerivToCtxWF d)
... | renFitsTo rho fits rhoId =
  subst
    (λ T -> Minimal (isType gamma T))
    (renTyIdBy rhoId A)
    (minRenTmTy d fits)

oneLiftCancelTm : (a t : RawTerm)
  -> subTm (qtrCompSub a) (renTm sucRen t) ≡ t
oneLiftCancelTm a t =
  subTmRen (qtrCompSub a) sucRen t
  ∙ subTmId t

twoLiftCancelTm : (b c t : RawTerm)
  -> subTm (sigmaCompSub b c) (renTm sucRen (renTm sucRen t)) ≡ t
twoLiftCancelTm b c t =
  subTmRen (sigmaCompSub b c) sucRen (renTm sucRen t)
  ∙ subTmRen (consSubst b idSubst) sucRen t
  ∙ subTmId t

subSigmaCompSub-apply : (sigma : Subst) (b c : RawTerm) (n : ℕ)
  -> applySubst (compSub sigma (sigmaCompSub b c)) n
       ≡ applySubst
           (compSub
             (sigmaCompSub (subTm sigma b) (subTm sigma c))
             (liftSubst (liftSubst sigma)))
           n
subSigmaCompSub-apply sigma b c zero = refl
subSigmaCompSub-apply sigma b c (suc zero) = refl
subSigmaCompSub-apply sigma b c (suc (suc n)) =
  sym (twoLiftCancelTm (subTm sigma b) (subTm sigma c) (applySubst sigma n))
  ∙ cong
      (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c)))
      (sym
        (liftSubst-apply-suc (liftSubst sigma) (suc n)
         ∙ cong (renTm sucRen) (liftSubst-apply-suc sigma n)))
  ∙ sym
      (applySubst-compSub
        (sigmaCompSub (subTm sigma b) (subTm sigma c))
        (liftSubst (liftSubst sigma))
        (suc (suc n)))

subSigmaCompSubTm : (sigma : Subst) (b c m : RawTerm)
  -> subTm sigma (subTm (sigmaCompSub b c) m)
       ≡ subTm
           (sigmaCompSub (subTm sigma b) (subTm sigma c))
           (subTm (liftSubst (liftSubst sigma)) m)
subSigmaCompSubTm sigma b c m =
  subTmComp sigma (sigmaCompSub b c) m
  ∙ subTmEq (subSigmaCompSub-apply sigma b c) m
  ∙ sym
      (subTmComp
        (sigmaCompSub (subTm sigma b) (subTm sigma c))
        (liftSubst (liftSubst sigma))
        m)

subQtrCompSub-apply : (sigma : Subst) (a : RawTerm) (n : ℕ)
  -> applySubst (compSub sigma (qtrCompSub a)) n
       ≡ applySubst
           (compSub (qtrCompSub (subTm sigma a)) (liftSubst sigma))
           n
subQtrCompSub-apply sigma a zero = refl
subQtrCompSub-apply sigma a (suc n) =
  sym (oneLiftCancelTm (subTm sigma a) (applySubst sigma n))
  ∙ cong
      (subTm (qtrCompSub (subTm sigma a)))
      (sym (liftSubst-apply-suc sigma n))
  ∙ sym
      (applySubst-compSub
        (qtrCompSub (subTm sigma a))
        (liftSubst sigma)
        (suc n))

subQtrCompSubTm : (sigma : Subst) (a l : RawTerm)
  -> subTm sigma (subTm (qtrCompSub a) l)
       ≡ subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l)
subQtrCompSubTm sigma a l =
  subTmComp sigma (qtrCompSub a) l
  ∙ subTmEq (subQtrCompSub-apply sigma a) l
  ∙ sym
      (subTmComp
        (qtrCompSub (subTm sigma a))
        (liftSubst sigma)
        l)

subQtrCohLeftTm : (sigma : Subst) (l : RawTerm)
  -> subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l)
       ≡ wkTmBy 1 (subTm (liftSubst sigma) l)
subQtrCohLeftTm sigma l =
  wkTmLiftSubst (liftSubst sigma) l

qtrSecondBranchSubLiftTail : (sigma : Subst)
  -> renSub qtrSecondBranchRen (renSub sucRen sigma)
       ≡ dropSubstBy 2 (liftSubst (liftSubst sigma))
qtrSecondBranchSubLiftTail (shiftSub zero) = refl
qtrSecondBranchSubLiftTail (shiftSub (suc k)) = refl
qtrSecondBranchSubLiftTail (consSub t sigma) =
  cong₂ consSubst
    (renTmComp qtrSecondBranchRen sucRen t ∙ sym (renTmComp sucRen sucRen t))
    (qtrSecondBranchSubLiftTail sigma)

qtrSecondBranchSubLiftComp : (sigma : Subst)
  -> compSubRen (liftSubst (liftSubst sigma)) qtrSecondBranchRen
       ≡ renSub qtrSecondBranchRen (liftSubst sigma)
qtrSecondBranchSubLiftComp sigma =
  cong (consSubst (var zero)) (sym (qtrSecondBranchSubLiftTail sigma))

subQtrCohRightTm : (sigma : Subst) (l : RawTerm)
  -> subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l)
       ≡ renTm qtrSecondBranchRen (subTm (liftSubst sigma) l)
subQtrCohRightTm sigma l =
  subTmRen (liftSubst (liftSubst sigma)) qtrSecondBranchRen l
  ∙ cong
      (λ theta -> subTm theta l)
      (qtrSecondBranchSubLiftComp sigma)
  ∙ sym (renTmSub qtrSecondBranchRen (liftSubst sigma) l)

wkQtrBranchIsCoh : (L : RawType) -> wkTyBy 1 (qtrBranchTy L) ≡ qtrCohTy L
wkQtrBranchIsCoh L =
  renTySub sucRen qtrBranchSub L

minSubstQtrCoherence :
  {target : Ctx} {sigma : Subst} {A L : RawType} {l : RawTerm}
  -> Minimal
       (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
         (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
         (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
         (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
  -> Minimal
       (termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ target)
         (wkTmBy 1 (subTm (liftSubst sigma) l))
         (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
         (qtrCohTy (subTy (liftSubst sigma) L)))
minSubstQtrCoherence {target = target} {sigma = sigma} {A = A} {L = L} {l = l} cohSub =
  subst
    (λ H -> Minimal
      (termEq (H ∷ subTy sigma A ∷ target)
        (wkTmBy 1 (subTm (liftSubst sigma) l))
        (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
        (qtrCohTy (subTy (liftSubst sigma) L))))
    (wkTyLiftSubst sigma A)
    cohTermTy
  where
  cohLeft : Minimal
    (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
      (wkTmBy 1 (subTm (liftSubst sigma) l))
      (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
      (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
  cohLeft =
    subst
      (λ t -> Minimal
        (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
          t
          (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
          (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L))))
      (subQtrCohLeftTm sigma l)
      cohSub

  cohRight : Minimal
    (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
      (wkTmBy 1 (subTm (liftSubst sigma) l))
      (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
      (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
  cohRight =
    subst
      (λ t -> Minimal
        (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
          (wkTmBy 1 (subTm (liftSubst sigma) l))
          t
          (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L))))
      (subQtrCohRightTm sigma l)
      cohLeft

  cohTermTy : Minimal
    (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
      (wkTmBy 1 (subTm (liftSubst sigma) l))
      (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
      (qtrCohTy (subTy (liftSubst sigma) L)))
  cohTermTy =
    subst
      (λ T -> Minimal
        (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
          (wkTmBy 1 (subTm (liftSubst sigma) l))
          (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
          T))
      (subQtrCohTy sigma L)
      cohRight

mutual
  minSubst : {J : JForm} {target : Ctx} {sigma : Subst}
    -> Minimal J
    -> MinFitsSubst target (ctxOf J) sigma
    -> Minimal (subJTo target sigma J)
  minSubst (minVarStar {delta = delta} wf dA) fits =
    minFitsLookup delta fits
  minSubst (minReflTy d) fits =
    minReflTy (minSubst d fits)
  minSubst (minReflTm d) fits =
    minReflTm (minSubst d fits)
  minSubst (minSymTy d dB) fits =
    minSymTy (minSubst d fits) (minSubst dB fits)
  minSubst (minSymTm d du dA) fits =
    minSymTm (minSubst d fits) (minSubst du fits) (minSubst dA fits)
  minSubst (minTransTy d e) fits =
    minTransTy (minSubst d fits) (minSubst e fits)
  minSubst (minTransTm d e) fits =
    minTransTm (minSubst d fits) (minSubst e fits)
  minSubst (minConv d dAB) fits =
    minConv (minSubst d fits) (minSubst dAB fits)
  minSubst (minConvEq d dAB) fits =
    minConvEq (minSubst d fits) (minSubst dAB fits)
  minSubst (minFTop wf) fits =
    minFTop (minFitsSubstCtxWF fits)
  minSubst (minITop wf) fits =
    minITop (minFitsSubstCtxWF fits)
  minSubst (minCTop d) fits =
    minCTop (minSubst d fits)
  minSubst (minFSigma dA dB) fits =
    minFSigma dA' dB'
    where
    dA' = minSubst dA fits
    dB' = minSubst dB (liftMinFits fits dA')
  minSubst (minFSigmaEq dAC dB dBD dRight) fits =
    minFSigmaEq dAC' dB' dBD' dRight'
    where
    dAC' = minSubst dAC fits
    dA' = minSubstTyEqLeft dAC fits
    dB' = minSubst dB (liftMinFits fits dA')
    dBD' = minSubst dBD (liftMinFits fits dA')
    dRight' = minSubst dRight fits
  minSubst {sigma = sigma}
    (minISigma {a = a} {B = B} da db dSigma) fits =
    minISigma da' db' dSigma'
    where
    da' = minSubst da fits
    dbSub = minSubst db fits
    db' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subSingleSubstTy sigma a B)
        dbSub
    dSigma' = minSubst dSigma fits
  minSubst {sigma = sigma}
    (minISigmaEq {a = a} {B = B} dac dbd dA dB) fits =
    minISigmaEq dac' dbd' dA' dB'
    where
    dac' = minSubst dac fits
    dbdSub = minSubst dbd fits
    dbd' =
      subst
        (λ T -> Minimal (termEq _ _ _ T))
        (subSingleSubstTy sigma a B)
        dbdSub
    dA' = minSubst dA fits
    dB' = minSubst dB (liftMinFits fits dA')
  minSubst {target = target} {sigma = sigma}
    (minESigma {A = A} {B = B} {M = M} {d = d} {m = m}
      dM dd dSigma dm dTy) fits =
    subst
      (λ T -> Minimal
        (hasTy target
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          T))
      (sym (subSingleSubstTy sigma d M))
      (minESigma dM' dd' dSigma' dm' dTy')
    where
    dd' = minSubst dd fits
    dSigma' = minSubst dSigma fits
    dA' = minSigmaLeft dSigma'
    dB' = minSigmaRight dSigma'
    dM' = minSubst dM (liftMinFits fits dSigma')
    dmSub = minSubst dm (liftMinFits (liftMinFits fits dA') dB')
    dm' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subSigmaBranchTy sigma M)
        dmSub
    dTySub = minSubst dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (subSingleSubstTy sigma d M)
        dTySub
  minSubst {target = target} {sigma = sigma}
    (minESigmaEq {A = A} {B = B} {M = M} {d = d} {d' = d2} {m = m} {m' = m2}
      dM dd dSigma dm dmm dTy) fits =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm sigma d2) (subTm (liftSubst (liftSubst sigma)) m2))
          T))
      (sym (subSingleSubstTy sigma d M))
      (minESigmaEq dM' dd' dSigma' dm' dmm' dTy')
    where
    dd' = minSubst dd fits
    dSigma' = minSubst dSigma fits
    dA' = minSigmaLeft dSigma'
    dB' = minSigmaRight dSigma'
    dM' = minSubst dM (liftMinFits fits dSigma')
    dmSub = minSubst dm (liftMinFits (liftMinFits fits dA') dB')
    dm' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subSigmaBranchTy sigma M)
        dmSub
    dmmSub = minSubst dmm (liftMinFits (liftMinFits fits dA') dB')
    dmm' =
      subst
        (λ T -> Minimal (termEq _ _ _ T))
        (subSigmaBranchTy sigma M)
        dmmSub
    dTySub = minSubst dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (subSingleSubstTy sigma d M)
        dTySub
  minSubst {target = target} {sigma = sigma}
    (minCSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m}
      dM dSigma db dc dm dTy) fits =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c)) (subTm (liftSubst (liftSubst sigma)) m))
          (subTm sigma (subTm (sigmaCompSub b c) m))
          T))
      (sym (subSingleSubstTy sigma (tmPair b c) M))
      (subst
        (λ u -> Minimal
          (termEq target
            (tmElSigma (tmPair (subTm sigma b) (subTm sigma c)) (subTm (liftSubst (liftSubst sigma)) m))
            u
            (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c))) (subTy (liftSubst sigma) M))))
        (sym (subSigmaCompSubTm sigma b c m))
        (minCSigma dM' dSigma' db' dc' dm' dTy'))
    where
    dSigma' = minSubst dSigma fits
    dA' = minSigmaLeft dSigma'
    dB' = minSigmaRight dSigma'
    dM' = minSubst dM (liftMinFits fits dSigma')
    db' = minSubst db fits
    dcSub = minSubst dc fits
    dc' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subSingleSubstTy sigma b B)
        dcSub
    dmSub = minSubst dm (liftMinFits (liftMinFits fits dA') dB')
    dm' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subSigmaBranchTy sigma M)
        dmSub
    dTySub = minSubst dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (subSingleSubstTy sigma (tmPair b c) M)
        dTySub
  minSubst (minFEq dA da db) fits =
    minFEq (minSubst dA fits) (minSubst da fits) (minSubst db fits)
  minSubst (minFEqEq dAC dac dbd dRight) fits =
    minFEqEq (minSubst dAC fits) (minSubst dac fits) (minSubst dbd fits) (minSubst dRight fits)
  minSubst (minIEq da) fits =
    minIEq (minSubst da fits)
  minSubst (minIEqEq d) fits =
    minIEqEq (minSubst d fits)
  minSubst (minEEqStar dp dA da db) fits =
    minEEqStar (minSubst dp fits) (minSubst dA fits) (minSubst da fits) (minSubst db fits)
  minSubst (minCEq dp dA da db) fits =
    minCEq (minSubst dp fits) (minSubst dA fits) (minSubst da fits) (minSubst db fits)
  minSubst (minFQtr dA) fits =
    minFQtr (minSubst dA fits)
  minSubst (minFQtrEq dAB) fits =
    minFQtrEq (minSubst dAB fits)
  minSubst (minIQtr da) fits =
    minIQtr (minSubst da fits)
  minSubst (minIQtrEq da db) fits =
    minIQtrEq (minSubst da fits) (minSubst db fits)
  minSubst {target = target} {sigma = sigma}
    (minEQtr {A = A} {L = L} {l = l} {p = p} dL dp dA dBranchTy dl dWkA coh dTy) fits =
    subst
      (λ T -> Minimal
        (hasTy target (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p)) T))
      (sym (subSingleSubstTy sigma p L))
      (minEQtr dL' dp' dA' dBranchTy' dl' dWkA' coh' dTy')
    where
    dp' = minSubst dp fits
    dA' = minSubst dA fits
    dQtr' = minFQtr dA'
    fitsA = liftMinFits fits dA'
    dL' = minSubst dL (liftMinFits fits dQtr')
    dBranchTySub = minSubst dBranchTy fitsA
    dBranchTy' =
      subst
        (λ T -> Minimal (isType (subTy sigma A ∷ target) T))
        (subQtrBranchTy sigma L)
        dBranchTySub
    dlSub = minSubst dl fitsA
    dl' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subQtrBranchTy sigma L)
        dlSub
    dWkASub = minSubst dWkA fitsA
    dWkA' =
      subst
        (λ T -> Minimal (isType (subTy sigma A ∷ target) T))
        (wkTyLiftSubst sigma A)
        dWkASub
    fitsCoh = liftMinFits fitsA dWkASub
    coh' =
      minSubstQtrCoherence {target = target} {sigma = sigma} {A = A} {L = L} {l = l}
        (minSubst coh fitsCoh)
    dTySub = minSubst dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (subSingleSubstTy sigma p L)
        dTySub
  minSubst {target = target} {sigma = sigma}
    (minEQtrEq {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p2}
      dL dp dA dBranchTy dl dl' dll' dWkA coh coh' dTy) fits =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst sigma) l') (subTm sigma p2))
          T))
      (sym (subSingleSubstTy sigma p L))
      (minEQtrEq dL' dp' dA' dBranchTy' dlL' dlR' dll'' dWkA' cohL' cohR' dTy')
    where
    dp' = minSubst dp fits
    dA' = minSubst dA fits
    dQtr' = minFQtr dA'
    fitsA = liftMinFits fits dA'
    dL' = minSubst dL (liftMinFits fits dQtr')
    dBranchTySub = minSubst dBranchTy fitsA
    dBranchTy' =
      subst
        (λ T -> Minimal (isType (subTy sigma A ∷ target) T))
        (subQtrBranchTy sigma L)
        dBranchTySub
    dlLSub = minSubst dl fitsA
    dlL' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subQtrBranchTy sigma L)
        dlLSub
    dlRSub = minSubst dl' fitsA
    dlR' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subQtrBranchTy sigma L)
        dlRSub
    dllSub = minSubst dll' fitsA
    dll'' =
      subst
        (λ T -> Minimal (termEq _ _ _ T))
        (subQtrBranchTy sigma L)
        dllSub
    dWkASub = minSubst dWkA fitsA
    dWkA' =
      subst
        (λ T -> Minimal (isType (subTy sigma A ∷ target) T))
        (wkTyLiftSubst sigma A)
        dWkASub
    fitsCoh = liftMinFits fitsA dWkASub
    cohL' =
      minSubstQtrCoherence {target = target} {sigma = sigma} {A = A} {L = L} {l = l}
        (minSubst coh fitsCoh)
    cohR' =
      minSubstQtrCoherence {target = target} {sigma = sigma} {A = A} {L = L} {l = l'}
        (minSubst coh' fitsCoh)
    dTySub = minSubst dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (subSingleSubstTy sigma p L)
        dTySub
  minSubst {target = target} {sigma = sigma}
    (minCQtr {A = A} {L = L} {a = a} {l = l} dL da dA dBranchTy dl dWkA coh dTy) fits =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElQtr (subTm (liftSubst sigma) l) (tmClass (subTm sigma a)))
          (subTm sigma (subTm (qtrCompSub a) l))
          T))
      (sym (subSingleSubstTy sigma (tmClass a) L))
      (subst
        (λ u -> Minimal
          (termEq target
            (tmElQtr (subTm (liftSubst sigma) l) (tmClass (subTm sigma a)))
            u
            (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L))))
        (sym (subQtrCompSubTm sigma a l))
        (minCQtr dL' da' dA' dBranchTy' dl' dWkA' coh' dTy'))
    where
    da' = minSubst da fits
    dA' = minSubst dA fits
    fitsA = liftMinFits fits dA'
    dL' = minSubst dL (liftMinFits fits (minFQtr dA'))
    dBranchTySub = minSubst dBranchTy fitsA
    dBranchTy' =
      subst
        (λ T -> Minimal (isType (subTy sigma A ∷ target) T))
        (subQtrBranchTy sigma L)
        dBranchTySub
    dlSub = minSubst dl fitsA
    dl' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subQtrBranchTy sigma L)
        dlSub
    dWkASub = minSubst dWkA fitsA
    dWkA' =
      subst
        (λ T -> Minimal (isType (subTy sigma A ∷ target) T))
        (wkTyLiftSubst sigma A)
        dWkASub
    fitsCoh = liftMinFits fitsA dWkASub
    coh' =
      minSubstQtrCoherence {target = target} {sigma = sigma} {A = A} {L = L} {l = l}
        (minSubst coh fitsCoh)
    dTySub = minSubst dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (subSingleSubstTy sigma (tmClass a) L)
        dTySub

  minSubstTmTy : {gamma target : Ctx} {sigma : Subst} {t : RawTerm} {A : RawType}
    -> Minimal (hasTy gamma t A)
    -> MinFitsSubst target gamma sigma
    -> Minimal (isType target (subTy sigma A))
  minSubstTmTy (minVarStar {delta = delta} wf dA) fits =
    minSelfTmTy (minFitsLookup delta fits)
  minSubstTmTy (minConv d dAB) fits =
    minSubstTyEqRight dAB fits
  minSubstTmTy (minITop wf) fits =
    minFTop (minFitsSubstCtxWF fits)
  minSubstTmTy (minISigma da db dSigma) fits =
    minSubst dSigma fits
  minSubstTmTy (minESigma _ _ _ _ dTy) fits =
    minSubst dTy fits
  minSubstTmTy (minIEq da) fits =
    minFEq (minSubstTmTy da fits) (minSubst da fits) (minSubst da fits)
  minSubstTmTy (minIQtr da) fits =
    minFQtr (minSubstTmTy da fits)
  minSubstTmTy (minEQtr _ _ _ _ _ _ _ dTy) fits =
    minSubst dTy fits

  minSubstTyEqLeft : {gamma target : Ctx} {sigma : Subst} {A B : RawType}
    -> Minimal (typeEq gamma A B)
    -> MinFitsSubst target gamma sigma
    -> Minimal (isType target (subTy sigma A))
  minSubstTyEqLeft (minReflTy d) fits =
    minSubst d fits
  minSubstTyEqLeft (minSymTy _ dB) fits =
    minSubst dB fits
  minSubstTyEqLeft (minTransTy d _) fits =
    minSubstTyEqLeft d fits
  minSubstTyEqLeft (minFSigmaEq dAC dB _ _) fits =
    minFSigma dA' dB'
    where
    dA' = minSubstTyEqLeft dAC fits
    dB' = minSubst dB (liftMinFits fits dA')
  minSubstTyEqLeft (minFEqEq dAC dac dbd _) fits =
    minFEq (minSubstTyEqLeft dAC fits)
      (minAssocTmLeft (minSubst dac fits))
      (minAssocTmLeft (minSubst dbd fits))
  minSubstTyEqLeft (minFQtrEq d) fits =
    minFQtr (minSubstTyEqLeft d fits)

  minSubstTyEqRight : {gamma target : Ctx} {sigma : Subst} {A B : RawType}
    -> Minimal (typeEq gamma A B)
    -> MinFitsSubst target gamma sigma
    -> Minimal (isType target (subTy sigma B))
  minSubstTyEqRight (minReflTy d) fits =
    minSubst d fits
  minSubstTyEqRight (minSymTy d _) fits =
    minSubstTyEqLeft d fits
  minSubstTyEqRight (minTransTy _ d) fits =
    minSubstTyEqRight d fits
  minSubstTyEqRight (minFSigmaEq _ _ _ dRight) fits =
    minSubst dRight fits
  minSubstTyEqRight (minFEqEq _ _ _ dRight) fits =
    minSubst dRight fits
  minSubstTyEqRight (minFQtrEq d) fits =
    minFQtr (minSubstTyEqRight d fits)
