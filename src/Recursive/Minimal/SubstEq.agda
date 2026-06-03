{-# OPTIONS --safe #-}

module Recursive.Minimal.SubstEq where

open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to length++)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.Properties using (+-suc) renaming (+-identityʳ to +-zero)

open import Recursive.Prelude
open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Evaluation
open import Recursive.Derivability
open import Recursive.Presupposition using
  ( keepSubstCtx ; keepSubstCtx-subTy ; singleSubstCtx ; singleSubstCtx-subTy
  ; singleSubstCtx-subTm ; singleSubstCtx-apply
  ; sigmaCompSubCtx ; sigmaCompSubCtx-subTy ; sigmaCompSubCtx-subTm
  ; headSubstCtx ; headSubstCtx-subTy )

open import Recursive.Minimal.Base public

open import Recursive.Minimal.Renaming public

open import Recursive.Minimal.Substitution public using
  ( minSubst ; minSubstTmTy ; minSubstTyEqLeft ; minSubstTyEqRight )
open import Recursive.Minimal.Substitution using
  ( minSelfTmTy ; subSigmaCompSubTm ; subQtrCompSubTm
  ; subQtrCohLeftTm ; subQtrCohRightTm ; wkQtrBranchIsCoh
  ; minSubstQtrCoherence )
subJEqTo : Ctx -> Subst -> Subst -> JForm -> JForm
subJEqTo gamma sigma tau (isType _ A) =
  typeEq gamma (subTy sigma A) (subTy tau A)
subJEqTo gamma sigma tau (typeEq _ A B) =
  typeEq gamma (subTy sigma A) (subTy tau B)
subJEqTo gamma sigma tau (hasTy _ t A) =
  termEq gamma (subTm sigma t) (subTm tau t) (subTy sigma A)
subJEqTo gamma sigma tau (termEq _ t u A) =
  termEq gamma (subTm sigma t) (subTm tau u) (subTy sigma A)

minFitsEqLeft : {gamma delta : Ctx} {sigma tau : Subst}
  -> MinFitsEqSubst gamma delta sigma tau
  -> MinFitsSubst gamma delta sigma
minFitsEqLeft (minFitsEqNil wf) =
  minFitsNil wf
minFitsEqLeft (minFitsEqCons fits dtu _ _) =
  minFitsCons (minFitsEqLeft fits) (minAssocTmLeft dtu)

minFitsEqRight : {gamma delta : Ctx} {sigma tau : Subst}
  -> MinFitsEqSubst gamma delta sigma tau
  -> MinFitsSubst gamma delta tau
minFitsEqRight (minFitsEqNil wf) =
  minFitsNil wf
minFitsEqRight (minFitsEqCons fits _ dRight _) =
  minFitsCons (minFitsEqRight fits) dRight

minFitsEqRefl : {gamma delta : Ctx} {sigma : Subst}
  -> MinFitsSubst gamma delta sigma
  -> MinFitsEqSubst gamma delta sigma sigma
minFitsEqRefl (minFitsNil wf) =
  minFitsEqNil wf
minFitsEqRefl (minFitsCons fits dt) =
  minFitsEqCons (minFitsEqRefl fits) (minReflTm dt) dt dt

minFitsEqLookupPrefix : (delta : Ctx)
  -> {target gamma : Ctx} {sigma tau : Subst} {A : RawType}
  -> MinFitsEqSubst target (delta ++ (A ∷ gamma)) sigma tau
  -> Minimal
       (termEq target
         (applySubst sigma (length delta))
         (applySubst tau (length delta))
         (subTy sigma (wkTyBy (suc (length delta)) A)))
minFitsEqLookupPrefix [] (minFitsEqCons {sigma = sigma} {t = t} _ dtu _ _) =
  subst
    (λ T -> Minimal (termEq _ _ _ T))
    (sym (subTyConsWk1 sigma t _))
    dtu
minFitsEqLookupPrefix (B ∷ delta) (minFitsEqCons {sigma = sigma} {t = t} fits _ _ _) =
  subst
    (λ T -> Minimal (termEq _ _ _ T))
    (sym (subTyConsWkSuc sigma t (suc (length delta)) _))
    (minFitsEqLookupPrefix delta fits)

minFitsEqLookupRightPrefix : (delta : Ctx)
  -> {target gamma : Ctx} {sigma tau : Subst} {A : RawType}
  -> MinFitsEqSubst target (delta ++ (A ∷ gamma)) sigma tau
  -> Minimal
       (hasTy target
         (applySubst tau (length delta))
         (subTy sigma (wkTyBy (suc (length delta)) A)))
minFitsEqLookupRightPrefix [] (minFitsEqCons {sigma = sigma} {t = t} _ _ _ dRightS) =
  subst
    (λ T -> Minimal (hasTy _ _ T))
    (sym (subTyConsWk1 sigma t _))
    dRightS
minFitsEqLookupRightPrefix (B ∷ delta) (minFitsEqCons {sigma = sigma} {t = t} fits _ _ _) =
  subst
    (λ T -> Minimal (hasTy _ _ T))
    (sym (subTyConsWkSuc sigma t (suc (length delta)) _))
    (minFitsEqLookupRightPrefix delta fits)

-- Equality-substitution admissibility (Borsetto §5.3.1 eqSub*Rule / Valentini 3.9.1),
-- split by judgement shape with σ on the left endpoint and τ on the right:
--   minSubstEqTy    isType A   -> typeEq (subTy σ A) (subTy τ A)
--   minSubstEqTyEq  typeEq A B -> typeEq (subTy σ A) (subTy τ B)
--   minSubstEqTm    hasTy t A  -> termEq (subTm σ t) (subTm τ t) (subTy σ A)
--   minSubstEqTmEq  termEq t u A -> termEq (subTm σ t) (subTm τ u) (subTy σ A)
--   minSubstEqTmRight hasTy t A -> hasTy  (subTm τ t) (subTy σ A)  (right endpoint at the σ-type)
-- The heavy intro/computation coherence cases are offloaded to the `asm…` assemblers
-- (asm = "assembler for the constructor named in the suffix"): each deep-matches the stored
-- type-formation subderivation to expose the components for the (double) liftMinFitsEq, then
-- rebuilds the goal type with `subst` along the substitution-coherence lemmas.
-- TERMINATION: the five mutual functions recurse only on syntactic SUBTERMS; minSubst,
-- minSubstQtrCoherence, liftMinFits(Eq) are total/external and may be applied to anything.
mutual
  minSubstEqTy : {delta target : Ctx} {sigma tau : Subst} {A : RawType}
    -> Minimal (isType delta A)
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (typeEq target (subTy sigma A) (subTy tau A))
  minSubstEqTy (minFTop wf) f =
    minReflTy (minFTop (minFitsEqSubstCtxWF f))
  minSubstEqTy (minFSigma dA dB) f =
    minFSigmaEq eqA isBσ eqB isSigmaτ
    where
    fL = minFitsEqLeft f
    dAσ = minSubst dA fL
    eqA = minSubstEqTy dA f
    isBσ = minSubst dB (liftMinFits fL dAσ)
    eqB = minSubstEqTy dB (liftMinFitsEq f dAσ eqA)
    isSigmaτ = minSubst (minFSigma dA dB) (minFitsEqRight f)
  minSubstEqTy (minFEq dA da db) f =
    minFEqEq (minSubstEqTy dA f) (minSubstEqTm da f) (minSubstEqTm db f)
      (minSubst (minFEq dA da db) (minFitsEqRight f))
  minSubstEqTy (minFQtr dA) f =
    minFQtrEq (minSubstEqTy dA f)

  minSubstEqTm : {delta target : Ctx} {sigma tau : Subst} {t : RawTerm} {A : RawType}
    -> Minimal (hasTy delta t A)
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (termEq target (subTm sigma t) (subTm tau t) (subTy sigma A))
  minSubstEqTm (minVarStar {delta = delta} wf dA) f =
    minFitsEqLookupPrefix delta f
  minSubstEqTm (minConv d dAB) f =
    minConvEq (minSubstEqTm d f) (minSubst dAB (minFitsEqLeft f))
  minSubstEqTm (minITop wf) f =
    minReflTm (minITop (minFitsEqSubstCtxWF f))
  minSubstEqTm {sigma = sigma} (minISigma {a = a} {B = B} da db dSigma) f =
    minISigmaEq eqa eqb isA isB
    where
    fL = minFitsEqLeft f
    eqa = minSubstEqTm da f
    eqbSub = minSubstEqTm db f
    eqb = subst (λ T -> Minimal (termEq _ _ _ T)) (subSingleSubstTy sigma a B) eqbSub
    isA = minSubst (minSigmaLeft dSigma) fL
    isB = minSubst (minSigmaRight dSigma) (liftMinFits fL isA)
  minSubstEqTm (minESigma dM dd dSigma dm dTy) f =
    asmESigmaTm dM dd dSigma dm dTy f
  minSubstEqTm (minIEq da) f =
    minIEqEq (minSubstEqTm da f)
  minSubstEqTm (minIQtr da) f =
    minIQtrEq (minSubst da (minFitsEqLeft f)) (minSubstEqTmRight da f)
  minSubstEqTm (minEQtr dL dp dA dBranchTy dl dWkA coh dTy) f =
    asmEQtrTm dL dp dA dBranchTy dl dWkA coh dTy f

  minSubstEqTmRight : {delta target : Ctx} {sigma tau : Subst} {t : RawTerm} {A : RawType}
    -> Minimal (hasTy delta t A)
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (hasTy target (subTm tau t) (subTy sigma A))
  minSubstEqTmRight (minVarStar {delta = delta} wf dA) f =
    minFitsEqLookupRightPrefix delta f
  minSubstEqTmRight (minITop wf) f =
    minSubst (minITop wf) (minFitsEqLeft f)
  minSubstEqTmRight (minIEq da) f =
    minSubst (minIEq da) (minFitsEqLeft f)
  minSubstEqTmRight (minConv d dAB) f =
    minConv (minSubstEqTmRight d f) (minSubst dAB (minFitsEqLeft f))
  minSubstEqTmRight (minIQtr da) f =
    minIQtr (minSubstEqTmRight da f)
  minSubstEqTmRight (minISigma da db dSigma) f =
    minConv (minSubst (minISigma da db dSigma) (minFitsEqRight f))
      (minSymTy (minSubstEqTy dSigma f) (minSubst dSigma (minFitsEqRight f)))
  minSubstEqTmRight (minESigma dM dd dSigma dm dTy) f =
    minConv (minSubst (minESigma dM dd dSigma dm dTy) (minFitsEqRight f))
      (minSymTy (minSubstEqTy dTy f) (minSubst dTy (minFitsEqRight f)))
  minSubstEqTmRight (minEQtr dL dp dA dBranchTy dl dWkA coh dTy) f =
    minConv (minSubst (minEQtr dL dp dA dBranchTy dl dWkA coh dTy) (minFitsEqRight f))
      (minSymTy (minSubstEqTy dTy f) (minSubst dTy (minFitsEqRight f)))

  minSubstEqTyEq : {delta target : Ctx} {sigma tau : Subst} {A B : RawType}
    -> Minimal (typeEq delta A B)
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (typeEq target (subTy sigma A) (subTy tau B))
  minSubstEqTyEq (minReflTy d) f =
    minSubstEqTy d f
  minSubstEqTyEq (minSymTy d dB) f =
    minTransTy (minSubstEqTy dB f) (minSubst (minSymTy d dB) (minFitsEqRight f))
  minSubstEqTyEq (minTransTy d e) f =
    minTransTy (minSubstEqTyEq d f) (minSubst e (minFitsEqRight f))
  minSubstEqTyEq (minFSigmaEq dAC dB dBD dRight) f =
    minTransTy (minSubst (minFSigmaEq dAC dB dBD dRight) (minFitsEqLeft f))
      (minSubstEqTy dRight f)
  minSubstEqTyEq (minFEqEq dAC dac dbd dRight) f =
    minTransTy (minSubst (minFEqEq dAC dac dbd dRight) (minFitsEqLeft f))
      (minSubstEqTy dRight f)
  minSubstEqTyEq (minFQtrEq d) f =
    minFQtrEq (minSubstEqTyEq d f)

  minSubstEqTmEq : {delta target : Ctx} {sigma tau : Subst} {t u : RawTerm} {A : RawType}
    -> Minimal (termEq delta t u A)
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (termEq target (subTm sigma t) (subTm tau u) (subTy sigma A))
  minSubstEqTmEq (minReflTm d) f =
    minSubstEqTm d f
  minSubstEqTmEq (minSymTm d du dA) f =
    minTransTm (minSubstEqTm du f)
      (minConvEq (minSubst (minSymTm d du dA) (minFitsEqRight f))
                 (minSymTy (minSubstEqTy dA f) (minSubst dA (minFitsEqRight f))))
  minSubstEqTmEq (minTransTm d e) f =
    minTransTm (minSubst d (minFitsEqLeft f)) (minSubstEqTmEq e f)
  minSubstEqTmEq (minConvEq d dAB) f =
    minConvEq (minSubstEqTmEq d f) (minSubst dAB (minFitsEqLeft f))
  minSubstEqTmEq (minCTop d) f =
    minSubst (minCTop d) (minFitsEqLeft f)
  minSubstEqTmEq {sigma = sigma} (minISigmaEq {a = a} {B = B} dac dbd dA dB) f =
    minISigmaEq eqac eqbd isA isB
    where
    fL = minFitsEqLeft f
    eqac = minSubstEqTmEq dac f
    eqbdSub = minSubstEqTmEq dbd f
    eqbd = subst (λ T -> Minimal (termEq _ _ _ T)) (subSingleSubstTy sigma a B) eqbdSub
    isA = minSubst dA fL
    isB = minSubst dB (liftMinFits fL isA)
  minSubstEqTmEq (minESigmaEq dM dd dSigma dm dmm dTy) f =
    asmESigmaEqTmEq dM dd dSigma dm dmm dTy f
  minSubstEqTmEq (minCSigma dM dSigma db dc dm dTy) f =
    asmCSigmaTmEq dM dSigma db dc dm dTy f
  minSubstEqTmEq (minIEqEq d) f =
    minSubst (minIEqEq d) (minFitsEqLeft f)
  minSubstEqTmEq (minEEqStar dp dA da db) f =
    minTransTm (minSubst (minEEqStar dp dA da db) (minFitsEqLeft f))
      (minSubstEqTm db f)
  minSubstEqTmEq (minCEq dp dA da db) f =
    minSubst (minCEq dp dA da db) (minFitsEqLeft f)
  minSubstEqTmEq (minIQtrEq da db) f =
    minIQtrEq (minSubst da (minFitsEqLeft f)) (minSubstEqTmRight db f)
  minSubstEqTmEq (minEQtrEq dL dp dA dBranchTy dl dl' dll' dWkA coh coh' dTy) f =
    asmEQtrEqTmEq dL dp dA dBranchTy dl dl' dll' dWkA coh coh' dTy f
  minSubstEqTmEq (minCQtr dL da dA dBranchTy dl dWkA coh dTy) f =
    asmCQtrTmEq dL da dA dBranchTy dl dWkA coh dTy f

  asmESigmaTm : {delta target : Ctx} {sigma tau : Subst} {A B M : RawType} {d m : RawTerm}
    -> Minimal (isType (tySigma A B ∷ delta) M)
    -> Minimal (hasTy delta d (tySigma A B))
    -> Minimal (isType delta (tySigma A B))
    -> Minimal (hasTy (B ∷ A ∷ delta) m (sigmaBranchTy M))
    -> Minimal (isType delta (subTy (singleSubst d) M))
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (termEq target
         (subTm sigma (tmElSigma d m)) (subTm tau (tmElSigma d m))
         (subTy sigma (subTy (singleSubst d) M)))
  asmESigmaTm {target = target} {sigma = sigma} {tau = tau} {M = M} {d = d} {m = m}
    dM dd (minFSigma dA0 dB0) dm dTy f =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm tau d) (subTm (liftSubst (liftSubst tau)) m))
          T))
      (sym (subSingleSubstTy sigma d M))
      (minESigmaEq dM' dd' dSigma' dm' dmm' dTy')
    where
    fL = minFitsEqLeft f
    dSigma' = minSubst (minFSigma dA0 dB0) fL
    dA' = minSubst dA0 fL
    dAeq = minSubstEqTy dA0 f
    fA = liftMinFits fL dA'
    fAeq = liftMinFitsEq f dA' dAeq
    dB' = minSubst dB0 fA
    dBeq = minSubstEqTy dB0 fAeq
    dM' = minSubst dM (liftMinFits fL dSigma')
    dd' = minSubstEqTm dd f
    dmSub = minSubst dm (liftMinFits fA dB')
    dm' = subst (λ T -> Minimal (hasTy _ _ T)) (subSigmaBranchTy sigma M) dmSub
    dmmSub = minSubstEqTm dm (liftMinFitsEq fAeq dB' dBeq)
    dmm' = subst (λ T -> Minimal (termEq _ _ _ T)) (subSigmaBranchTy sigma M) dmmSub
    dTySub = minSubst dTy fL
    dTy' = subst (λ T -> Minimal (isType target T)) (subSingleSubstTy sigma d M) dTySub

  asmESigmaEqTmEq : {delta target : Ctx} {sigma tau : Subst}
    {A B M : RawType} {d d' m m' : RawTerm}
    -> Minimal (isType (tySigma A B ∷ delta) M)
    -> Minimal (termEq delta d d' (tySigma A B))
    -> Minimal (isType delta (tySigma A B))
    -> Minimal (hasTy (B ∷ A ∷ delta) m (sigmaBranchTy M))
    -> Minimal (termEq (B ∷ A ∷ delta) m m' (sigmaBranchTy M))
    -> Minimal (isType delta (subTy (singleSubst d) M))
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (termEq target
         (subTm sigma (tmElSigma d m)) (subTm tau (tmElSigma d' m'))
         (subTy sigma (subTy (singleSubst d) M)))
  asmESigmaEqTmEq {target = target} {sigma = sigma} {tau = tau} {M = M}
    {d = d} {d' = d'} {m = m} {m' = m'}
    dM dd (minFSigma dA0 dB0) dm dmm dTy f =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm tau d') (subTm (liftSubst (liftSubst tau)) m'))
          T))
      (sym (subSingleSubstTy sigma d M))
      (minESigmaEq dM' dd' dSigma' dm' dmm' dTy')
    where
    fL = minFitsEqLeft f
    dSigma' = minSubst (minFSigma dA0 dB0) fL
    dA' = minSubst dA0 fL
    dAeq = minSubstEqTy dA0 f
    fA = liftMinFits fL dA'
    fAeq = liftMinFitsEq f dA' dAeq
    dB' = minSubst dB0 fA
    dBeq = minSubstEqTy dB0 fAeq
    dM' = minSubst dM (liftMinFits fL dSigma')
    dd' = minSubstEqTmEq dd f
    dmSub = minSubst dm (liftMinFits fA dB')
    dm' = subst (λ T -> Minimal (hasTy _ _ T)) (subSigmaBranchTy sigma M) dmSub
    dmmSub = minSubstEqTmEq dmm (liftMinFitsEq fAeq dB' dBeq)
    dmm' = subst (λ T -> Minimal (termEq _ _ _ T)) (subSigmaBranchTy sigma M) dmmSub
    dTySub = minSubst dTy fL
    dTy' = subst (λ T -> Minimal (isType target T)) (subSingleSubstTy sigma d M) dTySub

  asmEQtrTm : {delta target : Ctx} {sigma tau : Subst} {A L : RawType} {l p : RawTerm}
    -> Minimal (isType (tyQtr A ∷ delta) L)
    -> Minimal (hasTy delta p (tyQtr A))
    -> Minimal (isType delta A)
    -> Minimal (isType (A ∷ delta) (qtrBranchTy L))
    -> Minimal (hasTy (A ∷ delta) l (qtrBranchTy L))
    -> Minimal (isType (A ∷ delta) (wkTyBy 1 A))
    -> Minimal (termEq (wkTyBy 1 A ∷ A ∷ delta)
         (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    -> Minimal (isType delta (subTy (singleSubst p) L))
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (termEq target
         (subTm sigma (tmElQtr l p)) (subTm tau (tmElQtr l p))
         (subTy sigma (subTy (singleSubst p) L)))
  asmEQtrTm {target = target} {sigma = sigma} {tau = tau} {A = A} {L = L} {l = l} {p = p}
    dL dp dA dBranchTy dl dWkA coh dTy f =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst tau) l) (subTm tau p))
          T))
      (sym (subSingleSubstTy sigma p L))
      (minEQtrEq dL' dp' dA' dBranchTy' dlL' dlR' dll'' dWkA' cohL' cohR' dTy')
    where
    fL = minFitsEqLeft f
    dA' = minSubst dA fL
    dAeq = minSubstEqTy dA f
    dQtr' = minFQtr dA'
    fitsA = liftMinFits fL dA'
    fAeq = liftMinFitsEq f dA' dAeq
    dL' = minSubst dL (liftMinFits fL dQtr')
    dp' = minSubstEqTm dp f
    dBranchTySub = minSubst dBranchTy fitsA
    dBranchTy' =
      subst (λ T -> Minimal (isType (subTy sigma A ∷ target) T))
        (subQtrBranchTy sigma L) dBranchTySub
    dlLSub = minSubst dl fitsA
    dlL' =
      subst (λ T -> Minimal (hasTy _ _ T)) (subQtrBranchTy sigma L) dlLSub
    dlRSub = minSubstEqTmRight dl fAeq
    dlR' =
      subst (λ T -> Minimal (hasTy _ _ T)) (subQtrBranchTy sigma L) dlRSub
    dllSub = minSubstEqTm dl fAeq
    dll'' =
      subst (λ T -> Minimal (termEq _ _ _ T)) (subQtrBranchTy sigma L) dllSub
    dWkASub = minSubst dWkA fitsA
    dWkA' =
      subst (λ T -> Minimal (isType (subTy sigma A ∷ target) T))
        (wkTyLiftSubst sigma A) dWkASub
    fitsCoh = liftMinFits fitsA dWkASub
    cohL' =
      minSubstQtrCoherence {target = target} {sigma = sigma} {A = A} {L = L} {l = l}
        (minSubst coh fitsCoh)
    dWkAeq = minSubstEqTy dWkA fAeq
    fitsCohEq = liftMinFitsEq fAeq dWkASub dWkAeq
    wfCoh : MinCtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ target)
    wfCoh = minWfCons (minWfCons (minFitsEqSubstCtxWF f) dA') dWkA'
    mixedRaw = minSubstEqTmEq coh fitsCohEq
    mixed =
      subst (λ H -> Minimal
              (termEq (H ∷ subTy sigma A ∷ target)
                (wkTmBy 1 (subTm (liftSubst sigma) l))
                (renTm qtrSecondBranchRen (subTm (liftSubst tau) l))
                (qtrCohTy (subTy (liftSubst sigma) L))))
            (wkTyLiftSubst sigma A)
        (subst (λ T -> Minimal
                 (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
                   (wkTmBy 1 (subTm (liftSubst sigma) l))
                   (renTm qtrSecondBranchRen (subTm (liftSubst tau) l))
                   T))
               (subQtrCohTy sigma L)
          (subst (λ u -> Minimal
                   (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
                     (wkTmBy 1 (subTm (liftSubst sigma) l))
                     u
                     (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (subQtrCohRightTm tau l)
            (subst (λ t0 -> Minimal
                     (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
                       t0
                       (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                       (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                   (subQtrCohLeftTm sigma l)
              mixedRaw)))
    dllSym = minSymTm dll'' dlR' dBranchTy'
    dllSymWk = minWeakenTmEq {delta = wkTyBy 1 (subTy sigma A) ∷ []} dllSym wfCoh
    cohP1 =
      subst (λ T -> Minimal
              (termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ target)
                (wkTmBy 1 (subTm (liftSubst tau) l))
                (wkTmBy 1 (subTm (liftSubst sigma) l))
                T))
            (wkQtrBranchIsCoh (subTy (liftSubst sigma) L))
            dllSymWk
    cohR' = minTransTm cohP1 mixed
    dTySub = minSubst dTy fL
    dTy' =
      subst (λ T -> Minimal (isType target T)) (subSingleSubstTy sigma p L) dTySub

  asmCSigmaTmEq : {delta target : Ctx} {sigma tau : Subst}
    {A B M : RawType} {b c m : RawTerm}
    -> Minimal (isType (tySigma A B ∷ delta) M)
    -> Minimal (isType delta (tySigma A B))
    -> Minimal (hasTy delta b A)
    -> Minimal (hasTy delta c (subTy (singleSubst b) B))
    -> Minimal (hasTy (B ∷ A ∷ delta) m (sigmaBranchTy M))
    -> Minimal (isType delta (subTy (singleSubst (tmPair b c)) M))
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (termEq target
         (subTm sigma (tmElSigma (tmPair b c) m))
         (subTm tau (subTm (sigmaCompSub b c) m))
         (subTy sigma (subTy (singleSubst (tmPair b c)) M)))
  asmCSigmaTmEq {target = target} {sigma = sigma} {tau = tau}
    {M = M} {b = b} {c = c} {m = m}
    dM dSigma db dc dm dTy f =
    minTransTm Eσ Erc
    where
    Eσ =
      minSubst (minCSigma dM dSigma db dc dm dTy) (minFitsEqLeft f)
    fitsA =
      minFitsEqCons f
        (minSubstEqTm db f)
        (minSubst db (minFitsEqRight f))
        (minSubstEqTmRight db f)
    eqcB =
      subst (λ T -> Minimal (termEq target (subTm sigma c) (subTm tau c) T))
        (subTyComp sigma (singleSubst b) _)
        (minSubstEqTm dc f)
    rightcB =
      subst (λ T -> Minimal (hasTy target (subTm tau c) T))
        (subTyComp tau (singleSubst b) _)
        (minSubst dc (minFitsEqRight f))
    rightScB =
      subst (λ T -> Minimal (hasTy target (subTm tau c) T))
        (subTyComp sigma (singleSubst b) _)
        (minSubstEqTmRight dc f)
    cf = minFitsEqCons fitsA eqcB rightcB rightScB
    ErcRaw = minSubstEqTm dm cf
    Erc =
      subst (λ T -> Minimal (termEq target _ _ T))
        ( sym (subTyComp sigma (sigmaCompSub b c) (sigmaBranchTy M))
          ∙ cong (subTy sigma) (sigmaBranchTyComp b c M) )
        (subst (λ u -> Minimal (termEq target _ u _))
          (sym (subTmComp tau (sigmaCompSub b c) m))
          (subst (λ s -> Minimal (termEq target s _ _))
            (sym (subTmComp sigma (sigmaCompSub b c) m))
            ErcRaw))

  asmEQtrEqTmEq : {delta target : Ctx} {sigma tau : Subst}
    {A L : RawType} {l l' p p' : RawTerm}
    -> Minimal (isType (tyQtr A ∷ delta) L)
    -> Minimal (termEq delta p p' (tyQtr A))
    -> Minimal (isType delta A)
    -> Minimal (isType (A ∷ delta) (qtrBranchTy L))
    -> Minimal (hasTy (A ∷ delta) l (qtrBranchTy L))
    -> Minimal (hasTy (A ∷ delta) l' (qtrBranchTy L))
    -> Minimal (termEq (A ∷ delta) l l' (qtrBranchTy L))
    -> Minimal (isType (A ∷ delta) (wkTyBy 1 A))
    -> Minimal (termEq (wkTyBy 1 A ∷ A ∷ delta)
         (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    -> Minimal (termEq (wkTyBy 1 A ∷ A ∷ delta)
         (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L))
    -> Minimal (isType delta (subTy (singleSubst p) L))
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (termEq target
         (subTm sigma (tmElQtr l p)) (subTm tau (tmElQtr l' p'))
         (subTy sigma (subTy (singleSubst p) L)))
  asmEQtrEqTmEq {target = target} {sigma = sigma} {tau = tau}
    {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
    dL dp dA dBranchTy dl dl' dll' dWkA coh coh' dTy f =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst tau) l') (subTm tau p'))
          T))
      (sym (subSingleSubstTy sigma p L))
      (minEQtrEq dL' dp' dA' dBranchTy' dlL' dlR' dll'' dWkA' cohL' cohR' dTy')
    where
    fL = minFitsEqLeft f
    dp' = minSubstEqTmEq dp f
    dA' = minSubst dA fL
    dAeq = minSubstEqTy dA f
    dQtr' = minFQtr dA'
    fitsA = liftMinFits fL dA'
    fAeq = liftMinFitsEq f dA' dAeq
    dL' = minSubst dL (liftMinFits fL dQtr')
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
    dlRSub = minSubstEqTmRight dl' fAeq
    dlR' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (subQtrBranchTy sigma L)
        dlRSub
    dllSub = minSubstEqTmEq dll' fAeq
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
    dWkAeq = minSubstEqTy dWkA fAeq
    fitsCohEq = liftMinFitsEq fAeq dWkASub dWkAeq
    wfCoh : MinCtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ target)
    wfCoh = minWfCons (minWfCons (minFitsEqSubstCtxWF f) dA') dWkA'
    mixedRaw = minSubstEqTmEq coh' fitsCohEq
    mixed =
      subst (λ H -> Minimal
              (termEq (H ∷ subTy sigma A ∷ target)
                (wkTmBy 1 (subTm (liftSubst sigma) l'))
                (renTm qtrSecondBranchRen (subTm (liftSubst tau) l'))
                (qtrCohTy (subTy (liftSubst sigma) L))))
            (wkTyLiftSubst sigma A)
        (subst (λ T -> Minimal
                 (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
                   (wkTmBy 1 (subTm (liftSubst sigma) l'))
                   (renTm qtrSecondBranchRen (subTm (liftSubst tau) l'))
                   T))
               (subQtrCohTy sigma L)
          (subst (λ u -> Minimal
                   (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
                     (wkTmBy 1 (subTm (liftSubst sigma) l'))
                     u
                     (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (subQtrCohRightTm tau l')
            (subst (λ t0 -> Minimal
                     (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ target)
                       t0
                       (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                       (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                   (subQtrCohLeftTm sigma l')
              mixedRaw)))
    dllSelfSub = minSubstEqTm dl' fAeq
    dllSelf =
      subst (λ T -> Minimal (termEq _ _ _ T)) (subQtrBranchTy sigma L) dllSelfSub
    dllSelfSym = minSymTm dllSelf dlR' dBranchTy'
    dllSelfSymWk = minWeakenTmEq {delta = wkTyBy 1 (subTy sigma A) ∷ []} dllSelfSym wfCoh
    cohP1 =
      subst (λ T -> Minimal
              (termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ target)
                (wkTmBy 1 (subTm (liftSubst tau) l'))
                (wkTmBy 1 (subTm (liftSubst sigma) l'))
                T))
            (wkQtrBranchIsCoh (subTy (liftSubst sigma) L))
            dllSelfSymWk
    cohR' = minTransTm cohP1 mixed
    dTySub = minSubst dTy fL
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (subSingleSubstTy sigma p L)
        dTySub

  asmCQtrTmEq : {delta target : Ctx} {sigma tau : Subst}
    {A L : RawType} {a l : RawTerm}
    -> Minimal (isType (tyQtr A ∷ delta) L)
    -> Minimal (hasTy delta a A)
    -> Minimal (isType delta A)
    -> Minimal (isType (A ∷ delta) (qtrBranchTy L))
    -> Minimal (hasTy (A ∷ delta) l (qtrBranchTy L))
    -> Minimal (isType (A ∷ delta) (wkTyBy 1 A))
    -> Minimal (termEq (wkTyBy 1 A ∷ A ∷ delta)
         (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    -> Minimal (isType delta (subTy (singleSubst (tmClass a)) L))
    -> MinFitsEqSubst target delta sigma tau
    -> Minimal (termEq target
         (subTm sigma (tmElQtr l (tmClass a)))
         (subTm tau (subTm (qtrCompSub a) l))
         (subTy sigma (subTy (singleSubst (tmClass a)) L)))
  asmCQtrTmEq {target = target} {sigma = sigma} {tau = tau}
    {A = A} {L = L} {a = a} {l = l}
    dL da dA dBranchTy dl dWkA coh dTy f =
    minTransTm Eσ Erc
    where
    Eσ = minSubst (minCQtr dL da dA dBranchTy dl dWkA coh dTy) (minFitsEqLeft f)
    daEq = minSubstEqTm da f
    daRight = minSubst da (minFitsEqRight f)
    daRightS = minSubstEqTmRight da f
    g = minFitsEqCons {t = subTm sigma a} {u = subTm tau a} f daEq daRight daRightS
    r0 = minSubstEqTm dl g
    lhsPath : subTm (consSubst (subTm sigma a) sigma) l
                ≡ subTm sigma (subTm (qtrCompSub a) l)
    lhsPath = sym (subTmComp sigma (qtrCompSub a) l)
    rhsPath : subTm (consSubst (subTm tau a) tau) l
                ≡ subTm tau (subTm (qtrCompSub a) l)
    rhsPath = sym (subTmComp tau (qtrCompSub a) l)
    typePath : subTy (consSubst (subTm sigma a) sigma) (qtrBranchTy L)
                 ≡ subTy sigma (subTy (singleSubst (tmClass a)) L)
    typePath =
      sym (subTyComp sigma (qtrCompSub a) (qtrBranchTy L))
      ∙ cong (subTy sigma) (qtrBranchTyComp a L)
    Erc =
      subst
        (λ T -> Minimal
          (termEq target
            (subTm sigma (subTm (qtrCompSub a) l))
            (subTm tau (subTm (qtrCompSub a) l))
            T))
        typePath
        (subst
          (λ v -> Minimal
            (termEq target
              (subTm sigma (subTm (qtrCompSub a) l))
              v
              (subTy (consSubst (subTm sigma a) sigma) (qtrBranchTy L))))
          rhsPath
          (subst
            (λ u -> Minimal
              (termEq target
                u
                (subTm (consSubst (subTm tau a) tau) l)
                (subTy (consSubst (subTm sigma a) sigma) (qtrBranchTy L))))
            lhsPath
            r0))

minSubstEq : {J : JForm} {target : Ctx} {sigma tau : Subst}
  -> Minimal J
  -> MinFitsEqSubst target (ctxOf J) sigma tau
  -> Minimal (subJEqTo target sigma tau J)
minSubstEq {J = isType _ _} d f = minSubstEqTy d f
minSubstEq {J = typeEq _ _ _} d f = minSubstEqTyEq d f
minSubstEq {J = hasTy _ _ _} d f = minSubstEqTm d f
minSubstEq {J = termEq _ _ _ _} d f = minSubstEqTmEq d f
