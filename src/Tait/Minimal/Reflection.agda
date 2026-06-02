{-# OPTIONS --safe #-}

module Tait.Minimal.Reflection where

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

open import Tait.Minimal.Substitution public using
  ( minSubst ; minSubstTmTy ; minSubstTyEqLeft ; minSubstTyEqRight )
open import Tait.Minimal.Substitution using
  ( minSelfTmTy ; subSigmaCompSubTm ; subQtrCompSubTm
  ; subQtrCohLeftTm ; subQtrCohRightTm ; wkQtrBranchIsCoh
  ; minSubstQtrCoherence )

open import Tait.Minimal.SubstEq public
minFitsKeepCtx : {delta gamma : Ctx}
  -> MinCtxWF (delta ++ gamma)
  -> MinFitsSubst (delta ++ gamma) gamma (keepSubstCtx (length delta) gamma)
minFitsKeepCtx {delta = delta} {gamma = []} wf =
  minFitsNil {sigma = keepSubstBy (length delta)} wf
minFitsKeepCtx {delta = delta} {gamma = A ∷ gamma} wf =
  minFitsCons liftedTail headVar
  where
  wfTail : MinCtxWF (((delta ++ (A ∷ [])) ++ gamma))
  wfTail = subst MinCtxWF (sym (++-assoc delta (A ∷ []) gamma)) wf

  tail0 : MinFitsSubst (((delta ++ (A ∷ [])) ++ gamma)) gamma
    (keepSubstCtx (length (delta ++ (A ∷ []))) gamma)
  tail0 = minFitsKeepCtx {delta = delta ++ (A ∷ [])} {gamma = gamma} wfTail

  tail1 : MinFitsSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstCtx (length (delta ++ (A ∷ []))) gamma)
  tail1 =
    subst
      (λ src -> MinFitsSubst src gamma (keepSubstCtx (length (delta ++ (A ∷ []))) gamma))
      (++-assoc delta (A ∷ []) gamma)
      tail0

  liftedTail : MinFitsSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstCtx (suc (length delta)) gamma)
  liftedTail =
    subst
      (λ k -> MinFitsSubst (delta ++ (A ∷ gamma)) gamma (keepSubstCtx k gamma))
      (lengthSnoc delta A)
      tail1

  headVar : Minimal
    (hasTy (delta ++ (A ∷ gamma)) (var (length delta))
      (subTy (keepSubstCtx (suc (length delta)) gamma) A))
  headVar =
    subst
      (λ T -> Minimal (hasTy (delta ++ (A ∷ gamma)) (var (length delta)) T))
      (renTyKeepSubstBy (suc (length delta)) A
        ∙ sym (keepSubstCtx-subTy (suc (length delta)) gamma A))
      (minVarStar wf (minCtxSuffixTy {delta = delta} {gamma = gamma} {A = A} wf))

minSingleFitsSubst : {gamma : Ctx} {A : RawType} {t : RawTerm}
  -> Minimal (hasTy gamma t A)
  -> MinFitsSubst gamma (A ∷ gamma) (singleSubstCtx t gamma)
minSingleFitsSubst {gamma = gamma} {A = A} {t = t} dt =
  minFitsCons
    (minFitsKeepCtx {delta = []} {gamma = gamma} (minDerivToCtxWF dt))
    (subst
      (λ T -> Minimal (hasTy gamma t T))
      (sym (keepSubstCtx-subTy 0 gamma A ∙ subTyId A))
      dt)

minSingleSubstTy : {gamma : Ctx} {A B : RawType} {t : RawTerm}
  -> Minimal (isType (A ∷ gamma) B)
  -> Minimal (hasTy gamma t A)
  -> Minimal (isType gamma (subTy (singleSubst t) B))
minSingleSubstTy {gamma = gamma} {B = B} {t = t} dB dt =
  subst
    (λ T -> Minimal (isType gamma T))
    (singleSubstCtx-subTy t gamma B)
    (minSubst dB (minSingleFitsSubst dt))

minSigmaCompFits : {gamma : Ctx} {A B : RawType} {b c : RawTerm}
  -> Minimal (hasTy gamma b A)
  -> Minimal (hasTy gamma c (subTy (singleSubst b) B))
  -> MinFitsSubst gamma (B ∷ A ∷ gamma) (sigmaCompSubCtx b c gamma)
minSigmaCompFits {gamma = gamma} {A = A} {B = B} {b = b} {c = c} db dc =
  minFitsCons firstStep cTyped
  where
  gammaWF : MinCtxWF gamma
  gammaWF = minDerivToCtxWF db

  base : MinFitsSubst gamma gamma (keepSubstCtx 0 gamma)
  base = minFitsKeepCtx {delta = []} {gamma = gamma} gammaWF

  bTyped : Minimal (hasTy gamma b (subTy (keepSubstCtx 0 gamma) A))
  bTyped =
    subst
      (λ T -> Minimal (hasTy gamma b T))
      (sym (keepSubstCtx-subTy 0 gamma A ∙ subTyId A))
      db

  firstStep : MinFitsSubst gamma (A ∷ gamma) (consSubst b (keepSubstCtx 0 gamma))
  firstStep = minFitsCons base bTyped

  cTyped : Minimal (hasTy gamma c (subTy (consSubst b (keepSubstCtx 0 gamma)) B))
  cTyped =
    subst
      (λ T -> Minimal (hasTy gamma c T))
      (sym (subTyEq (singleSubstCtx-apply b gamma) B))
      dc

minSigmaCompTy : {gamma : Ctx} {A B M : RawType} {b c : RawTerm}
  -> Minimal (isType ((tySigma A B) ∷ gamma) M)
  -> Minimal (hasTy gamma b A)
  -> Minimal (hasTy gamma c (subTy (singleSubst b) B))
  -> Minimal (isType gamma (subTy (singleSubst (tmPair b c)) M))
minSigmaCompTy {gamma = gamma} {M = M} {b = b} {c = c} dM db dc =
  subst
    (λ T -> Minimal (isType gamma T))
    (singleSubstCtx-subTy (tmPair b c) gamma M)
    (minSubst dM (minSingleFitsSubst pairTy))
  where
  sigmaTy : Minimal (isType gamma _)
  sigmaTy = minCtxSuffixTy {delta = []} (minDerivToCtxWF dM)

  pairTy : Minimal (hasTy gamma (tmPair b c) _)
  pairTy = minISigma db dc sigmaTy

minQtrCompTy : {gamma : Ctx} {A L : RawType} {a : RawTerm}
  -> Minimal (isType ((tyQtr A) ∷ gamma) L)
  -> Minimal (hasTy gamma a A)
  -> Minimal (isType gamma (subTy (singleSubst (tmClass a)) L))
minQtrCompTy {gamma = gamma} {L = L} {a = a} dL da =
  subst
    (λ T -> Minimal (isType gamma T))
    (singleSubstCtx-subTy (tmClass a) gamma L)
    (minSubst dL (minSingleFitsSubst (minIQtr da)))

minHeadTypeTransportFits : {gamma : Ctx} {A C : RawType}
  -> Minimal (typeEq gamma A C)
  -> Minimal (isType gamma C)
  -> MinFitsSubst (C ∷ gamma) (A ∷ gamma) (headSubstCtx gamma)
minHeadTypeTransportFits {gamma = gamma} {A = A} {C = C} dAC dC =
  minFitsCons tail headVarA
  where
  wfGamma : MinCtxWF gamma
  wfGamma = minDerivToCtxWF dC

  wfC : MinCtxWF (C ∷ gamma)
  wfC = minWfCons wfGamma dC

  tail : MinFitsSubst (C ∷ gamma) gamma (keepSubstCtx 1 gamma)
  tail = minFitsKeepCtx {delta = C ∷ []} {gamma = gamma} wfC

  headVarC : Minimal (hasTy (C ∷ gamma) (var zero) (wkTyBy 1 C))
  headVarC = minVarStar {delta = []} {A = C} wfC dC

  headVarA0 : Minimal (hasTy (C ∷ gamma) (var zero) (wkTyBy 1 A))
  headVarA0 =
    minConv headVarC
      (minSymTy
        (minWeakenTyEq {delta = C ∷ []} dAC wfC)
        (minWeakenTy dC wfC))

  headVarA : Minimal (hasTy (C ∷ gamma) (var zero) (subTy (keepSubstCtx 1 gamma) A))
  headVarA =
    subst
      (λ T -> Minimal (hasTy (C ∷ gamma) (var zero) T))
      (renTyKeepSubstBy 1 A ∙ sym (keepSubstCtx-subTy 1 gamma A))
      headVarA0

minTransportFamilyTy : {gamma : Ctx} {A C D : RawType}
  -> Minimal (typeEq gamma A C)
  -> Minimal (isType gamma C)
  -> Minimal (isType (A ∷ gamma) D)
  -> Minimal (isType (C ∷ gamma) D)
minTransportFamilyTy {gamma = gamma} {C = C} {D = D} dAC dC dD =
  subst
    (λ T -> Minimal (isType (C ∷ gamma) T))
    (subTyId D)
    (subst
      (λ T -> Minimal (isType (C ∷ gamma) T))
      (headSubstCtx-subTy gamma D)
      (minSubst dD (minHeadTypeTransportFits dAC dC)))

mutual
  minSingleFitsEqSubst : {gamma : Ctx} {A : RawType} {t u : RawTerm}
    -> Minimal (termEq gamma t u A)
    -> MinFitsEqSubst gamma (A ∷ gamma) (singleSubstCtx t gamma) (singleSubstCtx u gamma)
  minSingleFitsEqSubst {gamma = gamma} {A = A} {t = t} {u = u} dtu =
    minFitsEqCons
      (minFitsEqRefl (minFitsKeepCtx {delta = []} {gamma = gamma} (minDerivToCtxWF dtu)))
      dtuTyped
      duTyped
      duTyped
    where
    dtuTyped : Minimal (termEq gamma t u (subTy (keepSubstCtx 0 gamma) A))
    dtuTyped =
      subst
        (λ T -> Minimal (termEq gamma t u T))
        (sym (keepSubstCtx-subTy 0 gamma A ∙ subTyId A))
        dtu

    duTyped : Minimal (hasTy gamma u (subTy (keepSubstCtx 0 gamma) A))
    duTyped =
      subst
        (λ T -> Minimal (hasTy gamma u T))
        (sym (keepSubstCtx-subTy 0 gamma A ∙ subTyId A))
        (minAssocTmRight dtu)

  minSingleEqSubstTy : {gamma : Ctx} {A B : RawType} {t u : RawTerm}
    -> Minimal (isType (A ∷ gamma) B)
    -> Minimal (termEq gamma t u A)
    -> Minimal (typeEq gamma (subTy (singleSubst t) B) (subTy (singleSubst u) B))
  minSingleEqSubstTy {gamma = gamma} {B = B} {t = t} {u = u} dB dtu =
    subst
      (λ T -> Minimal (typeEq gamma T (subTy (singleSubst u) B)))
      (singleSubstCtx-subTy t gamma B)
      (subst
        (λ T -> Minimal (typeEq gamma (subTy (singleSubstCtx t gamma) B) T))
        (singleSubstCtx-subTy u gamma B)
        (minSubstEq dB (minSingleFitsEqSubst dtu)))

  minAssocTmRight : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Minimal (termEq gamma t u A)
    -> Minimal (hasTy gamma u A)
  minAssocTmRight (minReflTm d) = d
  minAssocTmRight (minSymTm d _ _) = minAssocTmLeft d
  minAssocTmRight (minTransTm _ d) = minAssocTmRight d
  minAssocTmRight (minConvEq d dAB) =
    minConv (minAssocTmRight d) dAB
  minAssocTmRight (minCTop d) =
    minITop (minDerivToCtxWF d)
  minAssocTmRight (minISigmaEq d1 d2 dA dB) =
    minISigma
      (minAssocTmRight d1)
      (minConv (minAssocTmRight d2) (minSingleEqSubstTy dB d1))
      (minFSigma dA dB)
  minAssocTmRight (minESigmaEq dM dd dSigma _ dmm _) =
    minConv
      (minESigma dM (minAssocTmRight dd) dSigma (minAssocTmRight dmm) dTyRight)
      (minSymTy (minSingleEqSubstTy dM dd) dTyRight)
    where
    dTyRight = minSingleSubstTy dM (minAssocTmRight dd)
  minAssocTmRight
    (minCSigma {gamma = gamma} {M = M} {b = b} {c = c} {m = m} dM _ db dc dm _) =
    subst
      (λ T -> Minimal (hasTy gamma (subTm (sigmaCompSub b c) m) T))
      (sigmaBranchTyComp b c M)
      (subst
        (λ T -> Minimal (hasTy gamma (subTm (sigmaCompSub b c) m) T))
        (sigmaCompSubCtx-subTy b c gamma (sigmaBranchTy M))
        (subst
          (λ u -> Minimal (hasTy gamma u (subTy (sigmaCompSubCtx b c gamma) (sigmaBranchTy M))))
          (sigmaCompSubCtx-subTm b c gamma m)
          (minSubst dm (minSigmaCompFits db dc))))
  minAssocTmRight (minIEqEq d) =
    minConv
      (minIEq (minAssocTmRight d))
      (minFEqEq
        (minReflTy (minAssocTmTy d))
        (minSymTm d (minAssocTmRight d) (minAssocTmTy d))
        (minSymTm d (minAssocTmRight d) (minAssocTmTy d))
        (minFEq (minAssocTmTy d) (minAssocTmLeft d) (minAssocTmLeft d)))
  minAssocTmRight (minEEqStar _ _ _ db) = db
  minAssocTmRight (minCEq p dA da db) =
    minConv
      (minIEq da)
      (minFEqEq
        (minReflTy dA)
        (minReflTm da)
        (minEEqStar p dA da db)
        (minFEq dA da db))
  minAssocTmRight (minIQtrEq _ db) =
    minIQtr db
  minAssocTmRight (minEQtrEq dL dp dA dBranch _ dlR _ dWkA _ coh' _) =
    minConv
      (minEQtr dL (minAssocTmRight dp) dA dBranch dlR dWkA coh' dTyRight)
      (minSymTy (minSingleEqSubstTy dL dp) dTyRight)
    where
    dTyRight = minSingleSubstTy dL (minAssocTmRight dp)
  minAssocTmRight
    (minCQtr {gamma = gamma} {L = L} {a = a} {l = l} _ da _ _ dl _ _ _) =
    subst
      (λ T -> Minimal (hasTy gamma (subTm (qtrCompSub a) l) T))
      (qtrBranchTyComp a L)
      (subst
        (λ T -> Minimal (hasTy gamma (subTm (qtrCompSub a) l) T))
        (singleSubstCtx-subTy a gamma (qtrBranchTy L))
        (subst
          (λ u -> Minimal (hasTy gamma u (subTy (singleSubstCtx a gamma) (qtrBranchTy L))))
          (singleSubstCtx-subTm a gamma l)
          (minSubst dl (minSingleFitsSubst da))))

  minAssocTmTy : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Minimal (termEq gamma t u A)
    -> Minimal (isType gamma A)
  minAssocTmTy (minReflTm d) = minSelfTmTy d
  minAssocTmTy (minSymTm _ _ dA) = dA
  minAssocTmTy (minTransTm d _) = minAssocTmTy d
  minAssocTmTy (minConvEq _ dAB) = minAssocTyRight dAB
  minAssocTmTy (minCTop d) = minFTop (minDerivToCtxWF d)
  minAssocTmTy (minISigmaEq _ _ dA dB) = minFSigma dA dB
  minAssocTmTy (minESigmaEq _ _ _ _ _ dTy) = dTy
  minAssocTmTy (minCSigma _ _ _ _ _ dTy) = dTy
  minAssocTmTy (minIEqEq d) =
    minFEq (minAssocTmTy d) (minAssocTmLeft d) (minAssocTmLeft d)
  minAssocTmTy (minEEqStar _ dA _ _) = dA
  minAssocTmTy (minCEq _ dA da db) = minFEq dA da db
  minAssocTmTy (minIQtrEq da _) = minFQtr (minSelfTmTy da)
  minAssocTmTy (minEQtrEq _ _ _ _ _ _ _ _ _ _ dTy) = dTy
  minAssocTmTy (minCQtr _ _ _ _ _ _ _ dTy) = dTy

mutual
  minimalToDerivable : {J : JForm} -> Minimal J -> Derivable J
  minimalToDerivable (minVarStar wf dA) =
    varStar (minCtxWFToCtxWF wf) (minimalToDerivable dA)
  minimalToDerivable (minReflTy d) =
    reflTy (minimalToDerivable d)
  minimalToDerivable (minReflTm d) =
    reflTm (minimalToDerivable d)
  minimalToDerivable (minSymTy d dB) =
    symTy (minimalToDerivable d) (minimalToDerivable dB)
  minimalToDerivable (minSymTm d du dA) =
    symTm (minimalToDerivable d) (minimalToDerivable du) (minimalToDerivable dA)
  minimalToDerivable (minTransTy d1 d2) =
    transTy (minimalToDerivable d1) (minimalToDerivable d2)
  minimalToDerivable (minTransTm d1 d2) =
    transTm (minimalToDerivable d1) (minimalToDerivable d2)
  minimalToDerivable (minConv d dAB) =
    conv (minimalToDerivable d) (minimalToDerivable dAB)
  minimalToDerivable (minConvEq d dAB) =
    convEq (minimalToDerivable d) (minimalToDerivable dAB)
  minimalToDerivable (minFTop wf) =
    fTop (minCtxWFToCtxWF wf)
  minimalToDerivable (minITop wf) =
    iTop (minCtxWFToCtxWF wf)
  minimalToDerivable (minCTop d) =
    cTop (minimalToDerivable d)
  minimalToDerivable (minFSigma dA dB) =
    fSigma (minimalToDerivable dA) (minimalToDerivable dB)
  minimalToDerivable (minFSigmaEq dAC dB dBD _) =
    fSigmaEq (minimalToDerivable dAC) (minimalToDerivable dB) (minimalToDerivable dBD)
  minimalToDerivable (minISigma da db dSigma) =
    iSigma (minimalToDerivable da) (minimalToDerivable db) (minimalToDerivable dSigma)
  minimalToDerivable (minISigmaEq dac dbd dA dB) =
    iSigmaEq (minimalToDerivable dac) (minimalToDerivable dbd)
      (minimalToDerivable dA) (minimalToDerivable dB)
  minimalToDerivable (minESigma dM dd _ dm _) =
    eSigma (minimalToDerivable dM) (minimalToDerivable dd) (minimalToDerivable dm)
  minimalToDerivable (minESigmaEq dM dd _ dm dmm _) =
    eSigmaEq (minimalToDerivable dM) (minimalToDerivable dd)
      (minimalToDerivable dm) (minimalToDerivable dmm)
  minimalToDerivable (minCSigma dM dSigma db dc dm _) =
    cSigma (minimalToDerivable dM) (minimalToDerivable dSigma)
      (minimalToDerivable db) (minimalToDerivable dc) (minimalToDerivable dm)
  minimalToDerivable (minFEq dA da db) =
    fEq (minimalToDerivable dA) (minimalToDerivable da) (minimalToDerivable db)
  minimalToDerivable (minFEqEq dAC dac dbd _) =
    fEqEq (minimalToDerivable dAC) (minimalToDerivable dac) (minimalToDerivable dbd)
  minimalToDerivable (minIEq da) =
    iEq (minimalToDerivable da)
  minimalToDerivable (minIEqEq d) =
    iEqEq (minimalToDerivable d)
  minimalToDerivable (minEEqStar dp dA da db) =
    eEqStar (minimalToDerivable dp) (minimalToDerivable dA)
      (minimalToDerivable da) (minimalToDerivable db)
  minimalToDerivable (minCEq dp dA da db) =
    cEq (minimalToDerivable dp) (minimalToDerivable dA)
      (minimalToDerivable da) (minimalToDerivable db)
  minimalToDerivable (minFQtr dA) =
    fQtr (minimalToDerivable dA)
  minimalToDerivable (minFQtrEq dAB) =
    fQtrEq (minimalToDerivable dAB)
  minimalToDerivable (minIQtr da) =
    iQtr (minimalToDerivable da)
  minimalToDerivable (minIQtrEq da db) =
    iQtrEq (minimalToDerivable da) (minimalToDerivable db)
  minimalToDerivable (minEQtr dL dp _ dBranchTy dl _ coh _) =
    eQtr (minimalToDerivable dL) (minimalToDerivable dp)
      (minimalToDerivable dBranchTy) (minimalToDerivable dl) (minimalToDerivable coh)
  minimalToDerivable (minEQtrEq dL dp _ dBranchTy dl dl' dll' _ coh coh' _) =
    eQtrEq (minimalToDerivable dL) (minimalToDerivable dp)
      (minimalToDerivable dBranchTy) (minimalToDerivable dl)
      (minimalToDerivable dl') (minimalToDerivable dll')
      (minimalToDerivable coh) (minimalToDerivable coh')
  minimalToDerivable (minCQtr dL da _ dBranchTy dl _ coh _) =
    cQtr (minimalToDerivable dL) (minimalToDerivable da)
      (minimalToDerivable dBranchTy) (minimalToDerivable dl) (minimalToDerivable coh)

  minCtxWFToCtxWF : {gamma : Ctx} -> MinCtxWF gamma -> CtxWF gamma
  minCtxWFToCtxWF minWfNil = wfNil
  minCtxWFToCtxWF (minWfCons wf dA) =
    wfCons (minCtxWFToCtxWF wf) (minimalToDerivable dA)

  minFitsToFits : {gamma delta : Ctx} {sigma : Subst}
    -> MinFitsSubst gamma delta sigma
    -> FitsSubst gamma delta sigma
  minFitsToFits (minFitsNil wf) =
    fitsNil {delta = []} (minCtxWFToCtxWF wf)
  minFitsToFits (minFitsCons fits dt) =
    fitsCons (minFitsToFits fits) (minimalToDerivable dt)

  minFitsEqToFitsEq : {gamma delta : Ctx} {sigma tau : Subst}
    -> MinFitsEqSubst gamma delta sigma tau
    -> FitsEqSubst gamma delta sigma tau
  minFitsEqToFitsEq (minFitsEqNil wf) =
    fitsEqNil {delta = []} (minCtxWFToCtxWF wf)
  minFitsEqToFitsEq (minFitsEqCons fitsEq dtu _ _) =
    fitsEqCons (minFitsEqToFitsEq fitsEq) (minimalToDerivable dtu)

  derivableToMinimal : {J : JForm} -> Derivable J -> Minimal J
  derivableToMinimal (varStar wf dA) =
    minVarStar (ctxWFToMinCtxWF wf) (derivableToMinimal dA)
  derivableToMinimal (weakenTy d wf) =
    minWeakenTy (derivableToMinimal d) (ctxWFToMinCtxWF wf)
  derivableToMinimal (weakenTyEq d wf) =
    minWeakenTyEq (derivableToMinimal d) (ctxWFToMinCtxWF wf)
  derivableToMinimal (weakenTm d wf) =
    minWeakenTm (derivableToMinimal d) (ctxWFToMinCtxWF wf)
  derivableToMinimal (weakenTmEq d wf) =
    minWeakenTmEq (derivableToMinimal d) (ctxWFToMinCtxWF wf)
  derivableToMinimal (reflTy d) =
    minReflTy (derivableToMinimal d)
  derivableToMinimal (reflTm d) =
    minReflTm (derivableToMinimal d)
  derivableToMinimal (symTy d dB) =
    minSymTy (derivableToMinimal d) (derivableToMinimal dB)
  derivableToMinimal (symTm d du dA) =
    minSymTm (derivableToMinimal d) (derivableToMinimal du) (derivableToMinimal dA)
  derivableToMinimal (transTy d e) =
    minTransTy (derivableToMinimal d) (derivableToMinimal e)
  derivableToMinimal (transTm d e) =
    minTransTm (derivableToMinimal d) (derivableToMinimal e)
  derivableToMinimal (conv d dAB) =
    minConv (derivableToMinimal d) (derivableToMinimal dAB)
  derivableToMinimal (convEq d dAB) =
    minConvEq (derivableToMinimal d) (derivableToMinimal dAB)
  derivableToMinimal (substTyRule d fits) =
    minSubst (derivableToMinimal d) (fitsToMinFits fits)
  derivableToMinimal (substTyEqRule d fits) =
    minSubst (derivableToMinimal d) (fitsToMinFits fits)
  derivableToMinimal (substTmRule d fits) =
    minSubst (derivableToMinimal d) (fitsToMinFits fits)
  derivableToMinimal (substTmEqRule d fits) =
    minSubst (derivableToMinimal d) (fitsToMinFits fits)
  derivableToMinimal (eqSubTyRule d fits) =
    minSubstEq dMin (fitsEqToMinFitsEq (minDerivToCtxWF dMin) fits)
    where
    dMin = derivableToMinimal d
  derivableToMinimal (eqSubTyEqRule d fits) =
    minSubstEq dMin (fitsEqToMinFitsEq (minDerivToCtxWF dMin) fits)
    where
    dMin = derivableToMinimal d
  derivableToMinimal (eqSubTmRule d fits) =
    minSubstEq dMin (fitsEqToMinFitsEq (minDerivToCtxWF dMin) fits)
    where
    dMin = derivableToMinimal d
  derivableToMinimal (eqSubTmEqRule d fits) =
    minSubstEq dMin (fitsEqToMinFitsEq (minDerivToCtxWF dMin) fits)
    where
    dMin = derivableToMinimal d
  derivableToMinimal (fTop wf) =
    minFTop (ctxWFToMinCtxWF wf)
  derivableToMinimal (iTop wf) =
    minITop (ctxWFToMinCtxWF wf)
  derivableToMinimal (cTop d) =
    minCTop (derivableToMinimal d)
  derivableToMinimal (fSigma dA dB) =
    minFSigma (derivableToMinimal dA) (derivableToMinimal dB)
  derivableToMinimal (fSigmaEq dAC dB dBD) =
    minFSigmaEq dACMin dBMin dBDMin dRight
    where
    dACMin = derivableToMinimal dAC
    dBMin = derivableToMinimal dB
    dBDMin = derivableToMinimal dBD
    dCMin = minAssocTyRight dACMin
    dDMin = minTransportFamilyTy dACMin dCMin (minAssocTyRight dBDMin)
    dRight = minFSigma dCMin dDMin
  derivableToMinimal (iSigma da db dSigma) =
    minISigma (derivableToMinimal da) (derivableToMinimal db) (derivableToMinimal dSigma)
  derivableToMinimal (iSigmaEq dac dbd dA dB) =
    minISigmaEq (derivableToMinimal dac) (derivableToMinimal dbd)
      (derivableToMinimal dA) (derivableToMinimal dB)
  derivableToMinimal (eSigma dM dd dm) =
    minESigma dMMin ddMin dSigmaMin dmMin dTyMin
    where
    dMMin = derivableToMinimal dM
    ddMin = derivableToMinimal dd
    dmMin = derivableToMinimal dm
    dSigmaMin = minSelfTmTy ddMin
    dTyMin = minSingleSubstTy dMMin ddMin
  derivableToMinimal (eSigmaEq dM dd dm dmm) =
    minESigmaEq dMMin ddMin dSigmaMin dmMin dmmMin dTyMin
    where
    dMMin = derivableToMinimal dM
    ddMin = derivableToMinimal dd
    dmMin = derivableToMinimal dm
    dmmMin = derivableToMinimal dmm
    dSigmaMin = minAssocTmTy ddMin
    dTyMin = minSingleSubstTy dMMin (minAssocTmLeft ddMin)
  derivableToMinimal (cSigma dM dSigma db dc dm) =
    minCSigma dMMin dSigmaMin dbMin dcMin dmMin dTyMin
    where
    dMMin = derivableToMinimal dM
    dSigmaMin = derivableToMinimal dSigma
    dbMin = derivableToMinimal db
    dcMin = derivableToMinimal dc
    dmMin = derivableToMinimal dm
    dTyMin = minSigmaCompTy dMMin dbMin dcMin
  derivableToMinimal (fEq dA da db) =
    minFEq (derivableToMinimal dA) (derivableToMinimal da) (derivableToMinimal db)
  derivableToMinimal (fEqEq dAC dac dbd) =
    minFEqEq dACMin dacMin dbdMin dRight
    where
    dACMin = derivableToMinimal dAC
    dacMin = derivableToMinimal dac
    dbdMin = derivableToMinimal dbd
    dRight =
      minFEq
        (minAssocTyRight dACMin)
        (minConv (minAssocTmRight dacMin) dACMin)
        (minConv (minAssocTmRight dbdMin) dACMin)
  derivableToMinimal (iEq da) =
    minIEq (derivableToMinimal da)
  derivableToMinimal (iEqEq d) =
    minIEqEq (derivableToMinimal d)
  derivableToMinimal (eEqStar dp dA da db) =
    minEEqStar (derivableToMinimal dp) (derivableToMinimal dA)
      (derivableToMinimal da) (derivableToMinimal db)
  derivableToMinimal (cEq dp dA da db) =
    minCEq (derivableToMinimal dp) (derivableToMinimal dA)
      (derivableToMinimal da) (derivableToMinimal db)
  derivableToMinimal (fQtr dA) =
    minFQtr (derivableToMinimal dA)
  derivableToMinimal (fQtrEq dAB) =
    minFQtrEq (derivableToMinimal dAB)
  derivableToMinimal (iQtr da) =
    minIQtr (derivableToMinimal da)
  derivableToMinimal (iQtrEq da db) =
    minIQtrEq (derivableToMinimal da) (derivableToMinimal db)
  derivableToMinimal (eQtr dL dp dBranchTy dl coh) =
    minEQtr dLMin dpMin dAMin dBranchTyMin dlMin dWkAMin cohMin dTyMin
    where
    dLMin = derivableToMinimal dL
    dpMin = derivableToMinimal dp
    dBranchTyMin = derivableToMinimal dBranchTy
    dlMin = derivableToMinimal dl
    cohMin = derivableToMinimal coh
    dAMin = minQtrInner (minSelfTmTy dpMin)
    wfA = minWfCons (minDerivToCtxWF dAMin) dAMin
    dWkAMin = minWeakenTy {delta = _ ∷ []} dAMin wfA
    dTyMin = minSingleSubstTy dLMin dpMin
  derivableToMinimal (eQtrEq dL dp dBranchTy dl dl' dll' coh coh') =
    minEQtrEq dLMin dpMin dAMin dBranchTyMin dlMin dl'Min dll'Min dWkAMin cohMin coh'Min dTyMin
    where
    dLMin = derivableToMinimal dL
    dpMin = derivableToMinimal dp
    dBranchTyMin = derivableToMinimal dBranchTy
    dlMin = derivableToMinimal dl
    dl'Min = derivableToMinimal dl'
    dll'Min = derivableToMinimal dll'
    cohMin = derivableToMinimal coh
    coh'Min = derivableToMinimal coh'
    dAMin = minQtrInner (minAssocTmTy dpMin)
    wfA = minWfCons (minDerivToCtxWF dAMin) dAMin
    dWkAMin = minWeakenTy {delta = _ ∷ []} dAMin wfA
    dTyMin = minSingleSubstTy dLMin (minAssocTmLeft dpMin)
  derivableToMinimal (cQtr dL da dBranchTy dl coh) =
    minCQtr dLMin daMin dAMin dBranchTyMin dlMin dWkAMin cohMin dTyMin
    where
    dLMin = derivableToMinimal dL
    daMin = derivableToMinimal da
    dBranchTyMin = derivableToMinimal dBranchTy
    dlMin = derivableToMinimal dl
    cohMin = derivableToMinimal coh
    dAMin = minSelfTmTy daMin
    wfA = minWfCons (minDerivToCtxWF dAMin) dAMin
    dWkAMin = minWeakenTy {delta = _ ∷ []} dAMin wfA
    dTyMin = minQtrCompTy dLMin daMin

  ctxWFToMinCtxWF : {gamma : Ctx} -> CtxWF gamma -> MinCtxWF gamma
  ctxWFToMinCtxWF wfNil = minWfNil
  ctxWFToMinCtxWF (wfCons wf dA) =
    minWfCons (ctxWFToMinCtxWF wf) (derivableToMinimal dA)

  fitsToMinFits : {gamma delta : Ctx} {sigma : Subst}
    -> FitsSubst gamma delta sigma
    -> MinFitsSubst gamma delta sigma
  fitsToMinFits (fitsNil wf) =
    minFitsNil (ctxWFToMinCtxWF wf)
  fitsToMinFits (fitsCons fits dt) =
    minFitsCons (fitsToMinFits fits) (derivableToMinimal dt)

  fitsEqToMinFitsEq : {gamma delta : Ctx} {sigma tau : Subst}
    -> MinCtxWF delta
    -> FitsEqSubst gamma delta sigma tau
    -> MinFitsEqSubst gamma delta sigma tau
  fitsEqToMinFitsEq _ (fitsEqNil wf) =
    minFitsEqNil (ctxWFToMinCtxWF wf)
  fitsEqToMinFitsEq (minWfCons wfDelta dA) (fitsEqCons fits dtu) =
    minFitsEqCons fitsMin dtuMin dRight dRightS
    where
    fitsMin = fitsEqToMinFitsEq wfDelta fits
    dtuMin = derivableToMinimal dtu
    dRightS = minAssocTmRight dtuMin
    dAeq = minSubstEqTy dA fitsMin
    dRight = minConv dRightS dAeq
