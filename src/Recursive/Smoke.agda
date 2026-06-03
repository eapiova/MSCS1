{-# OPTIONS --safe #-}

-- Tait-style rebuild (Phase K/L) — non-vacuity smoke test.
-- Builds a concrete closed derivation containing a Sigma ELIMINATOR
-- (`tmElSigma (tmPair tmStar tmStar) tmStar`) and checks that
-- `canonicalFormTheorem` genuinely reduces it to its normal form
-- `tmStar` — verified by `refl`, so the theorem really computes.

module Recursive.Smoke where

open import Recursive.Prelude
open import Data.Empty using (⊥)
open import Data.List.Base using ([] ; _∷_)
open import Data.Product using (Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)

open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Evaluation
open import Recursive.Derivability
open import Recursive.Minimal
open import Recursive.CanonicalForm
open import Recursive.FullCanonicalForm
open import Recursive.Corollaries
open import Recursive.Inversion using (IsJust ; invQtrHead? ; invMinimalQtrHead?)

wf1 : CtxWF (tyTop ∷ [])
wf1 = wfCons wfNil (fTop wfNil)

wf2 : CtxWF (tyTop ∷ tyTop ∷ [])
wf2 = wfCons wf1 (fTop wf1)

-- isType [] (tySigma tyTop tyTop)
dSig : Derivable (isType [] (tySigma tyTop tyTop))
dSig = fSigma (fTop wfNil) (fTop wf1)

-- the pair (*, *) : Sigma Top Top
dPair : Derivable (hasTy [] (tmPair tmStar tmStar) (tySigma tyTop tyTop))
dPair = iSigma (iTop wfNil) (iTop wfNil) dSig

-- motive M = Top over context (Sigma Top Top ∷ [])
dM : Derivable (isType (tySigma tyTop tyTop ∷ []) tyTop)
dM = fTop (wfCons wfNil dSig)

-- branch m = * : sigmaBranchTy Top  (= Top) over (Top ∷ Top ∷ [])
dBranch : Derivable (hasTy (tyTop ∷ tyTop ∷ []) tmStar (sigmaBranchTy tyTop))
dBranch = iTop wf2

-- the eliminator term, well-typed
dElim : Derivable
  (hasTy [] (tmElSigma (tmPair tmStar tmStar) tmStar)
            (subTy (singleSubst (tmPair tmStar tmStar)) tyTop))
dElim = eSigma dM dPair dBranch

-- the canonical-form theorem applied to it inhabits CanonicalForm.
smoke : CanonicalForm
  (hasTy [] (tmElSigma (tmPair tmStar tmStar) tmStar)
            (subTy (singleSubst (tmPair tmStar tmStar)) tyTop))
smoke = canonicalFormTheorem dElim

-- DECISIVE: the theorem computes the eliminator down to `tmStar`.
-- If this `refl` typechecks, normalisation genuinely ran.
smokeReduces : proj₁ (canonicalFormTheorem dElim) ≡ tmStar
smokeReduces = refl

smokeEvaluationTerm : proj₁ (evaluationTerm dElim) ≡ tmStar
smokeEvaluationTerm = refl

fullSmokeSigmaElim : FullCanonicalForm
  (hasTy [] (tmElSigma (tmPair tmStar tmStar) tmStar)
            (subTy (singleSubst (tmPair tmStar tmStar)) tyTop))
fullSmokeSigmaElim = fullCanonicalFormTheorem dElim

fullSmokeSigmaReduces : proj₁ fullSmokeSigmaElim ≡ tmStar
fullSmokeSigmaReduces = refl

dPairEq : Derivable
  (termEq [] (tmPair tmStar tmStar) (tmPair tmStar tmStar) (tySigma tyTop tyTop))
dPairEq = reflTm dPair

fullSmokeSigmaPairEq : FullCanonicalForm
  (termEq [] (tmPair tmStar tmStar) (tmPair tmStar tmStar) (tySigma tyTop tyTop))
fullSmokeSigmaPairEq = fullCanonicalFormTheorem dPairEq

fullSmokeSigmaPairEqCanonical :
  CanonicalTmEq (tmPair tmStar tmStar) (tmPair tmStar tmStar) (tySigma tyTop tyTop)
fullSmokeSigmaPairEqCanonical =
  proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ fullSmokeSigmaPairEq))))))

sigmaPairEqFst :
  CanonicalTmEq (tmPair tmStar tmStar) (tmPair tmStar tmStar) (tySigma tyTop tyTop)
  -> Derivable (termEq [] tmStar tmStar tyTop)
sigmaPairEqFst (canPairTmEq dac _ _ _) = dac

sigmaPairEqSnd :
  CanonicalTmEq (tmPair tmStar tmStar) (tmPair tmStar tmStar) (tySigma tyTop tyTop)
  -> Derivable (termEq [] tmStar tmStar (subTy (singleSubst tmStar) tyTop))
sigmaPairEqSnd (canPairTmEq _ dbd _ _) = dbd

fullSmokeSigmaPairEqFst : Derivable (termEq [] tmStar tmStar tyTop)
fullSmokeSigmaPairEqFst =
  sigmaPairEqFst fullSmokeSigmaPairEqCanonical

fullSmokeSigmaPairEqSnd :
  Derivable (termEq [] tmStar tmStar (subTy (singleSubst tmStar) tyTop))
fullSmokeSigmaPairEqSnd =
  sigmaPairEqSnd fullSmokeSigmaPairEqCanonical

smokeSigmaExistentialFst : proj₁ (sigmaExistential dPair) ≡ tmStar
smokeSigmaExistentialFst = refl

smokeSigmaExistentialSnd : proj₁ (proj₂ (sigmaExistential dPair)) ≡ tmStar
smokeSigmaExistentialSnd = refl

-- Eq-type non-vacuity: refl at Top has canonical representative `tmRefl`.
dEqTy : Derivable (isType [] (tyEq tyTop tmStar tmStar))
dEqTy = fEq (fTop wfNil) (iTop wfNil) (iTop wfNil)

dEqTerm : Derivable (hasTy [] tmRefl (tyEq tyTop tmStar tmStar))
dEqTerm = iEq (iTop wfNil)

smokeEqReduces : proj₁ (canonicalFormTheorem dEqTerm) ≡ tmRefl
smokeEqReduces = refl

fullSmokeEqTerm : FullCanonicalForm
  (hasTy [] tmRefl (tyEq tyTop tmStar tmStar))
fullSmokeEqTerm = fullCanonicalFormTheorem dEqTerm

fullSmokeEqReduces : proj₁ fullSmokeEqTerm ≡ tmRefl
fullSmokeEqReduces = refl

-- Qtr-type non-vacuity: a closed quotient eliminator computes to `tmStar`.
dQtrTy : Derivable (isType [] (tyQtr tyTop))
dQtrTy = fQtr (fTop wfNil)

dQtrClass : Derivable (hasTy [] (tmClass tmStar) (tyQtr tyTop))
dQtrClass = iQtr (iTop wfNil)

dQtrMotive : Derivable (isType (tyQtr tyTop ∷ []) tyTop)
dQtrMotive = fTop (wfCons wfNil dQtrTy)

dQtrBranchTy : Derivable (isType (tyTop ∷ []) (qtrBranchTy tyTop))
dQtrBranchTy = fTop wf1

dQtrBranch : Derivable (hasTy (tyTop ∷ []) tmStar (qtrBranchTy tyTop))
dQtrBranch = iTop wf1

dQtrCoh : Derivable
  (termEq (wkTyBy 1 tyTop ∷ tyTop ∷ [])
    (wkTmBy 1 tmStar)
    (renTm qtrSecondBranchRen tmStar)
    (qtrCohTy tyTop))
dQtrCoh = cTop (iTop wf2)

dQtrElim : Derivable
  (hasTy [] (tmElQtr tmStar (tmClass tmStar))
    (subTy (singleSubst (tmClass tmStar)) tyTop))
dQtrElim = eQtr dQtrMotive dQtrClass dQtrBranchTy dQtrBranch dQtrCoh

smokeQtrReduces : proj₁ (canonicalFormTheorem dQtrElim) ≡ tmStar
smokeQtrReduces = refl

fullSmokeQtrElim : FullCanonicalForm
  (hasTy [] (tmElQtr tmStar (tmClass tmStar))
    (subTy (singleSubst (tmClass tmStar)) tyTop))
fullSmokeQtrElim = fullCanonicalFormTheorem dQtrElim

fullSmokeQtrReduces : proj₁ fullSmokeQtrElim ≡ tmStar
fullSmokeQtrReduces = refl

fullSmokeQtrClass : FullCanonicalForm
  (hasTy [] (tmClass tmStar) (tyQtr tyTop))
fullSmokeQtrClass = fullCanonicalFormTheorem dQtrClass

fullSmokeQtrClassReduces : proj₁ fullSmokeQtrClass ≡ tmClass tmStar
fullSmokeQtrClassReduces = refl

fullSmokeQtrClassCanonical : CanonicalTm (tmClass tmStar) (tyQtr tyTop)
fullSmokeQtrClassCanonical = canClassTm (iTop wfNil)

fullSmokeQtrClassDerivable : Derivable (hasTy [] (tmClass tmStar) (tyQtr tyTop))
fullSmokeQtrClassDerivable = canonicalTmDerivable fullSmokeQtrClassCanonical

qtrClassRepresentativeTy :
  CanonicalTm (tmClass tmStar) (tyQtr tyTop)
  -> Derivable (hasTy [] tmStar tyTop)
qtrClassRepresentativeTy (canClassTm da) = da

fullSmokeQtrClassRepresentativeTy : Derivable (hasTy [] tmStar tyTop)
fullSmokeQtrClassRepresentativeTy =
  qtrClassRepresentativeTy
    (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ fullSmokeQtrClass)))))

smokeTregConsistent :
  Derivable (typeEq [] tyTop (tySigma tyTop tyTop))
  -> ⊥
smokeTregConsistent = tregConsistent

smokeQtrHeadInversion : IsJust (invQtrHead? dQtrElim)
smokeQtrHeadInversion = tt

minWf1 : MinCtxWF (tyTop ∷ [])
minWf1 = minWfCons minWfNil (minFTop minWfNil)

minWf2 : MinCtxWF (tyTop ∷ tyTop ∷ [])
minWf2 = minWfCons minWf1 (minFTop minWf1)

minQtrTy : Minimal (isType [] (tyQtr tyTop))
minQtrTy = minFQtr (minFTop minWfNil)

minQtrClass : Minimal (hasTy [] (tmClass tmStar) (tyQtr tyTop))
minQtrClass = minIQtr (minITop minWfNil)

minQtrMotive : Minimal (isType (tyQtr tyTop ∷ []) tyTop)
minQtrMotive = minFTop (minWfCons minWfNil minQtrTy)

minQtrBranchTy : Minimal (isType (tyTop ∷ []) (qtrBranchTy tyTop))
minQtrBranchTy = minFTop minWf1

minQtrBranch : Minimal (hasTy (tyTop ∷ []) tmStar (qtrBranchTy tyTop))
minQtrBranch = minITop minWf1

minQtrCoh : Minimal
  (termEq (wkTyBy 1 tyTop ∷ tyTop ∷ [])
    (wkTmBy 1 tmStar)
    (renTm qtrSecondBranchRen tmStar)
    (qtrCohTy tyTop))
minQtrCoh = minCTop (minITop minWf2)

minQtrElim : Minimal
  (hasTy [] (tmElQtr tmStar (tmClass tmStar))
    (subTy (singleSubst (tmClass tmStar)) tyTop))
minQtrElim =
  minEQtr minQtrMotive minQtrClass (minFTop minWfNil) minQtrBranchTy minQtrBranch
    (minFTop minWf1) minQtrCoh
    (minFTop minWfNil)

smokeMinimalQtrHeadInversion : IsJust (invMinimalQtrHead? minQtrElim)
smokeMinimalQtrHeadInversion = tt
