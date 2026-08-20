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
open import Data.Nat using (zero ; suc)
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
  proj₁ (proj₂ (proj₂ (proj₂ (proj₂ fullSmokeSigmaPairEq))))

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
    (proj₁ (proj₂ (proj₂ fullSmokeQtrClass)))

-- Nat non-vacuity: the eliminator doubles one to two.
dNat : Derivable (isType [] tyNat)
dNat = fNat wfNil

wfNat1 : CtxWF (tyNat ∷ [])
wfNat1 = wfCons wfNil dNat

wfNat2 : CtxWF (tyNat ∷ tyNat ∷ [])
wfNat2 = wfCons wfNat1 (fNat wfNat1)

dOne : Derivable (hasTy [] (tmSuc tmZero) tyNat)
dOne = iSuc (iZero wfNil)

dNatMotive : Derivable (isType (tyNat ∷ []) tyNat)
dNatMotive = fNat wfNat1

dNatStep : Derivable
  (hasTy (natStepArgTy tyNat ∷ tyNat ∷ [])
    (tmSuc (tmSuc (var zero)))
    (natStepTy tyNat))
dNatStep =
  iSuc (iSuc
    (varStar {gamma = tyNat ∷ []} {delta = []} {A = tyNat}
      wfNat2 (fNat wfNat1)))

dDouble : Derivable
  (hasTy []
    (tmElNat tmZero (tmSuc (tmSuc (var zero))) (tmSuc tmZero))
    (subTy (singleSubst (tmSuc tmZero)) tyNat))
dDouble =
  eNat dNatMotive dOne (iZero wfNil) dNatStep

evalDouble :
  tmElNat tmZero (tmSuc (tmSuc (var zero))) (tmSuc tmZero)
    =>e tmSuc (tmSuc tmZero)
evalDouble =
  evalElNatS evalSucV (evalElNatZ evalZero evalZero) evalSucV

smokeNatElimReduces : proj₁ (canonicalFormTheorem dDouble) ≡ tmSuc (tmSuc tmZero)
smokeNatElimReduces =
  evalDetTm (proj₂ (canonicalFormTheorem dDouble)) evalDouble

fullSmokeNatElim : FullCanonicalForm
  (hasTy []
    (tmElNat tmZero (tmSuc (tmSuc (var zero))) (tmSuc tmZero))
    (subTy (singleSubst (tmSuc tmZero)) tyNat))
fullSmokeNatElim =
  fullCanonicalFormTheorem dDouble

fullSmokeNatElimReduces : proj₁ fullSmokeNatElim ≡ tmSuc (tmSuc tmZero)
fullSmokeNatElimReduces =
  evalDetTm (proj₁ (proj₂ fullSmokeNatElim)) evalDouble

smokeNumeralDistinct :
  Derivable (termEq [] tmZero (tmSuc tmZero) tyNat)
  -> ⊥
smokeNumeralDistinct = natNoConfusion

smokeTregNonCollapse :
  Derivable (typeEq [] tyTop (tySigma tyTop tyTop))
  -> ⊥
smokeTregNonCollapse = tregNonCollapse

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

-- ---------------------------------------------------------------------------
-- ADVERSARIAL Qtr test.
--
-- Qtr evaluation "leaks" the representative: `tmElQtr l (tmClass a)`
-- substitutes the concrete representative `a` into the branch `l`. Since
-- `iQtrEq` identifies ALL representatives ([a] = [b] for any a, b : A), one
-- might worry that a motive genuinely depending on the quotient variable
-- could observe the choice of representative and break canonical forms.
--
-- This section is the worst case: the dependent motive
--   Ladv = tyEq (tyQtr tyTop) (var 0) (tmClass tmStar)
-- mentions the quotient variable, the branch is typed only via conversion
-- through the iQtrEq collapse, and coherence likewise. The refl-checks at
-- the end confirm the eliminator still computes to a canonical form
-- (tmRefl) at the declared type, so the leak is harmless: RawType has no
-- large elimination, and any term-level dependence on representatives is
-- collapsed by iQtrEq.
-- ---------------------------------------------------------------------------

wfQtr0 : CtxWF (tyQtr tyTop ∷ [])
wfQtr0 = wfCons wfNil (fQtr (fTop wfNil))

-- A = tyTop, L = tyEq (tyQtr tyTop) (var 0) (tmClass tmStar) over (tyQtr tyTop ∷ [])
Ladv : RawType
Ladv = tyEq (tyQtr tyTop) (var zero) (tmClass tmStar)

-- the quotient variable in context (tyQtr tyTop ∷ []):
-- var 0 : wkTyBy 1 (tyQtr tyTop) = tyQtr tyTop
varQ : Derivable (hasTy (tyQtr tyTop ∷ []) (var zero) (tyQtr tyTop))
varQ = varStar {delta = []} wfQtr0 (fQtr (fTop wfNil))

clStar0 : Derivable (hasTy (tyQtr tyTop ∷ []) (tmClass tmStar) (tyQtr tyTop))
clStar0 = iQtr (iTop wfQtr0)

-- L is a type over (tyQtr tyTop ∷ [])
dLadv : Derivable (isType (tyQtr tyTop ∷ []) Ladv)
dLadv = fEq (fQtr (fTop wfQtr0)) varQ clStar0

-- branch type over (tyTop ∷ [])
branchTyAdv : RawType
branchTyAdv = qtrBranchTy Ladv  -- = tyEq (tyQtr tyTop) (tmClass (var 0)) (tmClass tmStar)

-- var 0 : tyTop in (tyTop ∷ [])
varT0 : Derivable (hasTy (tyTop ∷ []) (var zero) (wkTyBy 1 tyTop))
varT0 = varStar {delta = []} wf1 (fTop wfNil)

clVar0 : Derivable (hasTy (tyTop ∷ []) (tmClass (var zero)) (tyQtr tyTop))
clVar0 = iQtr varT0

clStarT : Derivable (hasTy (tyTop ∷ []) (tmClass tmStar) (tyQtr tyTop))
clStarT = iQtr (iTop wf1)

-- [var0] = [tmStar] in Qtr Top  (total collapse)
qEqAdv : Derivable (termEq (tyTop ∷ []) (tmClass (var zero)) (tmClass tmStar) (tyQtr tyTop))
qEqAdv = iQtrEq varT0 (iTop wf1)

-- Eq(Qtr,[v0],[v0]) ≡ Eq(Qtr,[v0],[*])
tyEqConv : Derivable (typeEq (tyTop ∷ [])
  (tyEq (tyQtr tyTop) (tmClass (var zero)) (tmClass (var zero)))
  (tyEq (tyQtr tyTop) (tmClass (var zero)) (tmClass tmStar)))
tyEqConv = fEqEq (reflTy (fQtr (fTop wf1)))
                 (reflTm clVar0)
                 qEqAdv

-- tmRefl : Eq(Qtr,[v0],[v0]), then conv to branchTyAdv
reflBranch0 : Derivable (hasTy (tyTop ∷ []) tmRefl
  (tyEq (tyQtr tyTop) (tmClass (var zero)) (tmClass (var zero))))
reflBranch0 = iEq clVar0

dlAdv : Derivable (hasTy (tyTop ∷ []) tmRefl branchTyAdv)
dlAdv = conv reflBranch0 tyEqConv

-- qtrCohTy Ladv = tyEq (tyQtr tyTop) (tmClass (var 1)) (tmClass tmStar)
cohTyAdv : RawType
cohTyAdv = qtrCohTy Ladv

-- var 1 : tyTop in coherence context (wkTyBy 1 tyTop ∷ tyTop ∷ [])
varT1 : Derivable (hasTy (wkTyBy 1 tyTop ∷ tyTop ∷ []) (tmClass (var (suc zero))) (tyQtr tyTop))
varT1 = iQtr (varStar {delta = wkTyBy 1 tyTop ∷ []} wf2 (fTop wfNil))

-- [var1] = [*] in Qtr Top
qEqCoh : Derivable (termEq (wkTyBy 1 tyTop ∷ tyTop ∷ [])
  (tmClass (var (suc zero))) (tmClass tmStar) (tyQtr tyTop))
qEqCoh = iQtrEq (varStar {delta = wkTyBy 1 tyTop ∷ []} wf2 (fTop wfNil)) (iTop wf2)

-- type-eq: Eq(Qtr,[v1],[v1]) ≡ qtrCohTy Ladv = Eq(Qtr,[v1],[*])
cohTyEq : Derivable (typeEq (wkTyBy 1 tyTop ∷ tyTop ∷ [])
  (tyEq (tyQtr tyTop) (tmClass (var (suc zero))) (tmClass (var (suc zero))))
  cohTyAdv)
cohTyEq = fEqEq (reflTy (fQtr (fTop wf2))) (reflTm varT1) qEqCoh

-- coherence: wkTmBy 1 tmRefl = tmRefl, renTm qtrSecondBranchRen tmRefl = tmRefl
-- so need termEq ... tmRefl tmRefl cohTyAdv
reflCoh0 : Derivable (termEq (wkTyBy 1 tyTop ∷ tyTop ∷ []) tmRefl tmRefl
  (tyEq (tyQtr tyTop) (tmClass (var (suc zero))) (tmClass (var (suc zero)))))
reflCoh0 = reflTm (iEq varT1)

dcohAdv : Derivable (termEq (wkTyBy 1 tyTop ∷ tyTop ∷ [])
  (wkTmBy 1 tmRefl) (renTm qtrSecondBranchRen tmRefl) cohTyAdv)
dcohAdv = convEq reflCoh0 cohTyEq

-- p = tmClass tmStar : Qtr Top in []
dpAdv : Derivable (hasTy [] (tmClass tmStar) (tyQtr tyTop))
dpAdv = iQtr (iTop wfNil)

-- branch type is a type over (tyTop ∷ [])
dBranchTyAdv : Derivable (isType (tyTop ∷ []) branchTyAdv)
dBranchTyAdv = fEq (fQtr (fTop wf1)) clVar0 clStarT

-- THE adversarial eliminator
dElimAdv : Derivable (hasTy [] (tmElQtr tmRefl (tmClass tmStar))
  (subTy (singleSubst (tmClass tmStar)) Ladv))
dElimAdv = eQtr dLadv dpAdv dBranchTyAdv dlAdv dcohAdv

-- declared type normal form: tyEq (tyQtr tyTop) (tmClass tmStar) (tmClass tmStar)
declTyAdv≡ : subTy (singleSubst (tmClass tmStar)) Ladv
  ≡ tyEq (tyQtr tyTop) (tmClass tmStar) (tmClass tmStar)
declTyAdv≡ = refl

cfAdv : CanonicalForm (hasTy [] (tmElQtr tmRefl (tmClass tmStar))
  (subTy (singleSubst (tmClass tmStar)) Ladv))
cfAdv = canonicalFormTheorem dElimAdv

-- DECISIVE: the worst-case dependent-motive eliminator computes to tmRefl.
-- (The companion check that the "evaluated" type component is the declared
-- type is gone with type evaluation: there is no such component now, and
-- the readout is indexed by the declared type itself.)
smokeQtrAdvReduces : proj₁ cfAdv ≡ tmRefl
smokeQtrAdvReduces = refl
