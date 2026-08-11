{-# OPTIONS --safe #-}

module Recursive.EvalSound where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List.Base using ([] ; _∷_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

open import Recursive.Prelude
open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Evaluation
open import Recursive.Derivability
open import Recursive.Presupposition
open import Recursive.Minimal
open import Recursive.Inversion

noMinimalEqTerm :
  {gamma : Ctx} {A T : RawType} {a : RawTerm}
  -> Minimal (hasTy gamma (tmEq A a) T)
  -> ⊥
noMinimalEqTerm (minConv d _) = noMinimalEqTerm d

record NatElimPremises
    (gamma : Ctx) (a l n : RawTerm) (T : RawType) : Type where
  constructor natElimPremises
  field
    natL : RawType
    natMotiveTy : Derivable (isType (tyNat ∷ gamma) natL)
    natScrutineeTy : Derivable (hasTy gamma n tyNat)
    natZeroTm : Derivable (hasTy gamma a (subTy (singleSubst tmZero) natL))
    natStepTm :
      Derivable (hasTy ((natStepArgTy natL) ∷ tyNat ∷ gamma) l (natStepTy natL))
    natTargetEq : Derivable (typeEq gamma (subTy (singleSubst n) natL) T)

open NatElimPremises public

natElimPremisesConv :
  {gamma : Ctx} {a l n : RawTerm} {S T : RawType}
  -> NatElimPremises gamma a l n S
  -> Derivable (typeEq gamma S T)
  -> NatElimPremises gamma a l n T
natElimPremisesConv prem dST =
  natElimPremises
    (natL prem)
    (natMotiveTy prem)
    (natScrutineeTy prem)
    (natZeroTm prem)
    (natStepTm prem)
    (transTy (natTargetEq prem) dST)

invMinimalNatHead :
  {gamma : Ctx} {a l n : RawTerm} {T : RawType}
  -> Minimal (hasTy gamma (tmElNat a l n) T)
  -> NatElimPremises gamma a l n T
invMinimalNatHead (minConv d dST) =
  natElimPremisesConv (invMinimalNatHead d) (minimalToDerivable dST)
invMinimalNatHead
  (minENat {L = L} dL dn da _ dl dTy) =
  natElimPremises
    L
    (minimalToDerivable dL)
    (minimalToDerivable dn)
    (minimalToDerivable da)
    (minimalToDerivable dl)
    (reflTy (minimalToDerivable dTy))

invNatHead :
  {gamma : Ctx} {a l n : RawTerm} {T : RawType}
  -> Derivable (hasTy gamma (tmElNat a l n) T)
  -> NatElimPremises gamma a l n T
invNatHead d =
  invMinimalNatHead (derivableToMinimal d)

record SucPremises (gamma : Ctx) (n : RawTerm) (T : RawType) : Type where
  constructor sucPremises
  field
    sucPredTy : Derivable (hasTy gamma n tyNat)
    sucTargetEq : Derivable (typeEq gamma tyNat T)

open SucPremises public

sucPremisesConv :
  {gamma : Ctx} {n : RawTerm} {S T : RawType}
  -> SucPremises gamma n S
  -> Derivable (typeEq gamma S T)
  -> SucPremises gamma n T
sucPremisesConv prem dST =
  sucPremises
    (sucPredTy prem)
    (transTy (sucTargetEq prem) dST)

invMinimalSuc :
  {gamma : Ctx} {n : RawTerm} {T : RawType}
  -> Minimal (hasTy gamma (tmSuc n) T)
  -> SucPremises gamma n T
invMinimalSuc (minConv d dST) =
  sucPremisesConv (invMinimalSuc d) (minimalToDerivable dST)
invMinimalSuc (minISuc dn) =
  sucPremises
    (minimalToDerivable dn)
    (reflTy (assocTy (minimalToDerivable dn)))

invSucAtNat :
  {gamma : Ctx} {n : RawTerm}
  -> Derivable (hasTy gamma (tmSuc n) tyNat)
  -> Derivable (hasTy gamma n tyNat)
invSucAtNat d =
  sucPredTy (invMinimalSuc (derivableToMinimal d))

natStepFitsEqHelper :
  {gamma : Ctx} {L : RawType} {n rec rec' : RawTerm}
  -> Derivable (hasTy gamma n tyNat)
  -> Derivable (termEq gamma rec rec' (subTy (singleSubst n) L))
  -> FitsEqSubst gamma ((natStepArgTy L) ∷ tyNat ∷ gamma)
       (natStepCompSubCtx n rec gamma)
       (natStepCompSubCtx n rec' gamma)
natStepFitsEqHelper {gamma = gamma} {L = L} {n = n} {rec = rec} {rec' = rec'} dn drec =
  fitsEqCons fitsN recEqAtStepArg
  where
  gammaWF : CtxWF gamma
  gammaWF = derivToCtxWF dn

  fitsGamma :
    FitsEqSubst gamma gamma
      (keepSubstCtx 0 gamma)
      (keepSubstCtx 0 gamma)
  fitsGamma =
    fitsEqKeep {delta = []} {gamma = gamma} gammaWF

  fitsN :
    FitsEqSubst gamma (tyNat ∷ gamma)
      (consSubst n (keepSubstCtx 0 gamma))
      (consSubst n (keepSubstCtx 0 gamma))
  fitsN =
    fitsEqCons fitsGamma (reflTm dn)

  recEqAtStepArg :
    Derivable
      (termEq gamma rec rec'
        (subTy (consSubst n (keepSubstCtx 0 gamma)) (natStepArgTy L)))
  recEqAtStepArg =
    subst
      (λ T -> Derivable (termEq gamma rec rec' T))
      (sym (natStepArgTyComp n gamma L))
      drec

evalSoundTm :
  {t g : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t A)
  -> t =>e g
  -> Derivable (hasTy [] g A) × Derivable (termEq [] t g A)
evalSoundTm d evalStar =
  d , reflTm d
evalSoundTm d evalPair =
  d , reflTm d
evalSoundTm d evalRefl =
  d , reflTm d
evalSoundTm d evalEqTm =
  ⊥-elim (noMinimalEqTerm (derivableToMinimal d))
evalSoundTm d evalClass =
  d , reflTm d
evalSoundTm d evalZero =
  d , reflTm d
evalSoundTm d evalSucV =
  d , reflTm d
evalSoundTm d (evalElSigma evScr evRed) =
  finalTy , finalEq
  where
  prem = invSigmaHead d

  scrSound = evalSoundTm (scrutineeTy prem) evScr
  pairTyDeriv = proj₁ scrSound
  scrEq = proj₂ scrSound

  pairPrem = invPairAtSigma pairTyDeriv

  beta : Derivable
    (termEq []
      (tmElSigma _ _)
      _
      (subTy (singleSubst _) (M prem)))
  beta =
    cSigma
      (motiveTy prem)
      (pairSigmaTy pairPrem)
      (pairFstTy pairPrem)
      (pairSndTy pairPrem)
      (branchTm prem)

  redSound = evalSoundTm (assocTmRight beta) evRed
  redTy = proj₁ redSound
  redEq = proj₂ redSound

  scrSubTyEq :
    Derivable
      (typeEq []
        (subTy (singleSubst _) (M prem))
        (subTy (singleSubst _) (M prem)))
  scrSubTyEq =
    singleEqSubstTyHelper (motiveTy prem) scrEq

  scrSubTyRight : Derivable (isType [] (subTy (singleSubst _) (M prem)))
  scrSubTyRight =
    singleSubstTyHelper (motiveTy prem) pairTyDeriv

  betaAtScr :
    Derivable
      (termEq []
        (tmElSigma _ _)
        _
        (subTy (singleSubst _) (M prem)))
  betaAtScr =
    convEq beta (symTy scrSubTyEq scrSubTyRight)

  congr :
    Derivable
      (termEq []
        (tmElSigma _ _)
        (tmElSigma _ _)
        (subTy (singleSubst _) (M prem)))
  congr =
    eSigmaEq
      (motiveTy prem)
      scrEq
      (branchTm prem)
      (reflTm (branchTm prem))

  redAtScr :
    Derivable
      (termEq []
        _
        _
        (subTy (singleSubst _) (M prem)))
  redAtScr =
    convEq redEq (symTy scrSubTyEq scrSubTyRight)

  atScr :
    Derivable
      (termEq []
        (tmElSigma _ _)
        _
        (subTy (singleSubst _) (M prem)))
  atScr =
    transTm (transTm congr betaAtScr) redAtScr

  finalTy : Derivable (hasTy [] _ _)
  finalTy =
    conv (assocTmRight atScr) (targetEq prem)

  finalEq : Derivable (termEq [] _ _ _)
  finalEq =
    convEq atScr (targetEq prem)
evalSoundTm d (evalElNatZ evScr evRed) =
  finalTy , finalEq
  where
  prem = invNatHead d

  scrSound = evalSoundTm (natScrutineeTy prem) evScr
  zeroTyDeriv = proj₁ scrSound
  scrEq = proj₂ scrSound

  beta : Derivable
    (termEq []
      (tmElNat _ _ tmZero)
      _
      (subTy (singleSubst tmZero) (natL prem)))
  beta =
    cNatZ
      (natMotiveTy prem)
      (natZeroTm prem)
      (natStepTm prem)

  redSound = evalSoundTm (assocTmRight beta) evRed
  redEq = proj₂ redSound

  scrSubTyEq :
    Derivable
      (typeEq []
        (subTy (singleSubst _) (natL prem))
        (subTy (singleSubst tmZero) (natL prem)))
  scrSubTyEq =
    singleEqSubstTyHelper (natMotiveTy prem) scrEq

  scrSubTyRight : Derivable (isType [] (subTy (singleSubst tmZero) (natL prem)))
  scrSubTyRight =
    singleSubstTyHelper (natMotiveTy prem) zeroTyDeriv

  betaAtScr :
    Derivable
      (termEq []
        (tmElNat _ _ tmZero)
        _
        (subTy (singleSubst _) (natL prem)))
  betaAtScr =
    convEq beta (symTy scrSubTyEq scrSubTyRight)

  congr :
    Derivable
      (termEq []
        (tmElNat _ _ _)
        (tmElNat _ _ tmZero)
        (subTy (singleSubst _) (natL prem)))
  congr =
    eNatEq
      (natMotiveTy prem)
      scrEq
      (natZeroTm prem)
      (reflTm (natZeroTm prem))
      (natStepTm prem)
      (reflTm (natStepTm prem))

  redAtScr :
    Derivable
      (termEq []
        _
        _
        (subTy (singleSubst _) (natL prem)))
  redAtScr =
    convEq redEq (symTy scrSubTyEq scrSubTyRight)

  atScr :
    Derivable
      (termEq []
        (tmElNat _ _ _)
        _
        (subTy (singleSubst _) (natL prem)))
  atScr =
    transTm (transTm congr betaAtScr) redAtScr

  finalTy : Derivable (hasTy [] _ _)
  finalTy =
    conv (assocTmRight atScr) (natTargetEq prem)

  finalEq : Derivable (termEq [] _ _ _)
  finalEq =
    convEq atScr (natTargetEq prem)
evalSoundTm d
    (evalElNatS {a = a} {l = l} {p = p} {k = k} {recVal = recVal} {g = g}
      evScr evRecRed evStepRed) =
  finalTy , finalEq
  where
  prem = invNatHead d

  scrSound = evalSoundTm (natScrutineeTy prem) evScr
  sucTyDeriv = proj₁ scrSound
  scrEq = proj₂ scrSound

  predTy : Derivable (hasTy [] k tyNat)
  predTy =
    invSucAtNat sucTyDeriv

  recHeadTy :
    Derivable (hasTy [] (tmElNat a l k) (subTy (singleSubst k) (natL prem)))
  recHeadTy =
    eNat
      (natMotiveTy prem)
      predTy
      (natZeroTm prem)
      (natStepTm prem)

  recSound = evalSoundTm recHeadTy evRecRed
  recValTy = proj₁ recSound
  recEq = proj₂ recSound

  stepTy :
    Derivable
      (hasTy []
        (subTm (natStepCompSub k recVal) l)
        (subTy (singleSubst (tmSuc k)) (natL prem)))
  stepTy =
    subst
      (λ T -> Derivable (hasTy [] (subTm (natStepCompSub k recVal) l) T))
      (natStepTyComp k recVal [] (natL prem))
      (subst
        (λ u -> Derivable
          (hasTy [] u (subTy (natStepCompSubCtx k recVal []) (natStepTy (natL prem)))))
        (natStepCompSubCtx-subTm k recVal [] l)
        (substTmRule
          (natStepTm prem)
          (natStepFitsHelper predTy recValTy)))

  stepSound = evalSoundTm stepTy evStepRed
  stepEq = proj₂ stepSound

  beta : Derivable
    (termEq []
      (tmElNat a l (tmSuc k))
      (subTm (natStepCompSub k (tmElNat a l k)) l)
      (subTy (singleSubst (tmSuc k)) (natL prem)))
  beta =
    cNatS
      (natMotiveTy prem)
      predTy
      (natZeroTm prem)
      (natStepTm prem)

  stepCongCtx :
    Derivable
      (termEq []
        (subTm (natStepCompSubCtx k (tmElNat a l k) []) l)
        (subTm (natStepCompSubCtx k recVal []) l)
        (subTy (natStepCompSubCtx k (tmElNat a l k) []) (natStepTy (natL prem))))
  stepCongCtx =
    eqSubTmRule
      (natStepTm prem)
      (natStepFitsEqHelper predTy recEq)

  stepCongPlain :
    Derivable
      (termEq []
        (subTm (natStepCompSub k (tmElNat a l k)) l)
        (subTm (natStepCompSub k recVal) l)
        (subTy (singleSubst (tmSuc k)) (natL prem)))
  stepCongPlain =
    subst
      (λ T -> Derivable
        (termEq []
          (subTm (natStepCompSub k (tmElNat a l k)) l)
          (subTm (natStepCompSub k recVal) l)
          T))
      (natStepTyComp k (tmElNat a l k) [] (natL prem))
      (subst
        (λ v -> Derivable
          (termEq []
            (subTm (natStepCompSub k (tmElNat a l k)) l)
            v
            (subTy (natStepCompSubCtx k (tmElNat a l k) []) (natStepTy (natL prem)))))
        (natStepCompSubCtx-subTm k recVal [] l)
        (subst
          (λ u -> Derivable
            (termEq []
              u
              (subTm (natStepCompSubCtx k recVal []) l)
              (subTy (natStepCompSubCtx k (tmElNat a l k) []) (natStepTy (natL prem)))))
          (natStepCompSubCtx-subTm k (tmElNat a l k) [] l)
          stepCongCtx))

  sucReduction :
    Derivable
      (termEq []
        (tmElNat a l (tmSuc k))
        g
        (subTy (singleSubst (tmSuc k)) (natL prem)))
  sucReduction =
    transTm beta (transTm stepCongPlain stepEq)

  scrSubTyEq :
    Derivable
      (typeEq []
        (subTy (singleSubst _) (natL prem))
        (subTy (singleSubst (tmSuc k)) (natL prem)))
  scrSubTyEq =
    singleEqSubstTyHelper (natMotiveTy prem) scrEq

  scrSubTyRight : Derivable (isType [] (subTy (singleSubst (tmSuc k)) (natL prem)))
  scrSubTyRight =
    singleSubstTyHelper (natMotiveTy prem) sucTyDeriv

  sucReductionAtScr :
    Derivable
      (termEq []
        (tmElNat a l (tmSuc k))
        g
        (subTy (singleSubst _) (natL prem)))
  sucReductionAtScr =
    convEq sucReduction (symTy scrSubTyEq scrSubTyRight)

  congr :
    Derivable
      (termEq []
        (tmElNat a l p)
        (tmElNat a l (tmSuc k))
        (subTy (singleSubst _) (natL prem)))
  congr =
    eNatEq
      (natMotiveTy prem)
      scrEq
      (natZeroTm prem)
      (reflTm (natZeroTm prem))
      (natStepTm prem)
      (reflTm (natStepTm prem))

  atScr :
    Derivable
      (termEq []
        (tmElNat a l p)
        g
        (subTy (singleSubst _) (natL prem)))
  atScr =
    transTm congr sucReductionAtScr

  finalTy : Derivable (hasTy [] _ _)
  finalTy =
    conv (assocTmRight atScr) (natTargetEq prem)

  finalEq : Derivable (termEq [] _ _ _)
  finalEq =
    convEq atScr (natTargetEq prem)
evalSoundTm d (evalElQtr evScr evRed) =
  finalTy , finalEq
  where
  prem = invQtrHead d

  scrSound = evalSoundTm (scrutineeTy prem) evScr
  classTyDeriv = proj₁ scrSound
  scrEq = proj₂ scrSound

  classPrem = invClassAtQtr classTyDeriv

  beta : Derivable
    (termEq []
      (tmElQtr _ (tmClass _))
      _
      (subTy (singleSubst (tmClass _)) (L prem)))
  beta =
    cQtr
      (motiveTy prem)
      (classRepTy classPrem)
      (branchTy prem)
      (branchTm prem)
      (coherence prem)

  redSound = evalSoundTm (assocTmRight beta) evRed
  redEq = proj₂ redSound

  scrSubTyEq :
    Derivable
      (typeEq []
        (subTy (singleSubst _) (L prem))
        (subTy (singleSubst (tmClass _)) (L prem)))
  scrSubTyEq =
    singleEqSubstTyHelper (motiveTy prem) scrEq

  scrSubTyRight : Derivable (isType [] (subTy (singleSubst (tmClass _)) (L prem)))
  scrSubTyRight =
    singleSubstTyHelper (motiveTy prem) classTyDeriv

  betaAtScr :
    Derivable
      (termEq []
        (tmElQtr _ (tmClass _))
        _
        (subTy (singleSubst _) (L prem)))
  betaAtScr =
    convEq beta (symTy scrSubTyEq scrSubTyRight)

  congr :
    Derivable
      (termEq []
        (tmElQtr _ _)
        (tmElQtr _ (tmClass _))
        (subTy (singleSubst _) (L prem)))
  congr =
    eQtrEq
      (motiveTy prem)
      scrEq
      (branchTy prem)
      (branchTm prem)
      (branchTm prem)
      (reflTm (branchTm prem))
      (coherence prem)
      (coherence prem)

  redAtScr :
    Derivable
      (termEq []
        _
        _
        (subTy (singleSubst _) (L prem)))
  redAtScr =
    convEq redEq (symTy scrSubTyEq scrSubTyRight)

  atScr :
    Derivable
      (termEq []
        (tmElQtr _ _)
        _
        (subTy (singleSubst _) (L prem)))
  atScr =
    transTm (transTm congr betaAtScr) redAtScr

  finalTy : Derivable (hasTy [] _ _)
  finalTy =
    conv (assocTmRight atScr) (targetEq prem)

  finalEq : Derivable (termEq [] _ _ _)
  finalEq =
    convEq atScr (targetEq prem)

evalSoundTmEq :
  {t u g h : RawTerm} {A : RawType}
  -> Derivable (termEq [] t u A)
  -> t =>e g
  -> u =>e h
  -> Derivable (termEq [] g h A)
evalSoundTmEq d evt evu =
  transTm
    (symTm leftEq leftValueTy dA)
    (transTm d rightEq)
  where
  leftSound = evalSoundTm (assocTmLeft d) evt
  rightSound = evalSoundTm (assocTmRight d) evu

  leftValueTy = proj₁ leftSound
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
  dA = assocTmTy d
