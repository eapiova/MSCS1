{-# OPTIONS --safe #-}

module Tait.EvalSound where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List.Base using ([])
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

open import Tait.Prelude
open import Tait.Syntax
open import Tait.Context
open import Tait.Substitution
open import Tait.Evaluation
open import Tait.Derivability
open import Tait.Presupposition
open import Tait.Minimal
open import Tait.Inversion

noMinimalEqTerm :
  {gamma : Ctx} {A T : RawType} {a : RawTerm}
  -> Minimal (hasTy gamma (tmEq A a) T)
  -> ⊥
noMinimalEqTerm (minConv d _) = noMinimalEqTerm d

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
