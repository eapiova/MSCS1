{-# OPTIONS --safe #-}

module Recursive.Inversion.TypeEq where

open import Data.Empty using (⊥)
open import Data.List.Base using ([] ; _∷_)
open import Data.Unit using (⊤)

open import Recursive.Prelude
open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Derivability
open import Recursive.Presupposition
open import Recursive.Minimal

open import Recursive.Inversion.Base public
invMinimalQtrEq :
  {gamma : Ctx} {A B : RawType}
  -> Minimal (typeEq gamma (tyQtr A) (tyQtr B))
  -> Derivable (typeEq gamma A B)
invMinimalQtrEq (minReflTy (minFQtr dA)) =
  reflTy (minimalToDerivable dA)
invMinimalQtrEq (minSymTy d dB) =
  symTy (invMinimalQtrEq d) (minimalToDerivable (minQtrInner dB))
invMinimalQtrEq (minTransTy {B = tyTop} d _) with minimalTyEqHead d
... | ()
invMinimalQtrEq (minTransTy {B = tySigma _ _} d _) with minimalTyEqHead d
... | ()
invMinimalQtrEq (minTransTy {B = tyEq _ _ _} d _) with minimalTyEqHead d
... | ()
invMinimalQtrEq (minTransTy {B = tyQtr _} d e) =
  transTy (invMinimalQtrEq d) (invMinimalQtrEq e)
invMinimalQtrEq (minFQtrEq dAB) =
  minimalToDerivable dAB

record SigmaEqPremises
    (gamma : Ctx) (A B C D : RawType) : Type where
  constructor sigmaEqPremises
  field
    sigmaLeftEq : Derivable (typeEq gamma A C)
    sigmaLeftFamilyTy : Derivable (isType (A ∷ gamma) B)
    sigmaFamilyEq : Derivable (typeEq (A ∷ gamma) B D)
    sigmaRightTy : Derivable (isType gamma (tySigma C D))

open SigmaEqPremises public

invMinimalSigmaEq :
  {gamma : Ctx} {A B C D : RawType}
  -> Minimal (typeEq gamma (tySigma A B) (tySigma C D))
  -> SigmaEqPremises gamma A B C D
invMinimalSigmaEq (minReflTy (minFSigma dA dB)) =
  sigmaEqPremises
    (reflTy (minimalToDerivable dA))
    (minimalToDerivable dB)
    (reflTy (minimalToDerivable dB))
    (fSigma (minimalToDerivable dA) (minimalToDerivable dB))
invMinimalSigmaEq (minSymTy d dRight) =
  sigmaEqPremises
    dAC
    dB
    dBD
    dSigmaC
  where
  prem = invMinimalSigmaEq d

  dCA : Derivable (typeEq _ _ _)
  dCA = sigmaLeftEq prem

  dSigmaC : Derivable (isType _ _)
  dSigmaC = assocTyLeft (minimalToDerivable d)

  dA : Derivable (isType _ _)
  dA = assocTyRight dCA

  dAC : Derivable (typeEq _ _ _)
  dAC = symTy dCA dA

  dB : Derivable (isType _ _)
  dB = minimalToDerivable (minSigmaRight dRight)

  dDB : Derivable (typeEq _ _ _)
  dDB = sigmaFamilyEq prem

  dBDInC : Derivable (typeEq _ _ _)
  dBDInC = symTy dDB (assocTyRight dDB)

  dBD : Derivable (typeEq _ _ _)
  dBD = transportFamilyTyEq dCA (assocTyRight dCA) dBDInC
invMinimalSigmaEq (minTransTy {B = tyTop} d _) with minimalTyEqHead d
... | ()
invMinimalSigmaEq (minTransTy {B = tySigma E F} d e) =
  sigmaEqPremises
    dAC
    (sigmaLeftFamilyTy left)
    dBD
    (sigmaRightTy right)
  where
  left = invMinimalSigmaEq d
  right = invMinimalSigmaEq e

  dAE : Derivable (typeEq _ _ _)
  dAE = sigmaLeftEq left

  dEC : Derivable (typeEq _ _ _)
  dEC = sigmaLeftEq right

  dEA : Derivable (typeEq _ _ _)
  dEA = symTy dAE (assocTyRight dAE)

  dAC : Derivable (typeEq _ _ _)
  dAC = transTy dAE dEC

  dFDInA : Derivable (typeEq _ _ _)
  dFDInA = transportFamilyTyEq dEA (assocTyLeft dAE) (sigmaFamilyEq right)

  dBD : Derivable (typeEq _ _ _)
  dBD = transTy (sigmaFamilyEq left) dFDInA
invMinimalSigmaEq (minTransTy {B = tyEq _ _ _} d _) with minimalTyEqHead d
... | ()
invMinimalSigmaEq (minTransTy {B = tyQtr _} d _) with minimalTyEqHead d
... | ()
invMinimalSigmaEq (minFSigmaEq dAC dB dBD dRight) =
  sigmaEqPremises
    (minimalToDerivable dAC)
    (minimalToDerivable dB)
    (minimalToDerivable dBD)
    (minimalToDerivable dRight)

record EqEqPremises
    (gamma : Ctx) (A : RawType) (a b : RawTerm) (C : RawType) (c d : RawTerm) : Type where
  constructor eqEqPremises
  field
    eqTypeEq : Derivable (typeEq gamma A C)
    eqLeftTmEq : Derivable (termEq gamma a c A)
    eqRightTmEq : Derivable (termEq gamma b d A)
    eqRightTy : Derivable (isType gamma (tyEq C c d))

open EqEqPremises public

invMinimalEqEq :
  {gamma : Ctx} {A C : RawType} {a b c d : RawTerm}
  -> Minimal (typeEq gamma (tyEq A a b) (tyEq C c d))
  -> EqEqPremises gamma A a b C c d
invMinimalEqEq (minReflTy (minFEq dA da db)) =
  eqEqPremises
    (reflTy (minimalToDerivable dA))
    (reflTm (minimalToDerivable da))
    (reflTm (minimalToDerivable db))
    (fEq (minimalToDerivable dA) (minimalToDerivable da) (minimalToDerivable db))
invMinimalEqEq (minSymTy d dRight) =
  eqEqPremises
    dAC
    dac
    dbd
    dTyRight
  where
  prem = invMinimalEqEq d

  dCA : Derivable (typeEq _ _ _)
  dCA = eqTypeEq prem

  dA : Derivable (isType _ _)
  dA = assocTyRight dCA

  dAC : Derivable (typeEq _ _ _)
  dAC = symTy dCA dA

  dTyRight : Derivable (isType _ _)
  dTyRight = assocTyLeft (minimalToDerivable d)

  dacAtC : Derivable (termEq _ _ _ _)
  dacAtC =
    symTm
      (eqLeftTmEq prem)
      (assocTmRight (eqLeftTmEq prem))
      (assocTmTy (eqLeftTmEq prem))

  dac : Derivable (termEq _ _ _ _)
  dac = convEq dacAtC dCA

  dbdAtC : Derivable (termEq _ _ _ _)
  dbdAtC =
    symTm
      (eqRightTmEq prem)
      (assocTmRight (eqRightTmEq prem))
      (assocTmTy (eqRightTmEq prem))

  dbd : Derivable (termEq _ _ _ _)
  dbd = convEq dbdAtC dCA
invMinimalEqEq (minTransTy {B = tyTop} d _) with minimalTyEqHead d
... | ()
invMinimalEqEq (minTransTy {B = tySigma _ _} d _) with minimalTyEqHead d
... | ()
invMinimalEqEq (minTransTy {B = tyEq E e f} d e') =
  eqEqPremises
    dAC
    dac
    dbd
    (eqRightTy right)
  where
  left = invMinimalEqEq d
  right = invMinimalEqEq e'

  dAE : Derivable (typeEq _ _ _)
  dAE = eqTypeEq left

  dEC : Derivable (typeEq _ _ _)
  dEC = eqTypeEq right

  dEA : Derivable (typeEq _ _ _)
  dEA = symTy dAE (assocTyRight dAE)

  dAC : Derivable (typeEq _ _ _)
  dAC = transTy dAE dEC

  decAtA : Derivable (termEq _ _ _ _)
  decAtA = convEq (eqLeftTmEq right) dEA

  dac : Derivable (termEq _ _ _ _)
  dac = transTm (eqLeftTmEq left) decAtA

  dfdAtA : Derivable (termEq _ _ _ _)
  dfdAtA = convEq (eqRightTmEq right) dEA

  dbd : Derivable (termEq _ _ _ _)
  dbd = transTm (eqRightTmEq left) dfdAtA
invMinimalEqEq (minTransTy {B = tyQtr _} d _) with minimalTyEqHead d
... | ()
invMinimalEqEq (minFEqEq dAC dac dbd dRight) =
  eqEqPremises
    (minimalToDerivable dAC)
    (minimalToDerivable dac)
    (minimalToDerivable dbd)
    (minimalToDerivable dRight)

invQtrEq :
  {gamma : Ctx} {A B : RawType}
  -> Derivable (typeEq gamma (tyQtr A) (tyQtr B))
  -> Derivable (typeEq gamma A B)
invQtrEq d =
  invMinimalQtrEq (derivableToMinimal d)

invSigmaEq :
  {gamma : Ctx} {A B C D : RawType}
  -> Derivable (typeEq gamma (tySigma A B) (tySigma C D))
  -> SigmaEqPremises gamma A B C D
invSigmaEq d =
  invMinimalSigmaEq (derivableToMinimal d)

invEqEq :
  {gamma : Ctx} {A C : RawType} {a b c d : RawTerm}
  -> Derivable (typeEq gamma (tyEq A a b) (tyEq C c d))
  -> EqEqPremises gamma A a b C c d
invEqEq d =
  invMinimalEqEq (derivableToMinimal d)

singleSubstTyEqHelper : {gamma : Ctx} {A B D : RawType} {t : RawTerm}
  -> Derivable (typeEq (A ∷ gamma) B D)
  -> Derivable (hasTy gamma t A)
  -> Derivable (typeEq gamma (subTy (singleSubst t) B) (subTy (singleSubst t) D))
singleSubstTyEqHelper {gamma = gamma} {B = B} {D = D} {t = t} dBD dt =
  subst (λ T -> Derivable (typeEq gamma T (subTy (singleSubst t) D)))
    (singleSubstCtx-subTy t gamma B)
    (subst (λ T -> Derivable (typeEq gamma (subTy (singleSubstCtx t gamma) B) T))
      (singleSubstCtx-subTy t gamma D)
      (substTyEqRule dBD (singleFitsSubstHelper dt)))
