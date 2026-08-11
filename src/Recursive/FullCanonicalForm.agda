{-# OPTIONS --safe #-}

module Recursive.FullCanonicalForm where

open import Data.List.Base using ([] ; _∷_)
open import Data.Nat using (_<_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wf)
open import Data.Product using (_×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Induction.WellFounded using (Acc ; acc)

open import Recursive.Prelude
open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Evaluation
open import Recursive.Derivability
open import Recursive.Presupposition
open import Recursive.Inversion
open import Recursive.Minimal using (derivableToMinimal)
open import Recursive.Computable
open import Recursive.Fundamental
open import Recursive.EvalSound
open import Recursive.CanonicalForm using (typeEval)
open import Recursive.Measure

data CanonicalTy : RawType -> Type where
  canTopTy :
    CanonicalTy tyTop

  canSigmaTy : {A B : RawType}
    -> Derivable (isType [] A)
    -> Derivable (isType (A ∷ []) B)
    -> CanonicalTy (tySigma A B)

  canEqTy : {A : RawType} {a b : RawTerm}
    -> Derivable (isType [] A)
    -> Derivable (hasTy [] a A)
    -> Derivable (hasTy [] b A)
    -> CanonicalTy (tyEq A a b)

  canQtrTy : {A : RawType}
    -> Derivable (isType [] A)
    -> CanonicalTy (tyQtr A)

  canNatTy :
    CanonicalTy tyNat

canonicalTyDerivable : {G : RawType} -> CanonicalTy G -> Derivable (isType [] G)
canonicalTyDerivable canTopTy =
  fTop wfNil
canonicalTyDerivable (canSigmaTy dA dB) =
  fSigma dA dB
canonicalTyDerivable (canEqTy dA da db) =
  fEq dA da db
canonicalTyDerivable (canQtrTy dA) =
  fQtr dA
canonicalTyDerivable canNatTy =
  fNat wfNil

canonicalTyFromDerivable : {G : RawType}
  -> Derivable (isType [] G)
  -> CanonicalTy G
canonicalTyFromDerivable {G = tyTop} d =
  canTopTy
canonicalTyFromDerivable {G = tySigma A B} d =
  canSigmaTy (leftTy prem) (familyTy prem)
  where
  prem = invSigmaTy d
canonicalTyFromDerivable {G = tyEq A a b} d =
  canEqTy (typeTy prem) (leftTm prem) (rightTm prem)
  where
  prem = invEqTy d
canonicalTyFromDerivable {G = tyQtr A} d =
  canQtrTy (innerTy prem)
  where
  prem = invQtrTy d
canonicalTyFromDerivable {G = tyNat} d =
  canNatTy

data CanonicalTyEq : RawType -> RawType -> Type where
  canTopTyEq :
    CanonicalTyEq tyTop tyTop

  canSigmaTyEq : {A B C D : RawType}
    -> Derivable (typeEq [] A C)
    -> Derivable (isType (A ∷ []) B)
    -> Derivable (typeEq (A ∷ []) B D)
    -> CanonicalTyEq (tySigma A B) (tySigma C D)

  canEqTyEq : {A C : RawType} {a b c d : RawTerm}
    -> Derivable (typeEq [] A C)
    -> Derivable (termEq [] a c A)
    -> Derivable (termEq [] b d A)
    -> CanonicalTyEq (tyEq A a b) (tyEq C c d)

  canQtrTyEq : {A B : RawType}
    -> Derivable (typeEq [] A B)
    -> CanonicalTyEq (tyQtr A) (tyQtr B)

  canNatTyEq :
    CanonicalTyEq tyNat tyNat

canonicalTyEqDerivable :
  {G H : RawType} -> CanonicalTyEq G H -> Derivable (typeEq [] G H)
canonicalTyEqDerivable canTopTyEq =
  reflTy (fTop wfNil)
canonicalTyEqDerivable (canSigmaTyEq dAC dB dBD) =
  fSigmaEq dAC dB dBD
canonicalTyEqDerivable (canEqTyEq dAC dac dbd) =
  fEqEq dAC dac dbd
canonicalTyEqDerivable (canQtrTyEq dAB) =
  fQtrEq dAB
canonicalTyEqDerivable canNatTyEq =
  reflTy (fNat wfNil)

canonicalTyEqFromDerivable : {G H : RawType}
  -> Derivable (typeEq [] G H)
  -> CanonicalTyEq G H
canonicalTyEqFromDerivable {G = tyTop} {H = tyTop} d =
  canTopTyEq
canonicalTyEqFromDerivable {G = tyTop} {H = tySigma _ _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyTop} {H = tyEq _ _ _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyTop} {H = tyQtr _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyTop} {H = tyNat} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tySigma A B} {H = tyTop} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tySigma A B} {H = tySigma C D} d =
  canSigmaTyEq
    (sigmaLeftEq prem)
    (sigmaLeftFamilyTy prem)
    (sigmaFamilyEq prem)
  where
  prem = invSigmaEq d
canonicalTyEqFromDerivable {G = tySigma _ _} {H = tyEq _ _ _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tySigma _ _} {H = tyQtr _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tySigma _ _} {H = tyNat} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyEq _ _ _} {H = tyTop} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyEq _ _ _} {H = tySigma _ _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyEq A a b} {H = tyEq C c e} d =
  canEqTyEq
    (eqTypeEq prem)
    (eqLeftTmEq prem)
    (eqRightTmEq prem)
  where
  prem = invEqEq d
canonicalTyEqFromDerivable {G = tyEq _ _ _} {H = tyQtr _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyEq _ _ _} {H = tyNat} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyQtr _} {H = tyTop} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyQtr _} {H = tySigma _ _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyQtr _} {H = tyEq _ _ _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyQtr A} {H = tyQtr B} d =
  canQtrTyEq (invQtrEq d)
canonicalTyEqFromDerivable {G = tyQtr _} {H = tyNat} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyNat} {H = tyTop} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyNat} {H = tySigma _ _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyNat} {H = tyEq _ _ _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyNat} {H = tyQtr _} d
  with minimalTyEqHead (derivableToMinimal d)
... | ()
canonicalTyEqFromDerivable {G = tyNat} {H = tyNat} d =
  canNatTyEq

data CanonicalTm : RawTerm -> RawType -> Type where
  canStarTm :
    CanonicalTm tmStar tyTop

  canPairTm : {A B : RawType} {a b : RawTerm}
    -> Derivable (hasTy [] a A)
    -> Derivable (hasTy [] b (subTy (singleSubst a) B))
    -> Derivable (isType [] (tySigma A B))
    -> CanonicalTm (tmPair a b) (tySigma A B)

  canReflTm : {A : RawType} {a b : RawTerm}
    -> Derivable (termEq [] a b A)
    -> CanonicalTm tmRefl (tyEq A a b)

  canClassTm : {A : RawType} {a : RawTerm}
    -> Derivable (hasTy [] a A)
    -> CanonicalTm (tmClass a) (tyQtr A)

  canZeroTm :
    CanonicalTm tmZero tyNat

  canSucTm : {n : RawTerm}
    -> Derivable (hasTy [] n tyNat)
    -> CanonicalTm (tmSuc n) tyNat

canonicalTmDerivable :
  {g : RawTerm} {G : RawType} -> CanonicalTm g G -> Derivable (hasTy [] g G)
canonicalTmDerivable canStarTm =
  iTop wfNil
canonicalTmDerivable (canPairTm da db dSigma) =
  iSigma da db dSigma
canonicalTmDerivable (canReflTm d) =
  let
    da = assocTmLeft d
    dA = assocTmTy d
  in
  conv (iEq da) (fEqEq (reflTy dA) (reflTm da) d)
canonicalTmDerivable (canClassTm da) =
  iQtr da
canonicalTmDerivable canZeroTm =
  iZero wfNil
canonicalTmDerivable (canSucTm dn) =
  iSuc dn

data CanonicalTmEq : RawTerm -> RawTerm -> RawType -> Type where
  canStarTmEq :
    CanonicalTmEq tmStar tmStar tyTop

  canPairTmEq : {A B : RawType} {a b c d : RawTerm}
    -> Derivable (termEq [] a c A)
    -> Derivable (termEq [] b d (subTy (singleSubst a) B))
    -> Derivable (isType [] A)
    -> Derivable (isType (A ∷ []) B)
    -> CanonicalTmEq (tmPair a b) (tmPair c d) (tySigma A B)

  canReflTmEq : {A : RawType} {a b : RawTerm}
    -> Derivable (termEq [] a b A)
    -> CanonicalTmEq tmRefl tmRefl (tyEq A a b)

  canClassTmEq : {A : RawType} {a b : RawTerm}
    -> Derivable (hasTy [] a A)
    -> Derivable (hasTy [] b A)
    -> CanonicalTmEq (tmClass a) (tmClass b) (tyQtr A)

  canZeroTmEq :
    CanonicalTmEq tmZero tmZero tyNat

  canSucTmEq : {n n' : RawTerm}
    -> Derivable (termEq [] n n' tyNat)
    -> CanonicalTmEq (tmSuc n) (tmSuc n') tyNat

canonicalTmEqDerivable :
  {g h : RawTerm} {G : RawType}
  -> CanonicalTmEq g h G
  -> Derivable (termEq [] g h G)
canonicalTmEqDerivable canStarTmEq =
  cTop (iTop wfNil)
canonicalTmEqDerivable (canPairTmEq dac dbd dA dB) =
  iSigmaEq dac dbd dA dB
canonicalTmEqDerivable (canReflTmEq d) =
  let
    da = assocTmLeft d
    dA = assocTmTy d
  in
  convEq (iEqEq d) (fEqEq (reflTy dA) (reflTm da) d)
canonicalTmEqDerivable (canClassTmEq da db) =
  iQtrEq da db
canonicalTmEqDerivable canZeroTmEq =
  reflTm (iZero wfNil)
canonicalTmEqDerivable (canSucTmEq dnn') =
  iSucEq dnn'

canonicalNatEqDerivable :
  {t u : RawTerm}
  -> Derivable (hasTy [] t tyNat)
  -> Derivable (hasTy [] u tyNat)
  -> CanonicalNatEq t u
  -> Derivable (termEq [] t u tyNat)
canonicalNatEqDerivable dt du (cZeroVEq evt evu) =
  transTm leftEq (symTm rightEq rightValueTy dNat)
  where
  leftSound = evalSoundTm dt evt
  rightSound = evalSoundTm du evu

  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
  rightValueTy = proj₁ rightSound
  dNat = fNat wfNil
canonicalNatEqDerivable dt du (cSucVEq {k = k} {k' = k'} evt evu eqK) =
  transTm leftEq (transTm sucEq (symTm rightEq rightValueTy dNat))
  where
  leftSound = evalSoundTm dt evt
  rightSound = evalSoundTm du evu

  leftValueTy = proj₁ leftSound
  rightValueTy = proj₁ rightSound
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
  dNat = fNat wfNil

  leftPredTy : Derivable (hasTy [] k tyNat)
  leftPredTy =
    invSucAtNat leftValueTy

  rightPredTy : Derivable (hasTy [] k' tyNat)
  rightPredTy =
    invSucAtNat rightValueTy

  predEq : Derivable (termEq [] k k' tyNat)
  predEq =
    canonicalNatEqDerivable leftPredTy rightPredTy eqK

  sucEq : Derivable (termEq [] (tmSuc k) (tmSuc k') tyNat)
  sucEq =
    iSucEq predEq

computableTmEqDerivableAcc :
  (A : RawType)
  -> (p : Acc _<_ (tyDepth A))
  -> {t u : RawTerm}
  -> Derivable (hasTy [] t A)
  -> Derivable (hasTy [] u A)
  -> ComputableTmEqAcc A p t u
  -> Derivable (termEq [] t u A)
computableTmEqDerivableAcc tyTop _ dt du (evt , evu) =
  transTm leftEq (symTm rightEq rightValueTy dTop)
  where
  leftSound = evalSoundTm dt evt
  rightSound = evalSoundTm du evu

  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
  rightValueTy = assocTmRight rightEq
  dTop = assocTmTy rightEq
computableTmEqDerivableAcc (tySigma A B) (acc rs) dt du
    (a , b , c , d , evt , evu , eqA , eqB , _) =
  transTm leftEq (transTm pairEq (symTm rightEq rightValueTy dSigma))
  where
  leftSound = evalSoundTm dt evt
  rightSound = evalSoundTm du evu

  leftValueTy = proj₁ leftSound
  rightValueTy = proj₁ rightSound
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound

  leftPair = invPairAtSigma leftValueTy
  rightPair = invPairAtSigma rightValueTy

  sigmaPrem = invSigmaTy (assocTy dt)
  dA = leftTy sigmaPrem
  dB = familyTy sigmaPrem
  dSigma = assocTy dt

  dac : Derivable (termEq [] a c A)
  dac =
    computableTmEqDerivableAcc A
      (rs (tyDepth-fst<Sigma A B))
      (pairFstTy leftPair)
      (pairFstTy rightPair)
      eqA

  leftFiberTy : Derivable (isType [] (subTy (singleSubst a) B))
  leftFiberTy =
    singleSubstTyHelper dB (pairFstTy leftPair)

  rightFiberTy : Derivable (isType [] (subTy (singleSubst c) B))
  rightFiberTy =
    singleSubstTyHelper dB (pairFstTy rightPair)

  fiberEq : Derivable
    (typeEq []
      (subTy (singleSubst a) B)
      (subTy (singleSubst c) B))
  fiberEq =
    singleEqSubstTyHelper dB dac

  rightSndAtLeft : Derivable (hasTy [] d (subTy (singleSubst a) B))
  rightSndAtLeft =
    conv (pairSndTy rightPair) (symTy fiberEq rightFiberTy)

  dbd : Derivable (termEq [] b d (subTy (singleSubst a) B))
  dbd =
    computableTmEqDerivableAcc (subTy (singleSubst a) B)
      (rs (subTy-snd< A B a))
      (pairSndTy leftPair)
      rightSndAtLeft
      eqB

  pairEq : Derivable (termEq [] (tmPair a b) (tmPair c d) (tySigma A B))
  pairEq =
    iSigmaEq dac dbd dA dB
computableTmEqDerivableAcc (tyEq A a b) (acc rs) dt du (evt , evu , eqab) =
  transTm leftEq (transTm reflEq (symTm rightEq rightValueTy dEq))
  where
  leftSound = evalSoundTm dt evt
  rightSound = evalSoundTm du evu

  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
  rightValueTy = assocTmRight rightEq
  dEq = assocTy dt

  eqPrem = invEqTy dEq

  boundaryEq : Derivable (termEq [] a b A)
  boundaryEq =
    computableTmEqDerivableAcc A
      (rs (tyDepth-base<Eq A a b))
      (leftTm eqPrem)
      (rightTm eqPrem)
      eqab

  reflEq : Derivable (termEq [] tmRefl tmRefl (tyEq A a b))
  reflEq =
    convEq
      (iEqEq boundaryEq)
      (fEqEq
        (reflTy (typeTy eqPrem))
        (reflTm (leftTm eqPrem))
        boundaryEq)
computableTmEqDerivableAcc (tyQtr A) (acc rs) dt du
    (p , q , evt , evu , _ , _) =
  transTm leftEq (transTm classEq (symTm rightEq rightValueTy dQtr))
  where
  leftSound = evalSoundTm dt evt
  rightSound = evalSoundTm du evu

  leftValueTy = proj₁ leftSound
  rightValueTy = proj₁ rightSound
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
  dQtr = assocTy dt

  leftClass = invClassAtQtr leftValueTy
  rightClass = invClassAtQtr rightValueTy

  classEq : Derivable (termEq [] (tmClass p) (tmClass q) (tyQtr A))
  classEq =
    iQtrEq (classRepTy leftClass) (classRepTy rightClass)
computableTmEqDerivableAcc tyNat _ dt du eq =
  canonicalNatEqDerivable dt du eq

computableTmEqDerivable :
  {A : RawType} {t u : RawTerm}
  -> Derivable (hasTy [] t A)
  -> Derivable (hasTy [] u A)
  -> ComputableTmEq A t u
  -> Derivable (termEq [] t u A)
computableTmEqDerivable {A = A} =
  computableTmEqDerivableAcc A (<-wf (tyDepth A))

FullCanonicalForm : JForm -> Type
FullCanonicalForm (isType [] A) =
  Σ[ G ∈ RawType ]
    (A =>t G) ×
    CanonicalTy G ×
    Derivable (typeEq [] A G)
FullCanonicalForm (hasTy [] t A) =
  Σ[ g ∈ RawTerm ] Σ[ G ∈ RawType ]
    (t =>e g) ×
    (A =>t G) ×
    CanonicalTm g G ×
    Derivable (termEq [] t g A) ×
    Derivable (typeEq [] A G)
FullCanonicalForm (typeEq [] A B) =
  Σ[ G ∈ RawType ] Σ[ H ∈ RawType ]
    (A =>t G) ×
    (B =>t H) ×
    CanonicalTyEq G H ×
    Derivable (typeEq [] A G) ×
    Derivable (typeEq [] B H)
FullCanonicalForm (termEq [] t u A) =
  Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] Σ[ G ∈ RawType ]
    (t =>e g) ×
    (u =>e h) ×
    (A =>t G) ×
    CanonicalTmEq g h G ×
    Derivable (termEq [] t g A) ×
    Derivable (termEq [] u h A) ×
    Derivable (typeEq [] A G)
FullCanonicalForm _ = ⊤

fullCanonicalType :
  {A : RawType}
  -> Derivable (isType [] A)
  -> FullCanonicalForm (isType [] A)
fullCanonicalType {A = A} d =
  A , typeEval A , canonicalTyFromDerivable d , reflTy d

fullCanonicalTerm :
  {t : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t A)
  -> FullCanonicalForm (hasTy [] t A)
fullCanonicalTerm {A = tyTop} d =
  tmStar , tyTop ,
    ev ,
    evalTop ,
    canStarTm ,
    soundEq ,
    reflTy (assocTy d)
  where
  ev = fundTmClosed d
  sound = evalSoundTm d ev
  soundEq = proj₂ sound
fullCanonicalTerm {A = tySigma A B} d with computableSigma-elim (fundTmClosed d)
... | a , b , ev , _ , _ =
  tmPair a b , tySigma A B ,
    ev ,
    evalSigma ,
    canPairTm (pairFstTy pairPrem) (pairSndTy pairPrem) (pairSigmaTy pairPrem) ,
    soundEq ,
    reflTy (assocTy d)
  where
  sound = evalSoundTm d ev
  soundTy = proj₁ sound
  soundEq = proj₂ sound
  pairPrem = invPairAtSigma soundTy
fullCanonicalTerm {A = tyEq A a b} d with computableEq-elim (fundTmClosed d)
... | ev , _ =
  tmRefl , tyEq A a b ,
    ev ,
    evalEq ,
    canReflTm boundaryEq ,
    soundEq ,
    reflTy (assocTy d)
  where
  sound = evalSoundTm d ev
  soundEq = proj₂ sound
  eqTyPrem = invEqTy (assocTy d)
  boundaryEq = eEqStar d (typeTy eqTyPrem) (leftTm eqTyPrem) (rightTm eqTyPrem)
fullCanonicalTerm {A = tyQtr A} d with computableQtr-elim (fundTmClosed d)
... | a , ev , _ =
  tmClass a , tyQtr A ,
    ev ,
    evalQtr ,
    canClassTm (classRepTy classPrem) ,
    soundEq ,
    reflTy (assocTy d)
  where
  sound = evalSoundTm d ev
  soundTy = proj₁ sound
  soundEq = proj₂ sound
  classPrem = invClassAtQtr soundTy
fullCanonicalTerm {A = tyNat} d with fundTmClosed d
... | cZeroV ev =
  tmZero , tyNat ,
    ev ,
    evalNat ,
    canZeroTm ,
    soundEq ,
    reflTy (assocTy d)
  where
  sound = evalSoundTm d ev
  soundEq = proj₂ sound
... | cSucV {k = k} ev _ =
  tmSuc k , tyNat ,
    ev ,
    evalNat ,
    canSucTm predTy ,
    soundEq ,
    reflTy (assocTy d)
  where
  sound = evalSoundTm d ev
  soundTy = proj₁ sound
  soundEq = proj₂ sound

  predTy : Derivable (hasTy [] k tyNat)
  predTy =
    invSucAtNat soundTy

fullCanonicalTypeEq :
  {A B : RawType}
  -> Derivable (typeEq [] A B)
  -> FullCanonicalForm (typeEq [] A B)
fullCanonicalTypeEq {A = A} {B = B} d =
  A , B ,
    typeEval A ,
    typeEval B ,
    canonicalTyEqFromDerivable d ,
    reflTy (assocTyLeft d) ,
    reflTy (assocTyRight d)

fullCanonicalTermEq :
  {t u : RawTerm} {A : RawType}
  -> Derivable (termEq [] t u A)
  -> FullCanonicalForm (termEq [] t u A)
fullCanonicalTermEq {A = tyTop} d =
  tmStar , tmStar , tyTop ,
    evt ,
    evu ,
    evalTop ,
    canStarTmEq ,
    leftEq ,
    rightEq ,
    reflTy (assocTmTy d)
  where
  evs = fundTmEqClosed d
  evt = proj₁ evs
  evu = proj₂ evs
  leftSound = evalSoundTm (assocTmLeft d) evt
  rightSound = evalSoundTm (assocTmRight d) evu
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
fullCanonicalTermEq {A = tySigma A B} d with computableTmEqSigma-elim (fundTmEqClosed d)
... | a , b , c , e , evt , evu , eqA , eqB , _ =
  tmPair a b , tmPair c e , tySigma A B ,
    evt ,
    evu ,
    evalSigma ,
    canPairTmEq dac dbd dA dB ,
    leftEq ,
    rightEq ,
    reflTy (assocTmTy d)
  where
  leftSound = evalSoundTm (assocTmLeft d) evt
  rightSound = evalSoundTm (assocTmRight d) evu
  leftTyDeriv = proj₁ leftSound
  rightTyDeriv = proj₁ rightSound
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
  leftPair = invPairAtSigma leftTyDeriv
  rightPair = invPairAtSigma rightTyDeriv
  sigmaPrem = invSigmaTy (assocTmTy d)
  dA = leftTy sigmaPrem
  dB = familyTy sigmaPrem

  dac : Derivable (termEq [] a c A)
  dac =
    computableTmEqDerivable
      (pairFstTy leftPair)
      (pairFstTy rightPair)
      eqA

  leftFiberTy : Derivable (isType [] (subTy (singleSubst a) B))
  leftFiberTy =
    singleSubstTyHelper dB (pairFstTy leftPair)

  rightFiberTy : Derivable (isType [] (subTy (singleSubst c) B))
  rightFiberTy =
    singleSubstTyHelper dB (pairFstTy rightPair)

  fiberEq : Derivable
    (typeEq []
      (subTy (singleSubst a) B)
      (subTy (singleSubst c) B))
  fiberEq =
    singleEqSubstTyHelper dB dac

  rightSndAtLeft : Derivable (hasTy [] e (subTy (singleSubst a) B))
  rightSndAtLeft =
    conv (pairSndTy rightPair) (symTy fiberEq rightFiberTy)

  dbd : Derivable (termEq [] b e (subTy (singleSubst a) B))
  dbd =
    computableTmEqDerivable
      (pairSndTy leftPair)
      rightSndAtLeft
      eqB
fullCanonicalTermEq {A = tyEq A a b} d with computableTmEqEqForm-elim (fundTmEqClosed d)
... | evt , evu , _ =
  tmRefl , tmRefl , tyEq A a b ,
    evt ,
    evu ,
    evalEq ,
    canReflTmEq boundaryEq ,
    leftEq ,
    rightEq ,
    reflTy (assocTmTy d)
  where
  leftSound = evalSoundTm (assocTmLeft d) evt
  rightSound = evalSoundTm (assocTmRight d) evu
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
  eqTyPrem = invEqTy (assocTmTy d)
  boundaryEq =
    eEqStar (assocTmLeft d) (typeTy eqTyPrem) (leftTm eqTyPrem) (rightTm eqTyPrem)
fullCanonicalTermEq {A = tyQtr A} d with computableTmEqQtr-elim (fundTmEqClosed d)
... | a , b , evt , evu , _ , _ =
  tmClass a , tmClass b , tyQtr A ,
    evt ,
    evu ,
    evalQtr ,
    canClassTmEq (classRepTy leftClass) (classRepTy rightClass) ,
    leftEq ,
    rightEq ,
    reflTy (assocTmTy d)
  where
  leftSound = evalSoundTm (assocTmLeft d) evt
  rightSound = evalSoundTm (assocTmRight d) evu
  leftTyDeriv = proj₁ leftSound
  rightTyDeriv = proj₁ rightSound
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
  leftClass = invClassAtQtr leftTyDeriv
  rightClass = invClassAtQtr rightTyDeriv
fullCanonicalTermEq {A = tyNat} d with fundTmEqClosed d
... | cZeroVEq evt evu =
  tmZero , tmZero , tyNat ,
    evt ,
    evu ,
    evalNat ,
    canZeroTmEq ,
    leftEq ,
    rightEq ,
    reflTy (assocTmTy d)
  where
  leftSound = evalSoundTm (assocTmLeft d) evt
  rightSound = evalSoundTm (assocTmRight d) evu
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound
... | cSucVEq {k = k} {k' = k'} evt evu eqK =
  tmSuc k , tmSuc k' , tyNat ,
    evt ,
    evu ,
    evalNat ,
    canSucTmEq predEq ,
    leftEq ,
    rightEq ,
    reflTy (assocTmTy d)
  where
  leftSound = evalSoundTm (assocTmLeft d) evt
  rightSound = evalSoundTm (assocTmRight d) evu
  leftTyDeriv = proj₁ leftSound
  rightTyDeriv = proj₁ rightSound
  leftEq = proj₂ leftSound
  rightEq = proj₂ rightSound

  leftPredTy : Derivable (hasTy [] k tyNat)
  leftPredTy =
    invSucAtNat leftTyDeriv

  rightPredTy : Derivable (hasTy [] k' tyNat)
  rightPredTy =
    invSucAtNat rightTyDeriv

  predEq : Derivable (termEq [] k k' tyNat)
  predEq =
    canonicalNatEqDerivable leftPredTy rightPredTy eqK

fullCanonicalFormTheorem :
  {J : JForm} -> Derivable J -> FullCanonicalForm J
fullCanonicalFormTheorem {J = isType [] A} d =
  fullCanonicalType d
fullCanonicalFormTheorem {J = hasTy [] t A} d =
  fullCanonicalTerm d
fullCanonicalFormTheorem {J = typeEq [] A B} d =
  fullCanonicalTypeEq d
fullCanonicalFormTheorem {J = termEq [] t u A} d =
  fullCanonicalTermEq d
fullCanonicalFormTheorem {J = isType (_ ∷ _) A} d = tt
fullCanonicalFormTheorem {J = hasTy (_ ∷ _) t A} d = tt
fullCanonicalFormTheorem {J = typeEq (_ ∷ _) A B} d = tt
fullCanonicalFormTheorem {J = termEq (_ ∷ _) t u A} d = tt
