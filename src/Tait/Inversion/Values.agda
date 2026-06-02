{-# OPTIONS --safe #-}

module Tait.Inversion.Values where

open import Data.Empty using (⊥)
open import Data.List.Base using ([] ; _∷_)
open import Data.Unit using (⊤)

open import Tait.Prelude
open import Tait.Syntax
open import Tait.Context
open import Tait.Substitution
open import Tait.Derivability
open import Tait.Presupposition
open import Tait.Minimal

open import Tait.Inversion.Base public
open import Tait.Inversion.TypeEq public
open import Tait.Inversion.Elim public
record PairPremises
    (gamma : Ctx) (a b : RawTerm) (T : RawType) : Type where
  constructor pairPremises
  field
    A : RawType
    B : RawType
    fstTy : Derivable (hasTy gamma a A)
    sndTy : Derivable (hasTy gamma b (subTy (singleSubst a) B))
    sigmaTy : Derivable (isType gamma (tySigma A B))
    targetEq : Derivable (typeEq gamma (tySigma A B) T)

open PairPremises public

record PairAtSigmaPremises
    (gamma : Ctx) (a b : RawTerm) (A B : RawType) : Type where
  constructor pairAtSigmaPremises
  field
    pairFstTy : Derivable (hasTy gamma a A)
    pairSndTy : Derivable (hasTy gamma b (subTy (singleSubst a) B))
    pairSigmaTy : Derivable (isType gamma (tySigma A B))

open PairAtSigmaPremises public

pairPremisesTyping :
  {gamma : Ctx} {a b : RawTerm} {T : RawType}
  -> (prem : PairPremises gamma a b T)
  -> Derivable (hasTy gamma (tmPair a b) (tySigma (A prem) (B prem)))
pairPremisesTyping prem =
  iSigma (fstTy prem) (sndTy prem) (sigmaTy prem)

pairPremisesTypedAtTarget :
  {gamma : Ctx} {a b : RawTerm} {T : RawType}
  -> (prem : PairPremises gamma a b T)
  -> Derivable (hasTy gamma (tmPair a b) T)
pairPremisesTypedAtTarget prem =
  conv (pairPremisesTyping prem) (targetEq prem)

pairPremisesConv :
  {gamma : Ctx} {a b : RawTerm} {S T : RawType}
  -> PairPremises gamma a b S
  -> Derivable (typeEq gamma S T)
  -> PairPremises gamma a b T
pairPremisesConv prem dST =
  pairPremises
    (A prem)
    (B prem)
    (fstTy prem)
    (sndTy prem)
    (sigmaTy prem)
    (transTy (targetEq prem) dST)

pairPremisesAtSigma :
  {gamma : Ctx} {a b : RawTerm} {A B : RawType}
  -> PairPremises gamma a b (tySigma A B)
  -> PairAtSigmaPremises gamma a b A B
pairPremisesAtSigma prem =
  pairAtSigmaPremises
    da
    db
    (sigmaRightTy sigmaEq)
  where
  sigmaEq = invSigmaEq (targetEq prem)

  da : Derivable (hasTy _ _ _)
  da = conv (fstTy prem) (sigmaLeftEq sigmaEq)

  dBSub : Derivable (typeEq _ _ _)
  dBSub = singleSubstTyEqHelper (sigmaFamilyEq sigmaEq) (fstTy prem)

  db : Derivable (hasTy _ _ _)
  db = conv (sndTy prem) dBSub

invMinimalPair :
  {gamma : Ctx} {a b : RawTerm} {T : RawType}
  -> Minimal (hasTy gamma (tmPair a b) T)
  -> PairPremises gamma a b T
invMinimalPair (minConv d dST) =
  pairPremisesConv (invMinimalPair d) (minimalToDerivable dST)
invMinimalPair (minISigma {A = A} {B = B} da db dSigma) =
  pairPremises
    A
    B
    (minimalToDerivable da)
    (minimalToDerivable db)
    (minimalToDerivable dSigma)
    (reflTy (minimalToDerivable dSigma))

record ClassPremises
    (gamma : Ctx) (a : RawTerm) (T : RawType) : Type where
  constructor classPremises
  field
    A : RawType
    repTy : Derivable (hasTy gamma a A)
    targetEq : Derivable (typeEq gamma (tyQtr A) T)

open ClassPremises public

record ClassAtQtrPremises
    (gamma : Ctx) (a : RawTerm) (A : RawType) : Type where
  constructor classAtQtrPremises
  field
    classRepTy : Derivable (hasTy gamma a A)

open ClassAtQtrPremises public

classPremisesTyping :
  {gamma : Ctx} {a : RawTerm} {T : RawType}
  -> (prem : ClassPremises gamma a T)
  -> Derivable (hasTy gamma (tmClass a) (tyQtr (A prem)))
classPremisesTyping prem =
  iQtr (repTy prem)

classPremisesTypedAtTarget :
  {gamma : Ctx} {a : RawTerm} {T : RawType}
  -> (prem : ClassPremises gamma a T)
  -> Derivable (hasTy gamma (tmClass a) T)
classPremisesTypedAtTarget prem =
  conv (classPremisesTyping prem) (targetEq prem)

classPremisesConv :
  {gamma : Ctx} {a : RawTerm} {S T : RawType}
  -> ClassPremises gamma a S
  -> Derivable (typeEq gamma S T)
  -> ClassPremises gamma a T
classPremisesConv prem dST =
  classPremises
    (A prem)
    (repTy prem)
    (transTy (targetEq prem) dST)

classPremisesAtQtr :
  {gamma : Ctx} {a : RawTerm} {A : RawType}
  -> ClassPremises gamma a (tyQtr A)
  -> ClassAtQtrPremises gamma a A
classPremisesAtQtr prem =
  classAtQtrPremises
    (conv (repTy prem) (invQtrEq (targetEq prem)))

invMinimalClass :
  {gamma : Ctx} {a : RawTerm} {T : RawType}
  -> Minimal (hasTy gamma (tmClass a) T)
  -> ClassPremises gamma a T
invMinimalClass (minConv d dST) =
  classPremisesConv (invMinimalClass d) (minimalToDerivable dST)
invMinimalClass (minIQtr {A = A} da) =
  classPremises
    A
    (minimalToDerivable da)
    (reflTy (fQtr (assocTy (minimalToDerivable da))))

record StarPremises (gamma : Ctx) (T : RawType) : Type where
  constructor starPremises
  field
    targetEq : Derivable (typeEq gamma tyTop T)

open StarPremises public

starPremisesTyping :
  {gamma : Ctx} {T : RawType}
  -> (prem : StarPremises gamma T)
  -> Derivable (hasTy gamma tmStar tyTop)
starPremisesTyping {gamma = gamma} prem =
  iTop (derivToCtxWF (assocTyRight (targetEq prem)))

starPremisesTypedAtTarget :
  {gamma : Ctx} {T : RawType}
  -> (prem : StarPremises gamma T)
  -> Derivable (hasTy gamma tmStar T)
starPremisesTypedAtTarget prem =
  conv (starPremisesTyping prem) (targetEq prem)

starPremisesConv :
  {gamma : Ctx} {S T : RawType}
  -> StarPremises gamma S
  -> Derivable (typeEq gamma S T)
  -> StarPremises gamma T
starPremisesConv prem dST =
  starPremises (transTy (targetEq prem) dST)

invMinimalStar :
  {gamma : Ctx} {T : RawType}
  -> Minimal (hasTy gamma tmStar T)
  -> StarPremises gamma T
invMinimalStar (minConv d dST) =
  starPremisesConv (invMinimalStar d) (minimalToDerivable dST)
invMinimalStar (minITop wf) =
  starPremises (reflTy (fTop (minCtxWFToCtxWF wf)))

record ReflPremises (gamma : Ctx) (T : RawType) : Type where
  constructor reflPremises
  field
    A : RawType
    a : RawTerm
    selfTy : Derivable (hasTy gamma a A)
    targetEq : Derivable (typeEq gamma (tyEq A a a) T)

open ReflPremises public

reflPremisesTyping :
  {gamma : Ctx} {T : RawType}
  -> (prem : ReflPremises gamma T)
  -> Derivable (hasTy gamma tmRefl (tyEq (A prem) (a prem) (a prem)))
reflPremisesTyping prem =
  iEq (selfTy prem)

reflPremisesTypedAtTarget :
  {gamma : Ctx} {T : RawType}
  -> (prem : ReflPremises gamma T)
  -> Derivable (hasTy gamma tmRefl T)
reflPremisesTypedAtTarget prem =
  conv (reflPremisesTyping prem) (targetEq prem)

reflPremisesConv :
  {gamma : Ctx} {S T : RawType}
  -> ReflPremises gamma S
  -> Derivable (typeEq gamma S T)
  -> ReflPremises gamma T
reflPremisesConv prem dST =
  reflPremises
    (A prem)
    (a prem)
    (selfTy prem)
    (transTy (targetEq prem) dST)

invMinimalRefl :
  {gamma : Ctx} {T : RawType}
  -> Minimal (hasTy gamma tmRefl T)
  -> ReflPremises gamma T
invMinimalRefl (minConv d dST) =
  reflPremisesConv (invMinimalRefl d) (minimalToDerivable dST)
invMinimalRefl (minIEq {A = A} {a = a} da) =
  reflPremises
    A
    a
    (minimalToDerivable da)
    (reflTy (fEq (assocTy (minimalToDerivable da)) (minimalToDerivable da) (minimalToDerivable da)))

record SigmaTyPremises (gamma : Ctx) (A B : RawType) : Type where
  constructor sigmaTyPremises
  field
    leftTy : Derivable (isType gamma A)
    familyTy : Derivable (isType (A ∷ gamma) B)

open SigmaTyPremises public

invMinimalSigmaTy :
  {gamma : Ctx} {A B : RawType}
  -> Minimal (isType gamma (tySigma A B))
  -> SigmaTyPremises gamma A B
invMinimalSigmaTy (minFSigma dA dB) =
  sigmaTyPremises (minimalToDerivable dA) (minimalToDerivable dB)

record EqTyPremises (gamma : Ctx) (A : RawType) (a b : RawTerm) : Type where
  constructor eqTyPremises
  field
    typeTy : Derivable (isType gamma A)
    leftTm : Derivable (hasTy gamma a A)
    rightTm : Derivable (hasTy gamma b A)

open EqTyPremises public

invMinimalEqTy :
  {gamma : Ctx} {A : RawType} {a b : RawTerm}
  -> Minimal (isType gamma (tyEq A a b))
  -> EqTyPremises gamma A a b
invMinimalEqTy (minFEq dA da db) =
  eqTyPremises (minimalToDerivable dA) (minimalToDerivable da) (minimalToDerivable db)

record QtrTyPremises (gamma : Ctx) (A : RawType) : Type where
  constructor qtrTyPremises
  field
    innerTy : Derivable (isType gamma A)

open QtrTyPremises public

invMinimalQtrTy :
  {gamma : Ctx} {A : RawType}
  -> Minimal (isType gamma (tyQtr A))
  -> QtrTyPremises gamma A
invMinimalQtrTy (minFQtr dA) =
  qtrTyPremises (minimalToDerivable dA)

invQtrHead :
  {gamma : Ctx} {l p : RawTerm} {T : RawType}
  -> Derivable (hasTy gamma (tmElQtr l p) T)
  -> QtrElimPremises gamma l p T
invQtrHead d =
  invMinimalQtrHead (derivableToMinimal d)

invSigmaHead :
  {gamma : Ctx} {d m : RawTerm} {T : RawType}
  -> Derivable (hasTy gamma (tmElSigma d m) T)
  -> SigmaElimPremises gamma d m T
invSigmaHead d =
  invMinimalSigmaHead (derivableToMinimal d)

invPair :
  {gamma : Ctx} {a b : RawTerm} {T : RawType}
  -> Derivable (hasTy gamma (tmPair a b) T)
  -> PairPremises gamma a b T
invPair d =
  invMinimalPair (derivableToMinimal d)

invPairAtSigma :
  {gamma : Ctx} {a b : RawTerm} {A B : RawType}
  -> Derivable (hasTy gamma (tmPair a b) (tySigma A B))
  -> PairAtSigmaPremises gamma a b A B
invPairAtSigma d =
  pairPremisesAtSigma (invPair d)

invClass :
  {gamma : Ctx} {a : RawTerm} {T : RawType}
  -> Derivable (hasTy gamma (tmClass a) T)
  -> ClassPremises gamma a T
invClass d =
  invMinimalClass (derivableToMinimal d)

invClassAtQtr :
  {gamma : Ctx} {a : RawTerm} {A : RawType}
  -> Derivable (hasTy gamma (tmClass a) (tyQtr A))
  -> ClassAtQtrPremises gamma a A
invClassAtQtr d =
  classPremisesAtQtr (invClass d)

invStar :
  {gamma : Ctx} {T : RawType}
  -> Derivable (hasTy gamma tmStar T)
  -> StarPremises gamma T
invStar d =
  invMinimalStar (derivableToMinimal d)

invRefl :
  {gamma : Ctx} {T : RawType}
  -> Derivable (hasTy gamma tmRefl T)
  -> ReflPremises gamma T
invRefl d =
  invMinimalRefl (derivableToMinimal d)

invSigmaTy :
  {gamma : Ctx} {A B : RawType}
  -> Derivable (isType gamma (tySigma A B))
  -> SigmaTyPremises gamma A B
invSigmaTy d =
  invMinimalSigmaTy (derivableToMinimal d)

invEqTy :
  {gamma : Ctx} {A : RawType} {a b : RawTerm}
  -> Derivable (isType gamma (tyEq A a b))
  -> EqTyPremises gamma A a b
invEqTy d =
  invMinimalEqTy (derivableToMinimal d)

invQtrTy :
  {gamma : Ctx} {A : RawType}
  -> Derivable (isType gamma (tyQtr A))
  -> QtrTyPremises gamma A
invQtrTy d =
  invMinimalQtrTy (derivableToMinimal d)
