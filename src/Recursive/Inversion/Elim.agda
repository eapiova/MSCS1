{-# OPTIONS --safe #-}

module Recursive.Inversion.Elim where

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
open import Recursive.Inversion.TypeEq public
record QtrElimPremises (gamma : Ctx) (l p : RawTerm) (T : RawType) : Type where
  constructor qtrElimPremises
  field
    A : RawType
    L : RawType
    motiveTy : Derivable (isType (tyQtr A ∷ gamma) L)
    scrutineeTy : Derivable (hasTy gamma p (tyQtr A))
    branchTy : Derivable (isType (A ∷ gamma) (qtrBranchTy L))
    branchTm : Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    coherence : Derivable
      (termEq (wkTyBy 1 A ∷ A ∷ gamma)
        (wkTmBy 1 l)
        (renTm qtrSecondBranchRen l)
        (qtrCohTy L))
    targetEq : Derivable (typeEq gamma (subTy (singleSubst p) L) T)

open QtrElimPremises public

qtrElimPremisesTyping :
  {gamma : Ctx} {l p : RawTerm} {T : RawType}
  -> (prem : QtrElimPremises gamma l p T)
  -> Derivable (hasTy gamma (tmElQtr l p) (subTy (singleSubst p) (L prem)))
qtrElimPremisesTyping prem =
  eQtr
    (motiveTy prem)
    (scrutineeTy prem)
    (branchTy prem)
    (branchTm prem)
    (coherence prem)

qtrElimPremisesTypedAtTarget :
  {gamma : Ctx} {l p : RawTerm} {T : RawType}
  -> (prem : QtrElimPremises gamma l p T)
  -> Derivable (hasTy gamma (tmElQtr l p) T)
qtrElimPremisesTypedAtTarget prem =
  conv (qtrElimPremisesTyping prem) (targetEq prem)

qtrElimPremisesConv :
  {gamma : Ctx} {l p : RawTerm} {S T : RawType}
  -> QtrElimPremises gamma l p S
  -> Derivable (typeEq gamma S T)
  -> QtrElimPremises gamma l p T
qtrElimPremisesConv prem dST =
  qtrElimPremises
    (A prem)
    (L prem)
    (motiveTy prem)
    (scrutineeTy prem)
    (branchTy prem)
    (branchTm prem)
    (coherence prem)
    (transTy (targetEq prem) dST)

record QtrHead (J : JForm) : Type where
  constructor qtrHead
  field
    gamma : Ctx
    l : RawTerm
    p : RawTerm
    T : RawType
    judgement : J ≡ hasTy gamma (tmElQtr l p) T
    premises : QtrElimPremises gamma l p T

open QtrHead public

invQtrHead? : {J : JForm} -> Derivable J -> Maybe (QtrHead J)
invQtrHead? (conv d dST) with invQtrHead? d
... | nothing = nothing
... | just (qtrHead gamma l p S refl prem) =
  just (qtrHead gamma l p _ refl (qtrElimPremisesConv prem dST))
invQtrHead?
  (eQtr {gamma = gamma} {A = A} {L = L} {l = l} {p = p}
    dL dp dBranchTy dl coh) =
  just
    (qtrHead
      gamma
      l
      p
      (subTy (singleSubst p) L)
      refl
      (qtrElimPremises
        A
        L
        dL
        dp
        dBranchTy
        dl
        coh
        (reflTy (singleSubstTyHelper dL dp))))
{-# CATCHALL #-}
invQtrHead? _ = nothing

invMinimalQtrHead? : {J : JForm} -> Minimal J -> Maybe (QtrHead J)
invMinimalQtrHead? (minConv d dST) with invMinimalQtrHead? d
... | nothing = nothing
... | just (qtrHead gamma l p S refl prem) =
  just (qtrHead gamma l p _ refl (qtrElimPremisesConv prem (minimalToDerivable dST)))
invMinimalQtrHead?
  (minEQtr {gamma = gamma} {A = A} {L = L} {l = l} {p = p}
    dL dp _ dBranchTy dl _ coh _) =
  just
    (qtrHead
      gamma
      l
      p
      (subTy (singleSubst p) L)
      refl
      (qtrElimPremises
        A
        L
        (minimalToDerivable dL)
        (minimalToDerivable dp)
        (minimalToDerivable dBranchTy)
        (minimalToDerivable dl)
        (minimalToDerivable coh)
        (reflTy (singleSubstTyHelper (minimalToDerivable dL) (minimalToDerivable dp)))))
{-# CATCHALL #-}
invMinimalQtrHead? _ = nothing

invMinimalQtrHead :
  {gamma : Ctx} {l p : RawTerm} {T : RawType}
  -> Minimal (hasTy gamma (tmElQtr l p) T)
  -> QtrElimPremises gamma l p T
invMinimalQtrHead (minConv d dST) =
  qtrElimPremisesConv (invMinimalQtrHead d) (minimalToDerivable dST)
invMinimalQtrHead
  (minEQtr {gamma = gamma} {A = A} {L = L} {l = l} {p = p}
    dL dp _ dBranchTy dl _ coh _) =
  qtrElimPremises
    A
    L
    (minimalToDerivable dL)
    (minimalToDerivable dp)
    (minimalToDerivable dBranchTy)
    (minimalToDerivable dl)
    (minimalToDerivable coh)
    (reflTy (singleSubstTyHelper (minimalToDerivable dL) (minimalToDerivable dp)))

record SigmaElimPremises
    (gamma : Ctx) (d m : RawTerm) (T : RawType) : Type where
  constructor sigmaElimPremises
  field
    A : RawType
    B : RawType
    M : RawType
    motiveTy : Derivable (isType (tySigma A B ∷ gamma) M)
    scrutineeTy : Derivable (hasTy gamma d (tySigma A B))
    branchTm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M))
    targetEq : Derivable (typeEq gamma (subTy (singleSubst d) M) T)

open SigmaElimPremises public

sigmaElimPremisesTyping :
  {gamma : Ctx} {d m : RawTerm} {T : RawType}
  -> (prem : SigmaElimPremises gamma d m T)
  -> Derivable (hasTy gamma (tmElSigma d m) (subTy (singleSubst d) (M prem)))
sigmaElimPremisesTyping prem =
  eSigma
    (motiveTy prem)
    (scrutineeTy prem)
    (branchTm prem)

sigmaElimPremisesTypedAtTarget :
  {gamma : Ctx} {d m : RawTerm} {T : RawType}
  -> (prem : SigmaElimPremises gamma d m T)
  -> Derivable (hasTy gamma (tmElSigma d m) T)
sigmaElimPremisesTypedAtTarget prem =
  conv (sigmaElimPremisesTyping prem) (targetEq prem)

sigmaElimPremisesConv :
  {gamma : Ctx} {d m : RawTerm} {S T : RawType}
  -> SigmaElimPremises gamma d m S
  -> Derivable (typeEq gamma S T)
  -> SigmaElimPremises gamma d m T
sigmaElimPremisesConv prem dST =
  sigmaElimPremises
    (A prem)
    (B prem)
    (M prem)
    (motiveTy prem)
    (scrutineeTy prem)
    (branchTm prem)
    (transTy (targetEq prem) dST)

invMinimalSigmaHead :
  {gamma : Ctx} {d m : RawTerm} {T : RawType}
  -> Minimal (hasTy gamma (tmElSigma d m) T)
  -> SigmaElimPremises gamma d m T
invMinimalSigmaHead (minConv d dST) =
  sigmaElimPremisesConv (invMinimalSigmaHead d) (minimalToDerivable dST)
invMinimalSigmaHead
  (minESigma {gamma = gamma} {A = A} {B = B} {M = M} {d = d} {m = m}
    dM dd _ dm _) =
  sigmaElimPremises
    A
    B
    M
    (minimalToDerivable dM)
    (minimalToDerivable dd)
    (minimalToDerivable dm)
    (reflTy (singleSubstTyHelper (minimalToDerivable dM) (minimalToDerivable dd)))
