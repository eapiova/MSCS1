{-# OPTIONS --safe #-}

module Recursive.Contractibility where

open import Recursive.Prelude
open import Data.List.Base using ([] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wf)
open import Induction.WellFounded using (Acc ; acc)

open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Derivability
open import Recursive.Measure
open import Recursive.Presupposition
open import Recursive.Minimal.Base using (renSingleSubstTy ; renSingleSubstTm)
open import Recursive.Minimal.Reflection using (derivableToMinimal)
open import Recursive.Inversion.Values

open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (_×_ ; _,_)

-- Contractibility is a property of the PURE fragment: N is not
-- contractible (0 and s(0) are distinct, see natNoConfusion), so the
-- theorem below is stated for Nat-free types. This predicate makes
-- the "pure T_reg" restriction of the paper explicit in the type.
NatFree : RawType -> Type
NatFree tyTop = ⊤
NatFree (tySigma A B) = NatFree A × NatFree B
NatFree (tyEq A a b) = NatFree A
NatFree (tyQtr A) = NatFree A
NatFree tyNat = ⊥

-- NatFree tracks only type-former structure (terms occur only in the
-- ignored Eq parameters), so it is invariant under substitution.
natFree-subTy : (sigma : Subst) (A : RawType)
  -> NatFree A -> NatFree (subTy sigma A)
natFree-subTy sigma tyTop nf = tt
natFree-subTy sigma (tySigma A B) (nfA , nfB) =
  natFree-subTy sigma A nfA , natFree-subTy (liftSubst sigma) B nfB
natFree-subTy sigma (tyEq A a b) nf = natFree-subTy sigma A nf
natFree-subTy sigma (tyQtr A) nf = natFree-subTy sigma A nf

record Contraction (A : RawType) : Type where
  field
    center    : RawTerm
    centerTm  : Derivable (hasTy [] center A)
    contract  : Derivable
      (termEq (A ∷ []) (var zero) (wkTmBy 1 center) (wkTyBy 1 A))

open Contraction public

singleSubst-wkTy : (t : RawTerm) (A : RawType)
  -> subTy (singleSubst t) (wkTyBy 1 A) ≡ A
singleSubst-wkTy t A =
  subTyRen (singleSubst t) (addRen 1) A ∙ subTyId A

singleSubst-wkTm : (t u : RawTerm)
  -> subTm (singleSubst t) (wkTmBy 1 u) ≡ u
singleSubst-wkTm t u =
  subTmRen (singleSubst t) (addRen 1) u ∙ subTmId u

qtrBranch-wkTy : (A : RawType)
  -> subTy qtrBranchSub (wkTyBy 1 A) ≡ wkTyBy 1 A
qtrBranch-wkTy A =
  subTyRen qtrBranchSub (addRen 1) A
  ∙ sym (renTyKeepSubstBy 1 A)

qtrBranch-wkTm : (t : RawTerm)
  -> subTm qtrBranchSub (wkTmBy 1 t) ≡ wkTmBy 1 t
qtrBranch-wkTm t =
  subTmRen qtrBranchSub (addRen 1) t
  ∙ sym (renTmKeepSubstBy 1 t)

qtrCoh-wkTy : (A : RawType)
  -> subTy qtrCohSub (wkTyBy 1 A) ≡ wkTyBy 2 A
qtrCoh-wkTy A =
  subTyRen qtrCohSub (addRen 1) A
  ∙ sym (renTyKeepSubstBy 2 A)

qtrCoh-wkTm : (t : RawTerm)
  -> subTm qtrCohSub (wkTmBy 1 t) ≡ wkTmBy 2 t
qtrCoh-wkTm t =
  subTmRen qtrCohSub (addRen 1) t
  ∙ sym (renTmKeepSubstBy 2 t)

sigmaBranch-wkTy : (A : RawType)
  -> subTy sigmaMotSub (wkTyBy 1 A) ≡ wkTyBy 2 A
sigmaBranch-wkTy A =
  subTyRen sigmaMotSub (addRen 1) A
  ∙ sym (renTyKeepSubstBy 2 A)

sigmaBranch-wkTm : (t : RawTerm)
  -> subTm sigmaMotSub (wkTmBy 1 t) ≡ wkTmBy 2 t
sigmaBranch-wkTm t =
  subTmRen sigmaMotSub (addRen 1) t
  ∙ sym (renTmKeepSubstBy 2 t)

sigmaSecondSubst : Subst
sigmaSecondSubst = consSubst (var (suc zero)) (keepSubstBy 2)

sigmaSecondSubst-apply : (n : ℕ)
  -> applySubst sigmaSecondSubst n ≡ applySubst (keepSubstBy 1) n
sigmaSecondSubst-apply zero = refl
sigmaSecondSubst-apply (suc n) = refl

sigmaSecondSubst-wkTy : (A : RawType)
  -> subTy sigmaSecondSubst A ≡ wkTyBy 1 A
sigmaSecondSubst-wkTy A =
  subTyEq sigmaSecondSubst-apply A
  ∙ sym (renTyKeepSubstBy 1 A)

sigmaSecondSubst-wkTm : (t : RawTerm)
  -> subTm sigmaSecondSubst t ≡ wkTmBy 1 t
sigmaSecondSubst-wkTm t =
  subTmEq sigmaSecondSubst-apply t
  ∙ sym (renTmKeepSubstBy 1 t)

wk2wk1Ty : (A : RawType) -> wkTyBy 2 (wkTyBy 1 A) ≡ wkTyBy 3 A
wk2wk1Ty A = renTyComp (addRen 2) (addRen 1) A

wk2wk1Tm : (t : RawTerm) -> wkTmBy 2 (wkTmBy 1 t) ≡ wkTmBy 3 t
wk2wk1Tm t = renTmComp (addRen 2) (addRen 1) t

sigmaTail3-wk2wk1Ty : (A : RawType)
  -> subTy (keepSubstBy 3) A ≡ wkTyBy 2 (wkTyBy 1 A)
sigmaTail3-wk2wk1Ty A =
  sym (renTyKeepSubstBy 3 A)
  ∙ sym (wk2wk1Ty A)

sigmaTail3-wk2wk1Tm : (t : RawTerm)
  -> subTm (keepSubstBy 3) t ≡ wkTmBy 2 (wkTmBy 1 t)
sigmaTail3-wk2wk1Tm t =
  sym (renTmKeepSubstBy 3 t)
  ∙ sym (wk2wk1Tm t)

sigmaHead-wk2wk1Ty : (h : RawTerm) (A : RawType)
  -> subTy (consSubst h (keepSubstBy 3)) (wkTyBy 1 A)
       ≡ wkTyBy 2 (wkTyBy 1 A)
sigmaHead-wk2wk1Ty h A =
  subTyRen (consSubst h (keepSubstBy 3)) (addRen 1) A
  ∙ sigmaTail3-wk2wk1Ty A

sigmaHead-wk2wk1Tm : (h t : RawTerm)
  -> subTm (consSubst h (keepSubstBy 3)) (wkTmBy 1 t)
       ≡ wkTmBy 2 (wkTmBy 1 t)
sigmaHead-wk2wk1Tm h t =
  subTmRen (consSubst h (keepSubstBy 3)) (addRen 1) t
  ∙ sigmaTail3-wk2wk1Tm t

contractAt : {A : RawType} {t : RawTerm}
  -> (c : Contraction A)
  -> Derivable (hasTy [] t A)
  -> Derivable (termEq [] t (center c) A)
contractAt {A = A} {t = t} c dt =
  subst
    (λ T -> Derivable (termEq [] t (center c) T))
    (singleSubst-wkTy t A)
    (subst
      (λ u -> Derivable (termEq [] t u (subTy (singleSubst t) (wkTyBy 1 A))))
      (singleSubst-wkTm t (center c))
      (substTmEqRule (contract c) (singleFitsSubstHelper dt)))

subTy-snd< : (A B : RawType) (a : RawTerm)
  -> tyDepth (subTy (singleSubst a) B) < suc (tyDepth A + tyDepth B)
subTy-snd< A B a =
  subst
    (λ k -> k < suc (tyDepth A + tyDepth B))
    (sym (tyDepth-subTy (singleSubst a) B))
    (tyDepth-snd<Sigma A B)

contractibleAcc : (A : RawType)
  -> Acc _<_ (tyDepth A)
  -> NatFree A
  -> Derivable (isType [] A)
  -> Contraction A
contractibleAcc tyNat _ () _
contractibleAcc tyTop _ _ dTop =
  record
    { center = tmStar
    ; centerTm = iTop wfNil
    ; contract = cTop (varStar {delta = []} (wfCons wfNil dTop) dTop)
    }
contractibleAcc (tySigma A B) (acc rec) (nfA , nfB) dSigma =
  record
    { center = tmPair (center cA) (center cB)
    ; centerTm = iSigma (centerTm cA) (centerTm cB) dSigma
    ; contract = sigmaContract
    }
  where
  prem = invMinimalSigmaTy (derivableToMinimal dSigma)

  dA : Derivable (isType [] A)
  dA = leftTy prem

  dB : Derivable (isType (A ∷ []) B)
  dB = familyTy prem

  cA : Contraction A
  cA = contractibleAcc A (rec (tyDepth-fst<Sigma A B)) nfA dA

  B0 : RawType
  B0 = subTy (singleSubst (center cA)) B

  dB0 : Derivable (isType [] B0)
  dB0 = singleSubstTyHelper dB (centerTm cA)

  cB : Contraction B0
  cB = contractibleAcc B0 (rec (subTy-snd< A B (center cA)))
         (natFree-subTy (singleSubst (center cA)) B nfB) dB0

  S : RawType
  S = tySigma A B

  wfS : CtxWF (S ∷ [])
  wfS = wfCons wfNil dSigma

  AS : RawType
  AS = wkTyBy 1 A

  BS : RawType
  BS = renTy (raiseRen (addRen 1)) B

  SS : RawType
  SS = wkTyBy 1 S

  dSS : Derivable (isType (S ∷ []) SS)
  dSS = weakenTy dSigma wfS

  varS : Derivable (hasTy (S ∷ []) (var zero) SS)
  varS = varStar {delta = []} wfS dSigma

  centerS : Derivable
    (hasTy (S ∷ []) (wkTmBy 1 (tmPair (center cA) (center cB))) SS)
  centerS = weakenTm (iSigma (centerTm cA) (centerTm cB) dSigma) wfS

  MotiveS : RawType
  MotiveS = tyEq (wkTyBy 1 SS) (var zero) (wkTmBy 1 (wkTmBy 1 (tmPair (center cA) (center cB))))

  wfMotiveS : CtxWF (SS ∷ S ∷ [])
  wfMotiveS = wfCons wfS dSS

  dMotiveS : Derivable (isType (SS ∷ S ∷ []) MotiveS)
  dMotiveS =
    fEq
      (weakenTy {delta = SS ∷ []} dSS wfMotiveS)
      (varStar {delta = []} wfMotiveS dSS)
      (weakenTm {delta = SS ∷ []} centerS wfMotiveS)

  dAS : Derivable (isType (S ∷ []) AS)
  dAS = leftTy (invMinimalSigmaTy (derivableToMinimal dSS))

  dBS : Derivable (isType (AS ∷ S ∷ []) BS)
  dBS = familyTy (invMinimalSigmaTy (derivableToMinimal dSS))

  wfAS : CtxWF (AS ∷ S ∷ [])
  wfAS = wfCons wfS dAS

  wfBranchS : CtxWF (BS ∷ AS ∷ S ∷ [])
  wfBranchS = wfCons wfAS dBS

  dNiceS : Derivable (isType (BS ∷ AS ∷ S ∷ []) (wkTyBy 2 SS))
  dNiceS = weakenTy {delta = BS ∷ AS ∷ []} dSS wfBranchS

  dNiceA : Derivable (isType (BS ∷ AS ∷ S ∷ []) (wkTyBy 2 AS))
  dNiceA = leftTy (invMinimalSigmaTy (derivableToMinimal dNiceS))

  dNiceB : Derivable
    (isType (wkTyBy 2 AS ∷ BS ∷ AS ∷ S ∷ [])
      (renTy (raiseRen (addRen 2)) BS))
  dNiceB = familyTy (invMinimalSigmaTy (derivableToMinimal dNiceS))

  varAΣ : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ []) (var (suc zero)) (wkTyBy 2 AS))
  varAΣ = varStar {gamma = S ∷ []} {delta = BS ∷ []} wfBranchS dAS

  varBΣ0 : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ []) (var zero) (wkTyBy 1 BS))
  varBΣ0 = varStar {gamma = AS ∷ S ∷ []} {delta = []} wfBranchS dBS

  varBΣ : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ []) (var zero)
      (subTy (singleSubst (var (suc zero))) (renTy (raiseRen (addRen 2)) BS)))
  varBΣ =
    subst
      (λ T -> Derivable (hasTy (BS ∷ AS ∷ S ∷ []) (var zero) T))
      (sym
        (subTyRen (singleSubst (var (suc zero))) (raiseRen (addRen 2)) BS
         ∙ sigmaSecondSubst-wkTy BS))
      varBΣ0

  pairVarΣ : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ [])
      (tmPair (var (suc zero)) (var zero))
      (wkTyBy 2 SS))
  pairVarΣ = iSigma varAΣ varBΣ dNiceS

  a0BranchΣ : RawTerm
  a0BranchΣ = wkTmBy 2 (wkTmBy 1 (center cA))

  b0BranchΣ : RawTerm
  b0BranchΣ = wkTmBy 2 (wkTmBy 1 (center cB))

  centerBranchΣ : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ [])
      (wkTmBy 2 (wkTmBy 1 (tmPair (center cA) (center cB))))
      (wkTyBy 2 SS))
  centerBranchΣ = weakenTm {delta = BS ∷ AS ∷ []} centerS wfBranchS

  varAForFits : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ []) (var (suc zero)) (subTy (keepSubstBy 3) A))
  varAForFits =
    subst
      (λ T -> Derivable (hasTy (BS ∷ AS ∷ S ∷ []) (var (suc zero)) T))
      (sym (sigmaTail3-wk2wk1Ty A))
      varAΣ

  fitsAΣ : FitsSubst
    (BS ∷ AS ∷ S ∷ [])
    (A ∷ [])
    (consSubst (var (suc zero)) (keepSubstBy 3))
  fitsAΣ =
    fitsCons
      (fitsNil {gamma = BS ∷ AS ∷ S ∷ []} {delta = []} {sigma = keepSubstBy 3} wfBranchS)
      varAForFits

  firstEq0 : Derivable
    (termEq (BS ∷ AS ∷ S ∷ [])
      (var (suc zero))
      (subTm (consSubst (var (suc zero)) (keepSubstBy 3)) (wkTmBy 1 (center cA)))
      (subTy (consSubst (var (suc zero)) (keepSubstBy 3)) (wkTyBy 1 A)))
  firstEq0 = substTmEqRule (contract cA) fitsAΣ

  firstEqNice : Derivable
    (termEq (BS ∷ AS ∷ S ∷ []) (var (suc zero)) a0BranchΣ (wkTyBy 2 AS))
  firstEqNice =
    subst
      (λ T -> Derivable (termEq (BS ∷ AS ∷ S ∷ []) (var (suc zero)) a0BranchΣ T))
      (sigmaHead-wk2wk1Ty (var (suc zero)) A)
      (subst
        (λ u -> Derivable
          (termEq (BS ∷ AS ∷ S ∷ []) (var (suc zero)) u
            (subTy (consSubst (var (suc zero)) (keepSubstBy 3)) (wkTyBy 1 A))))
        (sigmaHead-wk2wk1Tm (var (suc zero)) (center cA))
        firstEq0)

  familyAtA0Eq : Derivable
    (typeEq (BS ∷ AS ∷ S ∷ [])
      (subTy (singleSubst (var (suc zero))) (renTy (raiseRen (addRen 2)) BS))
      (subTy (singleSubst a0BranchΣ) (renTy (raiseRen (addRen 2)) BS)))
  familyAtA0Eq = singleEqSubstTyHelper dNiceB firstEqNice

  varBAtA0 : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ []) (var zero)
      (subTy (singleSubst a0BranchΣ) (renTy (raiseRen (addRen 2)) BS)))
  varBAtA0 = conv varBΣ familyAtA0Eq

  B0BranchPath :
    wkTyBy 2 (wkTyBy 1 B0)
      ≡ subTy (singleSubst a0BranchΣ) (renTy (raiseRen (addRen 2)) BS)
  B0BranchPath =
    cong (wkTyBy 2) (renSingleSubstTy (addRen 1) (center cA) B)
    ∙ renSingleSubstTy (addRen 2) (wkTmBy 1 (center cA)) BS

  varBAtB0 : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ []) (var zero) (wkTyBy 2 (wkTyBy 1 B0)))
  varBAtB0 =
    subst
      (λ T -> Derivable (hasTy (BS ∷ AS ∷ S ∷ []) (var zero) T))
      (sym B0BranchPath)
      varBAtA0

  varBForFits : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ []) (var zero) (subTy (keepSubstBy 3) B0))
  varBForFits =
    subst
      (λ T -> Derivable (hasTy (BS ∷ AS ∷ S ∷ []) (var zero) T))
      (sym (sigmaTail3-wk2wk1Ty B0))
      varBAtB0

  fitsBΣ : FitsSubst
    (BS ∷ AS ∷ S ∷ [])
    (B0 ∷ [])
    (consSubst (var zero) (keepSubstBy 3))
  fitsBΣ =
    fitsCons
      (fitsNil {gamma = BS ∷ AS ∷ S ∷ []} {delta = []} {sigma = keepSubstBy 3} wfBranchS)
      varBForFits

  secondEq0 : Derivable
    (termEq (BS ∷ AS ∷ S ∷ [])
      (var zero)
      (subTm (consSubst (var zero) (keepSubstBy 3)) (wkTmBy 1 (center cB)))
      (subTy (consSubst (var zero) (keepSubstBy 3)) (wkTyBy 1 B0)))
  secondEq0 = substTmEqRule (contract cB) fitsBΣ

  secondEqAtA0B0 : Derivable
    (termEq (BS ∷ AS ∷ S ∷ []) (var zero) b0BranchΣ (wkTyBy 2 (wkTyBy 1 B0)))
  secondEqAtA0B0 =
    subst
      (λ T -> Derivable (termEq (BS ∷ AS ∷ S ∷ []) (var zero) b0BranchΣ T))
      (sigmaHead-wk2wk1Ty (var zero) B0)
      (subst
        (λ u -> Derivable
          (termEq (BS ∷ AS ∷ S ∷ []) (var zero) u
            (subTy (consSubst (var zero) (keepSubstBy 3)) (wkTyBy 1 B0))))
        (sigmaHead-wk2wk1Tm (var zero) (center cB))
        secondEq0)

  secondEqAtA0 : Derivable
    (termEq (BS ∷ AS ∷ S ∷ []) (var zero) b0BranchΣ
      (subTy (singleSubst a0BranchΣ) (renTy (raiseRen (addRen 2)) BS)))
  secondEqAtA0 =
    convEq secondEqAtA0B0
      (subst
        (λ T -> Derivable
          (typeEq (BS ∷ AS ∷ S ∷ []) (wkTyBy 2 (wkTyBy 1 B0)) T))
        B0BranchPath
        (reflTy (assocTmTy secondEqAtA0B0)))

  secondEqNice : Derivable
    (termEq (BS ∷ AS ∷ S ∷ []) (var zero) b0BranchΣ
      (subTy (singleSubst (var (suc zero))) (renTy (raiseRen (addRen 2)) BS)))
  secondEqNice =
    convEq secondEqAtA0
      (symTy familyAtA0Eq (assocTyRight familyAtA0Eq))

  pairEqNice : Derivable
    (termEq (BS ∷ AS ∷ S ∷ [])
      (tmPair (var (suc zero)) (var zero))
      (wkTmBy 2 (wkTmBy 1 (tmPair (center cA) (center cB))))
      (wkTyBy 2 SS))
  pairEqNice = iSigmaEq firstEqNice secondEqNice dNiceA dNiceB

  branchBaseEqS : Derivable
    (typeEq (BS ∷ AS ∷ S ∷ [])
      (wkTyBy 2 SS)
      (subTy sigmaMotSub (wkTyBy 1 SS)))
  branchBaseEqS =
    subst
      (λ T -> Derivable (typeEq (BS ∷ AS ∷ S ∷ []) (wkTyBy 2 SS) T))
      (sym (sigmaBranch-wkTy SS))
      (reflTy dNiceS)

  branchEndpointEqS : Derivable
    (termEq (BS ∷ AS ∷ S ∷ [])
      (tmPair (var (suc zero)) (var zero))
      (subTm sigmaMotSub (wkTmBy 1 (wkTmBy 1 (tmPair (center cA) (center cB)))))
      (wkTyBy 2 SS))
  branchEndpointEqS =
    subst
      (λ u -> Derivable
        (termEq (BS ∷ AS ∷ S ∷ [])
          (tmPair (var (suc zero)) (var zero)) u (wkTyBy 2 SS)))
      (sym (sigmaBranch-wkTm (wkTmBy 1 (tmPair (center cA) (center cB)))))
      pairEqNice

  branchTyEqS : Derivable
    (typeEq (BS ∷ AS ∷ S ∷ [])
      (tyEq (wkTyBy 2 SS)
        (tmPair (var (suc zero)) (var zero))
        (tmPair (var (suc zero)) (var zero)))
      (sigmaBranchTy MotiveS))
  branchTyEqS =
    fEqEq
      branchBaseEqS
      (reflTm pairVarΣ)
      branchEndpointEqS

  dBranchS : Derivable
    (hasTy (BS ∷ AS ∷ S ∷ []) tmRefl (sigmaBranchTy MotiveS))
  dBranchS = conv (iEq pairVarΣ) branchTyEqS

  sigmaProof0 : Derivable
    (hasTy (S ∷ []) (tmElSigma (var zero) tmRefl)
      (subTy (singleSubst (var zero)) MotiveS))
  sigmaProof0 = eSigma dMotiveS varS dBranchS

  sigmaProofTyPath :
    subTy (singleSubst (var zero)) MotiveS
      ≡ tyEq SS (var zero) (wkTmBy 1 (tmPair (center cA) (center cB)))
  sigmaProofTyPath =
    cong₃ tyEq
      (singleSubst-wkTy (var zero) SS)
      refl
      (singleSubst-wkTm (var zero) (wkTmBy 1 (tmPair (center cA) (center cB))))

  sigmaProof : Derivable
    (hasTy (S ∷ []) (tmElSigma (var zero) tmRefl)
      (tyEq SS (var zero) (wkTmBy 1 (tmPair (center cA) (center cB)))))
  sigmaProof =
    subst
      (λ T -> Derivable (hasTy (S ∷ []) (tmElSigma (var zero) tmRefl) T))
      sigmaProofTyPath
      sigmaProof0

  sigmaContract : Derivable
    (termEq (S ∷ []) (var zero) (wkTmBy 1 (tmPair (center cA) (center cB))) SS)
  sigmaContract = eEqStar sigmaProof dSS varS centerS
contractibleAcc (tyEq A a b) (acc rec) nf dEq =
  record
    { center = tmRefl
    ; centerTm = centerEqTm
    ; contract =
        cEq
          (varStar {delta = []} wfEq dEq)
          (weakenTy dA wfEq)
          (weakenTm da wfEq)
          (weakenTm db wfEq)
    }
  where
  prem = invMinimalEqTy (derivableToMinimal dEq)

  dA : Derivable (isType [] A)
  dA = typeTy prem

  da : Derivable (hasTy [] a A)
  da = leftTm prem

  db : Derivable (hasTy [] b A)
  db = rightTm prem

  cA : Contraction A
  cA = contractibleAcc A (rec (tyDepth-base<Eq A a b)) nf dA

  a=a₀ : Derivable (termEq [] a (center cA) A)
  a=a₀ = contractAt cA da

  b=a₀ : Derivable (termEq [] b (center cA) A)
  b=a₀ = contractAt cA db

  a₀=a : Derivable (termEq [] (center cA) a A)
  a₀=a = symTm a=a₀ (centerTm cA) dA

  a₀=b : Derivable (termEq [] (center cA) b A)
  a₀=b = symTm b=a₀ (centerTm cA) dA

  centerEqTy : Derivable (typeEq [] (tyEq A (center cA) (center cA)) (tyEq A a b))
  centerEqTy = fEqEq (reflTy dA) a₀=a a₀=b

  centerEqTm : Derivable (hasTy [] tmRefl (tyEq A a b))
  centerEqTm = conv (iEq (centerTm cA)) centerEqTy

  wfEq : CtxWF (tyEq A a b ∷ [])
  wfEq = wfCons wfNil dEq
contractibleAcc (tyQtr A) (acc rec) nf dQtr =
  record
    { center = tmClass (center cA)
    ; centerTm = iQtr (centerTm cA)
    ; contract = qtrContract
    }
  where
  prem = invMinimalQtrTy (derivableToMinimal dQtr)

  dA : Derivable (isType [] A)
  dA = innerTy prem

  cA : Contraction A
  cA = contractibleAcc A (rec (tyDepth-base<Qtr A)) nf dA

  Q : RawType
  Q = tyQtr A

  wfQ : CtxWF (Q ∷ [])
  wfQ = wfCons wfNil dQtr

  AQ : RawType
  AQ = wkTyBy 1 A

  QQ : RawType
  QQ = wkTyBy 1 Q

  dQQ : Derivable (isType (Q ∷ []) QQ)
  dQQ = weakenTy dQtr wfQ

  varQ : Derivable (hasTy (Q ∷ []) (var zero) QQ)
  varQ = varStar {delta = []} wfQ dQtr

  centerQ : Derivable (hasTy (Q ∷ []) (wkTmBy 1 (tmClass (center cA))) QQ)
  centerQ = weakenTm (iQtr (centerTm cA)) wfQ

  MotiveQ : RawType
  MotiveQ = tyEq (wkTyBy 1 QQ) (var zero) (wkTmBy 1 (wkTmBy 1 (tmClass (center cA))))

  wfL : CtxWF (QQ ∷ Q ∷ [])
  wfL = wfCons wfQ dQQ

  dL : Derivable (isType (QQ ∷ Q ∷ []) MotiveQ)
  dL =
    fEq
      (weakenTy {delta = QQ ∷ []} dQQ wfL)
      (varStar {delta = []} wfL dQQ)
      (weakenTm {delta = QQ ∷ []} centerQ wfL)

  dAQ : Derivable (isType (Q ∷ []) AQ)
  dAQ = weakenTy dA wfQ

  wfBranch : CtxWF (AQ ∷ Q ∷ [])
  wfBranch = wfCons wfQ dAQ

  dBranchBase : Derivable (isType (AQ ∷ Q ∷ []) (wkTyBy 1 QQ))
  dBranchBase = weakenTy {delta = AQ ∷ []} dQQ wfBranch

  varA : Derivable (hasTy (AQ ∷ Q ∷ []) (var zero) (wkTyBy 1 AQ))
  varA = varStar {delta = []} wfBranch dAQ

  a0Branch : Derivable
    (hasTy (AQ ∷ Q ∷ []) (wkTmBy 1 (wkTmBy 1 (center cA))) (wkTyBy 1 AQ))
  a0Branch = weakenTm {delta = AQ ∷ []} (weakenTm (centerTm cA) wfQ) wfBranch

  branchLeft : Derivable
    (hasTy (AQ ∷ Q ∷ []) (tmClass (var zero)) (wkTyBy 1 QQ))
  branchLeft = iQtr varA

  branchRight : Derivable
    (hasTy (AQ ∷ Q ∷ []) (wkTmBy 1 (wkTmBy 1 (tmClass (center cA)))) (wkTyBy 1 QQ))
  branchRight = iQtr a0Branch

  branchEndpointEq : Derivable
    (termEq (AQ ∷ Q ∷ [])
      (tmClass (var zero))
      (wkTmBy 1 (wkTmBy 1 (tmClass (center cA))))
      (wkTyBy 1 QQ))
  branchEndpointEq = iQtrEq varA a0Branch

  branchBaseEq : Derivable
    (typeEq (AQ ∷ Q ∷ [])
      (wkTyBy 1 QQ)
      (subTy qtrBranchSub (wkTyBy 1 QQ)))
  branchBaseEq =
    subst
      (λ T -> Derivable (typeEq (AQ ∷ Q ∷ []) (wkTyBy 1 QQ) T))
      (sym (qtrBranch-wkTy QQ))
      (reflTy dBranchBase)

  branchEndpointEq' : Derivable
    (termEq (AQ ∷ Q ∷ [])
      (tmClass (var zero))
      (subTm qtrBranchSub (wkTmBy 1 (wkTmBy 1 (tmClass (center cA)))))
      (wkTyBy 1 QQ))
  branchEndpointEq' =
    subst
      (λ u -> Derivable
        (termEq (AQ ∷ Q ∷ []) (tmClass (var zero)) u (wkTyBy 1 QQ)))
      (sym (qtrBranch-wkTm (wkTmBy 1 (tmClass (center cA)))))
      branchEndpointEq

  branchTyEq : Derivable
    (typeEq (AQ ∷ Q ∷ [])
      (tyEq (wkTyBy 1 QQ) (tmClass (var zero)) (tmClass (var zero)))
      (qtrBranchTy MotiveQ))
  branchTyEq =
    fEqEq
      branchBaseEq
      (reflTm branchLeft)
      branchEndpointEq'

  dBranchTy : Derivable (isType (AQ ∷ Q ∷ []) (qtrBranchTy MotiveQ))
  dBranchTy = assocTyRight branchTyEq

  dBranch : Derivable (hasTy (AQ ∷ Q ∷ []) tmRefl (qtrBranchTy MotiveQ))
  dBranch = conv (iEq branchLeft) branchTyEq

  dWkAQ : Derivable (isType (AQ ∷ Q ∷ []) (wkTyBy 1 AQ))
  dWkAQ = weakenTy {delta = AQ ∷ []} dAQ wfBranch

  wfCoh : CtxWF (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ [])
  wfCoh = wfCons wfBranch dWkAQ

  dCohBase : Derivable
    (isType (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ []) (wkTyBy 2 QQ))
  dCohBase =
    weakenTy {delta = wkTyBy 1 AQ ∷ AQ ∷ []} dQQ wfCoh

  varA1 : Derivable
    (hasTy (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ []) (var (suc zero)) (wkTyBy 2 AQ))
  varA1 =
    varStar {gamma = Q ∷ []} {delta = wkTyBy 1 AQ ∷ []} wfCoh dAQ

  a0Coh : Derivable
    (hasTy (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ [])
      (wkTmBy 2 (wkTmBy 1 (center cA)))
      (wkTyBy 2 AQ))
  a0Coh =
    weakenTm
      {delta = wkTyBy 1 AQ ∷ AQ ∷ []}
      (weakenTm (centerTm cA) wfQ)
      wfCoh

  cohLeft : Derivable
    (hasTy (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ [])
      (tmClass (var (suc zero)))
      (wkTyBy 2 QQ))
  cohLeft = iQtr varA1

  cohEndpointEq : Derivable
    (termEq (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ [])
      (tmClass (var (suc zero)))
      (wkTmBy 2 (wkTmBy 1 (tmClass (center cA))))
      (wkTyBy 2 QQ))
  cohEndpointEq = iQtrEq varA1 a0Coh

  cohBaseEq : Derivable
    (typeEq (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ [])
      (wkTyBy 2 QQ)
      (subTy qtrCohSub (wkTyBy 1 QQ)))
  cohBaseEq =
    subst
      (λ T -> Derivable
        (typeEq (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ []) (wkTyBy 2 QQ) T))
      (sym (qtrCoh-wkTy QQ))
      (reflTy dCohBase)

  cohEndpointEq' : Derivable
    (termEq (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ [])
      (tmClass (var (suc zero)))
      (subTm qtrCohSub (wkTmBy 1 (wkTmBy 1 (tmClass (center cA)))))
      (wkTyBy 2 QQ))
  cohEndpointEq' =
    subst
      (λ u -> Derivable
        (termEq (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ [])
          (tmClass (var (suc zero))) u (wkTyBy 2 QQ)))
      (sym (qtrCoh-wkTm (wkTmBy 1 (tmClass (center cA)))))
      cohEndpointEq

  cohTyEq : Derivable
    (typeEq (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ [])
      (tyEq (wkTyBy 2 QQ) (tmClass (var (suc zero))) (tmClass (var (suc zero))))
      (qtrCohTy MotiveQ))
  cohTyEq =
    fEqEq
      cohBaseEq
      (reflTm cohLeft)
      cohEndpointEq'

  cohRefl : Derivable
    (hasTy (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ []) tmRefl (qtrCohTy MotiveQ))
  cohRefl = conv (iEq cohLeft) cohTyEq

  dCoh : Derivable
    (termEq (wkTyBy 1 AQ ∷ AQ ∷ Q ∷ [])
      (wkTmBy 1 tmRefl)
      (renTm qtrSecondBranchRen tmRefl)
      (qtrCohTy MotiveQ))
  dCoh = reflTm cohRefl

  qtrProof0 : Derivable
    (hasTy (Q ∷ []) (tmElQtr tmRefl (var zero)) (subTy (singleSubst (var zero)) MotiveQ))
  qtrProof0 = eQtr dL varQ dBranchTy dBranch dCoh

  qtrProofTyPath :
    subTy (singleSubst (var zero)) MotiveQ
      ≡ tyEq QQ (var zero) (wkTmBy 1 (tmClass (center cA)))
  qtrProofTyPath =
    cong₃ tyEq
      (singleSubst-wkTy (var zero) QQ)
      refl
      (singleSubst-wkTm (var zero) (wkTmBy 1 (tmClass (center cA))))

  qtrProof : Derivable
    (hasTy (Q ∷ []) (tmElQtr tmRefl (var zero))
      (tyEq QQ (var zero) (wkTmBy 1 (tmClass (center cA)))))
  qtrProof =
    subst
      (λ T -> Derivable (hasTy (Q ∷ []) (tmElQtr tmRefl (var zero)) T))
      qtrProofTyPath
      qtrProof0

  qtrContract : Derivable
    (termEq (Q ∷ []) (var zero) (wkTmBy 1 (tmClass (center cA))) QQ)
  qtrContract = eEqStar qtrProof dQQ varQ centerQ

contractible : (A : RawType)
  -> NatFree A
  -> Derivable (isType [] A) -> Contraction A
contractible A nf dA = contractibleAcc A (<-wf (tyDepth A)) nf dA

dSig : Derivable (isType [] (tySigma tyTop tyTop))
dSig = fSigma (fTop wfNil) (fTop (wfCons wfNil (fTop wfNil)))

contractibleSigmaCenter :
  center (contractible (tySigma tyTop tyTop) (tt , tt) dSig) ≡ tmPair tmStar tmStar
contractibleSigmaCenter = refl

dQtrTop : Derivable (isType [] (tyQtr tyTop))
dQtrTop = fQtr (fTop wfNil)

contractibleQtrCenter :
  center (contractible (tyQtr tyTop) tt dQtrTop) ≡ tmClass tmStar
contractibleQtrCenter = refl
