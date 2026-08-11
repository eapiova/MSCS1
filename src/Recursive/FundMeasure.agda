{-# OPTIONS --safe #-}

module Recursive.FundMeasure where

open import Recursive.Prelude
open import Data.List.Base using (_∷_)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.Base using (_<_ ; _≤_) renaming (s≤s to suc-≤-suc)
open import Data.Nat.Properties using (≤-refl ; ≤-trans)
import Data.Nat.Properties as NatProps
open import Data.Nat.Induction public using (<-wellFounded)
open import Induction.WellFounded public using (Acc ; acc)

open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution using (Subst ; subTy ; singleSubst)
open import Recursive.Derivability

≤-sum-l : {m n : ℕ} -> m ≤ m + n
≤-sum-l {m} {n} = NatProps.m≤m+n m n

≤-sum-r : {m n : ℕ} -> m ≤ n + m
≤-sum-r {m} {n} = NatProps.m≤n+m m n

≤-sum-extend-r : {n m k : ℕ} -> n ≤ m -> n ≤ m + k
≤-sum-extend-r n≤m = ≤-trans n≤m ≤-sum-l

≤-sum-extend-l : {n m k : ℕ} -> n ≤ m -> n ≤ k + m
≤-sum-extend-l n≤m = ≤-trans n≤m ≤-sum-r

<-suc-of-≤ : {n m : ℕ} -> n ≤ m -> n < suc m
<-suc-of-≤ = suc-≤-suc

mutual
  mDeriv : {J : JForm} -> Derivable J -> ℕ
  mDeriv (varStar wf dA) = suc (mCtxWF wf + mDeriv dA)
  mDeriv (weakenTy d wf) = suc (mDeriv d + mCtxWF wf)
  mDeriv (weakenTyEq d wf) = suc (mDeriv d + mCtxWF wf)
  mDeriv (weakenTm d wf) = suc (mDeriv d + mCtxWF wf)
  mDeriv (weakenTmEq d wf) = suc (mDeriv d + mCtxWF wf)
  mDeriv (reflTy d) = suc (mDeriv d)
  mDeriv (reflTm d) = suc (mDeriv d)
  mDeriv (symTy d dB) = suc (mDeriv d + mDeriv dB)
  mDeriv (symTm d du dA) = suc (mDeriv d + mDeriv du + mDeriv dA)
  mDeriv (transTy d₁ d₂) = suc (mDeriv d₁ + mDeriv d₂)
  mDeriv (transTm d₁ d₂) = suc (mDeriv d₁ + mDeriv d₂)
  mDeriv (conv d dAB) = suc (mDeriv d + mDeriv dAB)
  mDeriv (convEq d dAB) = suc (mDeriv d + mDeriv dAB)
  mDeriv (substTyRule d fits) = suc (mDeriv d + mFits fits)
  mDeriv (substTyEqRule d fits) = suc (mDeriv d + mFits fits)
  mDeriv (substTmRule d fits) = suc (mDeriv d + mFits fits)
  mDeriv (substTmEqRule d fits) = suc (mDeriv d + mFits fits)
  mDeriv (eqSubTyRule d fitsEq) = suc (mDeriv d + mFitsEq fitsEq)
  mDeriv (eqSubTyEqRule d fitsEq) = suc (mDeriv d + mFitsEq fitsEq)
  mDeriv (eqSubTmRule d fitsEq) = suc (mDeriv d + mFitsEq fitsEq)
  mDeriv (eqSubTmEqRule d fitsEq) = suc (mDeriv d + mFitsEq fitsEq)
  mDeriv (fTop wf) = suc (mCtxWF wf)
  mDeriv (iTop wf) = suc (mCtxWF wf)
  mDeriv (cTop d) = suc (mDeriv d)
  mDeriv (fSigma dA dB) = suc (mDeriv dA + mDeriv dB)
  mDeriv (fSigmaEq dAC dB dBD) = suc (mDeriv dAC + mDeriv dB + mDeriv dBD)
  mDeriv (iSigma da db dSigma) = suc (mDeriv da + mDeriv db + mDeriv dSigma)
  mDeriv (iSigmaEq dac dbd dA dB) = suc (mDeriv dac + mDeriv dbd + mDeriv dA + mDeriv dB)
  mDeriv (eSigma dM dd dm) = suc (mDeriv dM + mDeriv dd + mDeriv dm)
  mDeriv (eSigmaEq dM dd dm dm') = suc (mDeriv dM + mDeriv dd + mDeriv dm + mDeriv dm')
  mDeriv (cSigma dM dSigma db dc dm) = suc (mDeriv dM + mDeriv dSigma + mDeriv db + mDeriv dc + mDeriv dm)
  mDeriv (fEq dA da db) = suc (mDeriv dA + mDeriv da + mDeriv db)
  mDeriv (fEqEq dAC dac dbd) = suc (mDeriv dAC + mDeriv dac + mDeriv dbd)
  mDeriv (iEq da) = suc (mDeriv da)
  mDeriv (iEqEq dab) = suc (mDeriv dab)
  mDeriv (eEqStar dp dA da db) = suc (mDeriv dp + mDeriv dA + mDeriv da + mDeriv db)
  mDeriv (cEq dp dA da db) = suc (mDeriv dp + mDeriv dA + mDeriv da + mDeriv db)
  mDeriv (fQtr dA) = suc (mDeriv dA)
  mDeriv (fQtrEq dAB) = suc (mDeriv dAB)
  mDeriv (iQtr da) = suc (mDeriv da)
  mDeriv (iQtrEq da db) = suc (mDeriv da + mDeriv db)
  mDeriv (eQtr dL dp dBranchTy dl dcoh) =
    suc (mDeriv dL + mDeriv dp + mDeriv dBranchTy + mDeriv dl + mDeriv dcoh)
  mDeriv (eQtrEq dL dp dBranchTy dl dl' dll' dcoh dcoh') =
    suc
      (mDeriv dL + mDeriv dp + mDeriv dBranchTy + mDeriv dl
       + mDeriv dl' + mDeriv dll' + mDeriv dcoh + mDeriv dcoh')
  mDeriv (cQtr dL da dBranchTy dl dcoh) =
    suc (mDeriv dL + mDeriv da + mDeriv dBranchTy + mDeriv dl + mDeriv dcoh)
  mDeriv (fNat wf) = suc (mCtxWF wf)
  mDeriv (iZero wf) = suc (mCtxWF wf)
  mDeriv (iSuc d) = suc (mDeriv d)
  mDeriv (iSucEq d) = suc (mDeriv d)
  mDeriv (eNat dL dn da dl) = suc (mDeriv dL + mDeriv dn + mDeriv da + mDeriv dl)
  mDeriv (eNatEq dL dnn' da daa' dl dll') =
    suc (mDeriv dL + mDeriv dnn' + mDeriv da + mDeriv daa' + mDeriv dl + mDeriv dll')
  mDeriv (cNatZ dL da dl) = suc (mDeriv dL + mDeriv da + mDeriv dl)
  mDeriv (cNatS dL dn da dl) = suc (mDeriv dL + mDeriv dn + mDeriv da + mDeriv dl)

  mCtxWF : {gamma : Ctx} -> CtxWF gamma -> ℕ
  mCtxWF wfNil = suc zero
  mCtxWF (wfCons wf dA) = suc (mCtxWF wf + mDeriv dA)

  mFits : {gamma delta : Ctx} {sigma : Subst} -> FitsSubst gamma delta sigma -> ℕ
  mFits (fitsNil wf) = suc (mCtxWF wf)
  mFits (fitsCons fits dt) = suc (mFits fits + mDeriv dt)

  mFitsEq : {gamma delta : Ctx} {sigma tau : Subst} -> FitsEqSubst gamma delta sigma tau -> ℕ
  mFitsEq (fitsEqNil wf) = suc (mCtxWF wf)
  mFitsEq (fitsEqCons fitsEq dtu) = suc (mFitsEq fitsEq + mDeriv dtu)

mDerivBody : {J : JForm} -> Derivable J -> ℕ
mDerivBody (varStar wf dA) = mCtxWF wf + mDeriv dA
mDerivBody (weakenTy d wf) = mDeriv d + mCtxWF wf
mDerivBody (weakenTyEq d wf) = mDeriv d + mCtxWF wf
mDerivBody (weakenTm d wf) = mDeriv d + mCtxWF wf
mDerivBody (weakenTmEq d wf) = mDeriv d + mCtxWF wf
mDerivBody (reflTy d) = mDeriv d
mDerivBody (reflTm d) = mDeriv d
mDerivBody (symTy d dB) = mDeriv d + mDeriv dB
mDerivBody (symTm d du dA) = mDeriv d + mDeriv du + mDeriv dA
mDerivBody (transTy d₁ d₂) = mDeriv d₁ + mDeriv d₂
mDerivBody (transTm d₁ d₂) = mDeriv d₁ + mDeriv d₂
mDerivBody (conv d dAB) = mDeriv d + mDeriv dAB
mDerivBody (convEq d dAB) = mDeriv d + mDeriv dAB
mDerivBody (substTyRule d fits) = mDeriv d + mFits fits
mDerivBody (substTyEqRule d fits) = mDeriv d + mFits fits
mDerivBody (substTmRule d fits) = mDeriv d + mFits fits
mDerivBody (substTmEqRule d fits) = mDeriv d + mFits fits
mDerivBody (eqSubTyRule d fitsEq) = mDeriv d + mFitsEq fitsEq
mDerivBody (eqSubTyEqRule d fitsEq) = mDeriv d + mFitsEq fitsEq
mDerivBody (eqSubTmRule d fitsEq) = mDeriv d + mFitsEq fitsEq
mDerivBody (eqSubTmEqRule d fitsEq) = mDeriv d + mFitsEq fitsEq
mDerivBody (fTop wf) = mCtxWF wf
mDerivBody (iTop wf) = mCtxWF wf
mDerivBody (cTop d) = mDeriv d
mDerivBody (fSigma dA dB) = mDeriv dA + mDeriv dB
mDerivBody (fSigmaEq dAC dB dBD) = mDeriv dAC + mDeriv dB + mDeriv dBD
mDerivBody (iSigma da db dSigma) = mDeriv da + mDeriv db + mDeriv dSigma
mDerivBody (iSigmaEq dac dbd dA dB) = mDeriv dac + mDeriv dbd + mDeriv dA + mDeriv dB
mDerivBody (eSigma dM dd dm) = mDeriv dM + mDeriv dd + mDeriv dm
mDerivBody (eSigmaEq dM dd dm dm') = mDeriv dM + mDeriv dd + mDeriv dm + mDeriv dm'
mDerivBody (cSigma dM dSigma db dc dm) =
  mDeriv dM + mDeriv dSigma + mDeriv db + mDeriv dc + mDeriv dm
mDerivBody (fEq dA da db) = mDeriv dA + mDeriv da + mDeriv db
mDerivBody (fEqEq dAC dac dbd) = mDeriv dAC + mDeriv dac + mDeriv dbd
mDerivBody (iEq da) = mDeriv da
mDerivBody (iEqEq dab) = mDeriv dab
mDerivBody (eEqStar dp dA da db) = mDeriv dp + mDeriv dA + mDeriv da + mDeriv db
mDerivBody (cEq dp dA da db) = mDeriv dp + mDeriv dA + mDeriv da + mDeriv db
mDerivBody (fQtr dA) = mDeriv dA
mDerivBody (fQtrEq dAB) = mDeriv dAB
mDerivBody (iQtr da) = mDeriv da
mDerivBody (iQtrEq da db) = mDeriv da + mDeriv db
mDerivBody (eQtr dL dp dBranchTy dl dcoh) =
  mDeriv dL + mDeriv dp + mDeriv dBranchTy + mDeriv dl + mDeriv dcoh
mDerivBody (eQtrEq dL dp dBranchTy dl dl' dll' dcoh dcoh') =
  mDeriv dL + mDeriv dp + mDeriv dBranchTy + mDeriv dl
  + mDeriv dl' + mDeriv dll' + mDeriv dcoh + mDeriv dcoh'
mDerivBody (cQtr dL da dBranchTy dl dcoh) =
  mDeriv dL + mDeriv da + mDeriv dBranchTy + mDeriv dl + mDeriv dcoh
mDerivBody (fNat wf) = mCtxWF wf
mDerivBody (iZero wf) = mCtxWF wf
mDerivBody (iSuc d) = mDeriv d
mDerivBody (iSucEq d) = mDeriv d
mDerivBody (eNat dL dn da dl) = mDeriv dL + mDeriv dn + mDeriv da + mDeriv dl
mDerivBody (eNatEq dL dnn' da daa' dl dll') =
  mDeriv dL + mDeriv dnn' + mDeriv da + mDeriv daa' + mDeriv dl + mDeriv dll'
mDerivBody (cNatZ dL da dl) = mDeriv dL + mDeriv da + mDeriv dl
mDerivBody (cNatS dL dn da dl) = mDeriv dL + mDeriv dn + mDeriv da + mDeriv dl

mCtxWFBody : {gamma : Ctx} -> CtxWF gamma -> ℕ
mCtxWFBody wfNil = zero
mCtxWFBody (wfCons wf dA) = mCtxWF wf + mDeriv dA

mFitsBody : {gamma delta : Ctx} {sigma : Subst} -> FitsSubst gamma delta sigma -> ℕ
mFitsBody (fitsNil wf) = mCtxWF wf
mFitsBody (fitsCons fits dt) = mFits fits + mDeriv dt

mFitsEqBody : {gamma delta : Ctx} {sigma tau : Subst} -> FitsEqSubst gamma delta sigma tau -> ℕ
mFitsEqBody (fitsEqNil wf) = mCtxWF wf
mFitsEqBody (fitsEqCons fitsEq dtu) = mFitsEq fitsEq + mDeriv dtu

mDeriv≡sucBody : {J : JForm} -> (d : Derivable J) -> mDeriv d ≡ suc (mDerivBody d)
mDeriv≡sucBody (varStar wf dA) = refl
mDeriv≡sucBody (weakenTy d wf) = refl
mDeriv≡sucBody (weakenTyEq d wf) = refl
mDeriv≡sucBody (weakenTm d wf) = refl
mDeriv≡sucBody (weakenTmEq d wf) = refl
mDeriv≡sucBody (reflTy d) = refl
mDeriv≡sucBody (reflTm d) = refl
mDeriv≡sucBody (symTy d dB) = refl
mDeriv≡sucBody (symTm d du dA) = refl
mDeriv≡sucBody (transTy d₁ d₂) = refl
mDeriv≡sucBody (transTm d₁ d₂) = refl
mDeriv≡sucBody (conv d dAB) = refl
mDeriv≡sucBody (convEq d dAB) = refl
mDeriv≡sucBody (substTyRule d fits) = refl
mDeriv≡sucBody (substTyEqRule d fits) = refl
mDeriv≡sucBody (substTmRule d fits) = refl
mDeriv≡sucBody (substTmEqRule d fits) = refl
mDeriv≡sucBody (eqSubTyRule d fitsEq) = refl
mDeriv≡sucBody (eqSubTyEqRule d fitsEq) = refl
mDeriv≡sucBody (eqSubTmRule d fitsEq) = refl
mDeriv≡sucBody (eqSubTmEqRule d fitsEq) = refl
mDeriv≡sucBody (fTop wf) = refl
mDeriv≡sucBody (iTop wf) = refl
mDeriv≡sucBody (cTop d) = refl
mDeriv≡sucBody (fSigma dA dB) = refl
mDeriv≡sucBody (fSigmaEq dAC dB dBD) = refl
mDeriv≡sucBody (iSigma da db dSigma) = refl
mDeriv≡sucBody (iSigmaEq dac dbd dA dB) = refl
mDeriv≡sucBody (eSigma dM dd dm) = refl
mDeriv≡sucBody (eSigmaEq dM dd dm dm') = refl
mDeriv≡sucBody (cSigma dM dSigma db dc dm) = refl
mDeriv≡sucBody (fEq dA da db) = refl
mDeriv≡sucBody (fEqEq dAC dac dbd) = refl
mDeriv≡sucBody (iEq da) = refl
mDeriv≡sucBody (iEqEq dab) = refl
mDeriv≡sucBody (eEqStar dp dA da db) = refl
mDeriv≡sucBody (cEq dp dA da db) = refl
mDeriv≡sucBody (fQtr dA) = refl
mDeriv≡sucBody (fQtrEq dAB) = refl
mDeriv≡sucBody (iQtr da) = refl
mDeriv≡sucBody (iQtrEq da db) = refl
mDeriv≡sucBody (eQtr dL dp dBranchTy dl dcoh) = refl
mDeriv≡sucBody (eQtrEq dL dp dBranchTy dl dl' dll' dcoh dcoh') = refl
mDeriv≡sucBody (cQtr dL da dBranchTy dl dcoh) = refl
mDeriv≡sucBody (fNat wf) = refl
mDeriv≡sucBody (iZero wf) = refl
mDeriv≡sucBody (iSuc d) = refl
mDeriv≡sucBody (iSucEq d) = refl
mDeriv≡sucBody (eNat dL dn da dl) = refl
mDeriv≡sucBody (eNatEq dL dnn' da daa' dl dll') = refl
mDeriv≡sucBody (cNatZ dL da dl) = refl
mDeriv≡sucBody (cNatS dL dn da dl) = refl

mCtxWF≡sucBody : {gamma : Ctx} -> (wf : CtxWF gamma) -> mCtxWF wf ≡ suc (mCtxWFBody wf)
mCtxWF≡sucBody wfNil = refl
mCtxWF≡sucBody (wfCons wf dA) = refl

mFits≡sucBody : {gamma delta : Ctx} {sigma : Subst}
  -> (fits : FitsSubst gamma delta sigma) -> mFits fits ≡ suc (mFitsBody fits)
mFits≡sucBody (fitsNil wf) = refl
mFits≡sucBody (fitsCons fits dt) = refl

mFitsEq≡sucBody : {gamma delta : Ctx} {sigma tau : Subst}
  -> (fitsEq : FitsEqSubst gamma delta sigma tau) -> mFitsEq fitsEq ≡ suc (mFitsEqBody fitsEq)
mFitsEq≡sucBody (fitsEqNil wf) = refl
mFitsEq≡sucBody (fitsEqCons fitsEq dtu) = refl

mDeriv-summand< : {J : JForm} -> (d : Derivable J) {n : ℕ}
  -> n ≤ mDerivBody d -> n < mDeriv d
mDeriv-summand< d {n} n≤body =
  subst (λ k -> n < k) (sym (mDeriv≡sucBody d)) (<-suc-of-≤ n≤body)

mCtxWF-summand< : {gamma : Ctx} -> (wf : CtxWF gamma) {n : ℕ}
  -> n ≤ mCtxWFBody wf -> n < mCtxWF wf
mCtxWF-summand< wf {n} n≤body =
  subst (λ k -> n < k) (sym (mCtxWF≡sucBody wf)) (<-suc-of-≤ n≤body)

mFits-summand< : {gamma delta : Ctx} {sigma : Subst}
  -> (fits : FitsSubst gamma delta sigma) {n : ℕ}
  -> n ≤ mFitsBody fits -> n < mFits fits
mFits-summand< fits {n} n≤body =
  subst (λ k -> n < k) (sym (mFits≡sucBody fits)) (<-suc-of-≤ n≤body)

mFitsEq-summand< : {gamma delta : Ctx} {sigma tau : Subst}
  -> (fitsEq : FitsEqSubst gamma delta sigma tau) {n : ℕ}
  -> n ≤ mFitsEqBody fitsEq -> n < mFitsEq fitsEq
mFitsEq-summand< fitsEq {n} n≤body =
  subst (λ k -> n < k) (sym (mFitsEq≡sucBody fitsEq)) (<-suc-of-≤ n≤body)

mCtxWF-wfCons-wf< : {gamma : Ctx} {A : RawType}
  -> (wf : CtxWF gamma)
  -> (dA : Derivable (isType gamma A))
  -> mCtxWF wf < mCtxWF (wfCons wf dA)
mCtxWF-wfCons-wf< wf dA = mCtxWF-summand< (wfCons wf dA) ≤-sum-l

mCtxWF-wfCons-deriv< : {gamma : Ctx} {A : RawType}
  -> (wf : CtxWF gamma)
  -> (dA : Derivable (isType gamma A))
  -> mDeriv dA < mCtxWF (wfCons wf dA)
mCtxWF-wfCons-deriv< wf dA = mCtxWF-summand< (wfCons wf dA) ≤-sum-r

mFits-fitsNil-wf< : {gamma delta : Ctx} {sigma : Subst}
  -> (wf : CtxWF gamma)
  -> mCtxWF wf < mFits (fitsNil {delta = delta} {sigma = sigma} wf)
mFits-fitsNil-wf< {delta = delta} {sigma = sigma} wf =
  mFits-summand< (fitsNil {delta = delta} {sigma = sigma} wf) ≤-refl

mFits-fitsCons-fits< : {gamma delta : Ctx} {sigma : Subst} {A : RawType} {t : RawTerm}
  -> (fits : FitsSubst gamma delta sigma)
  -> (dt : Derivable (hasTy gamma t (subTy sigma A)))
  -> mFits fits < mFits (fitsCons fits dt)
mFits-fitsCons-fits< fits dt = mFits-summand< (fitsCons fits dt) ≤-sum-l

mFits-fitsCons-deriv< : {gamma delta : Ctx} {sigma : Subst} {A : RawType} {t : RawTerm}
  -> (fits : FitsSubst gamma delta sigma)
  -> (dt : Derivable (hasTy gamma t (subTy sigma A)))
  -> mDeriv dt < mFits (fitsCons fits dt)
mFits-fitsCons-deriv< fits dt = mFits-summand< (fitsCons fits dt) ≤-sum-r

mFitsEq-fitsEqNil-wf< : {gamma delta : Ctx} {sigma tau : Subst}
  -> (wf : CtxWF gamma)
  -> mCtxWF wf < mFitsEq (fitsEqNil {delta = delta} {sigma = sigma} {tau = tau} wf)
mFitsEq-fitsEqNil-wf< {delta = delta} {sigma = sigma} {tau = tau} wf =
  mFitsEq-summand< (fitsEqNil {delta = delta} {sigma = sigma} {tau = tau} wf) ≤-refl

mFitsEq-fitsEqCons-fitsEq< : {gamma delta : Ctx} {sigma tau : Subst}
    {A : RawType} {t u : RawTerm}
  -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> (dtu : Derivable (termEq gamma t u (subTy sigma A)))
  -> mFitsEq fitsEq < mFitsEq (fitsEqCons fitsEq dtu)
mFitsEq-fitsEqCons-fitsEq< fitsEq dtu =
  mFitsEq-summand< (fitsEqCons fitsEq dtu) ≤-sum-l

mFitsEq-fitsEqCons-deriv< : {gamma delta : Ctx} {sigma tau : Subst}
    {A : RawType} {t u : RawTerm}
  -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> (dtu : Derivable (termEq gamma t u (subTy sigma A)))
  -> mDeriv dtu < mFitsEq (fitsEqCons fitsEq dtu)
mFitsEq-fitsEqCons-deriv< fitsEq dtu =
  mFitsEq-summand< (fitsEqCons fitsEq dtu) ≤-sum-r
