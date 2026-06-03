{-# OPTIONS --safe #-}

module Recursive.Fundamental.MeasureLemmas where

open import Recursive.Prelude
open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; _≤_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wf)
import Data.Nat.Properties as NatProps
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; <⇒≤ ; +-mono-≤ ; +-mono-<-≤)
open import Data.Product using (Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc ; acc)

open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Evaluation
open import Recursive.Derivability
open import Recursive.Measure
open import Recursive.Computable
open import Recursive.CompLemmas
open import Recursive.Env
open import Recursive.Presupposition
open import Recursive.FundMeasure
open import Recursive.Fundamental.SumLemmas
open import Recursive.Fundamental.Infrastructure
open import Recursive.Fundamental.ComputabilityLemmas public
mutual
  mDeriv-ctxWF≤ : {J : JForm} -> (d : Derivable J)
    -> mCtxWF (derivToCtxWF d) ≤ mDeriv d
  mDeriv-ctxWF≤ d@(varStar wf _) =
    <⇒≤ (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(weakenTy _ wf) =
    <⇒≤ (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(weakenTyEq _ wf) =
    <⇒≤ (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(weakenTm _ wf) =
    <⇒≤ (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(weakenTmEq _ wf) =
    <⇒≤ (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(reflTy dA) =
    ≤-via-< (mDeriv-ctxWF≤ dA) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(reflTm dt) =
    ≤-via-< (mDeriv-ctxWF≤ dt) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(symTy dAB dB) =
    ≤-via-< (mDeriv-ctxWF≤ dAB) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(symTm dtu du dA) =
    ≤-via-< (mDeriv-ctxWF≤ dtu)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv dtu) (mDeriv du) (mDeriv dA)))
  mDeriv-ctxWF≤ d@(transTy dAB dBC) =
    ≤-via-< (mDeriv-ctxWF≤ dAB) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(transTm dtu duv) =
    ≤-via-< (mDeriv-ctxWF≤ dtu) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(conv dt dAB) =
    ≤-via-< (mDeriv-ctxWF≤ dt) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(convEq dtu dAB) =
    ≤-via-< (mDeriv-ctxWF≤ dtu) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(substTyRule dA fits) =
    ≤-via-< (mFits-ctxWF≤ fits) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(substTyEqRule dAB fits) =
    ≤-via-< (mFits-ctxWF≤ fits) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(substTmRule dt fits) =
    ≤-via-< (mFits-ctxWF≤ fits) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(substTmEqRule dtu fits) =
    ≤-via-< (mFits-ctxWF≤ fits) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(eqSubTyRule dA fitsEq) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(eqSubTyEqRule dAB fitsEq) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(eqSubTmRule dt fitsEq) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(eqSubTmEqRule dtu fitsEq) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(fTop wf) =
    <⇒≤ (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(iTop wf) =
    <⇒≤ (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(cTop dt) =
    ≤-via-< (mDeriv-ctxWF≤ dt) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(fSigma dA dB) =
    ≤-via-< (mDeriv-ctxWF≤ dA) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(fSigmaEq dAC dB dBD) =
    ≤-via-< (mDeriv-ctxWF≤ dAC)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv dAC) (mDeriv dB) (mDeriv dBD)))
  mDeriv-ctxWF≤ d@(iSigma da db dSigma) =
    ≤-via-< (mDeriv-ctxWF≤ da)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv da) (mDeriv db) (mDeriv dSigma)))
  mDeriv-ctxWF≤ d@(iSigmaEq dac dbd dA dB) =
    ≤-via-< (mDeriv-ctxWF≤ dac)
      (mDeriv-summand< d (≤-sum1-4 (mDeriv dac) (mDeriv dbd) (mDeriv dA) (mDeriv dB)))
  mDeriv-ctxWF≤ d@(eSigma dM dd dm) =
    ≤-via-< (mDeriv-ctxWF≤ dd)
      (mDeriv-summand< d (≤-sum2-3 (mDeriv dM) (mDeriv dd) (mDeriv dm)))
  mDeriv-ctxWF≤ d@(eSigmaEq dM dd dm dmEq) =
    ≤-via-< (mDeriv-ctxWF≤ dd)
      (mDeriv-summand< d (≤-sum2-4 (mDeriv dM) (mDeriv dd) (mDeriv dm) (mDeriv dmEq)))
  mDeriv-ctxWF≤ d@(cSigma dM dSigma db dc dm) =
    ≤-via-< (mDeriv-ctxWF≤ db)
      (mDeriv-summand< d
        (≤-sum3-5 (mDeriv dM) (mDeriv dSigma) (mDeriv db) (mDeriv dc) (mDeriv dm)))
  mDeriv-ctxWF≤ d@(fEq dA da db) =
    ≤-via-< (mDeriv-ctxWF≤ dA)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv dA) (mDeriv da) (mDeriv db)))
  mDeriv-ctxWF≤ d@(fEqEq dAC dac dbd) =
    ≤-via-< (mDeriv-ctxWF≤ dAC)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv dAC) (mDeriv dac) (mDeriv dbd)))
  mDeriv-ctxWF≤ d@(iEq da) =
    ≤-via-< (mDeriv-ctxWF≤ da) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(iEqEq dab) =
    ≤-via-< (mDeriv-ctxWF≤ dab) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(eEqStar dp dA da db) =
    ≤-via-< (mDeriv-ctxWF≤ dp)
      (mDeriv-summand< d (≤-sum1-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db)))
  mDeriv-ctxWF≤ d@(cEq dp dA da db) =
    ≤-via-< (mDeriv-ctxWF≤ dp)
      (mDeriv-summand< d (≤-sum1-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db)))
  mDeriv-ctxWF≤ d@(fQtr dA) =
    ≤-via-< (mDeriv-ctxWF≤ dA) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(fQtrEq dAB) =
    ≤-via-< (mDeriv-ctxWF≤ dAB) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(iQtr da) =
    ≤-via-< (mDeriv-ctxWF≤ da) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(iQtrEq da db) =
    ≤-via-< (mDeriv-ctxWF≤ da) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(eQtr dL dp dBranch dl dcoh) =
    ≤-via-< (mDeriv-ctxWF≤ dp)
      (mDeriv-summand< d
        (≤-sum2-5 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl) (mDeriv dcoh)))
  mDeriv-ctxWF≤ d@(eQtrEq dL dp dBranch dl dl' dll' dcoh dcoh') =
    ≤-via-< (mDeriv-ctxWF≤ dp)
      (mDeriv-summand< d
        (≤-sum2-8 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl)
          (mDeriv dl') (mDeriv dll') (mDeriv dcoh) (mDeriv dcoh')))
  mDeriv-ctxWF≤ d@(cQtr dL da dBranch dl dcoh) =
    ≤-via-< (mDeriv-ctxWF≤ da)
      (mDeriv-summand< d
        (≤-sum2-5 (mDeriv dL) (mDeriv da) (mDeriv dBranch) (mDeriv dl) (mDeriv dcoh)))

  mFits-ctxWF≤ : {gamma delta : Ctx} {sigma : Subst}
    -> (fits : FitsSubst gamma delta sigma)
    -> mCtxWF (fitsSubstCtxWF fits) ≤ mFits fits
  mFits-ctxWF≤ (fitsNil {delta = delta} {sigma = sigma} wf) =
    <⇒≤ (mFits-fitsNil-wf< {delta = delta} {sigma = sigma} wf)
  mFits-ctxWF≤ (fitsCons fits dt) =
    ≤-via-< (mFits-ctxWF≤ fits) (mFits-fitsCons-fits< fits dt)

  mFitsEq-ctxWF≤ : {gamma delta : Ctx} {sigma tau : Subst}
    -> (fitsEq : FitsEqSubst gamma delta sigma tau)
    -> mCtxWF (fitsEqSubstCtxWF fitsEq) ≤ mFitsEq fitsEq
  mFitsEq-ctxWF≤ (fitsEqNil {delta = delta} {sigma = sigma} {tau = tau} wf) =
    <⇒≤ (mFitsEq-fitsEqNil-wf< {delta = delta} {sigma = sigma} {tau = tau} wf)
  mFitsEq-ctxWF≤ (fitsEqCons fitsEq dtu) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mFitsEq-fitsEqCons-fitsEq< fitsEq dtu)

fitsEqCtxMeasure<Deriv : {J : JForm} {gamma delta : Ctx} {sigma tau : Subst}
  -> (d : Derivable J)
  -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> mFitsEq fitsEq + mCtxWF (derivToCtxWF d) < suc (mDeriv d + mFitsEq fitsEq)
fitsEqCtxMeasure<Deriv d fitsEq =
  <-suc-of-≤
    (≤-trans
      (+-mono-≤ ≤-refl (mDeriv-ctxWF≤ d))
      (NatProps.≤-reflexive (NatProps.+-comm (mFitsEq fitsEq) (mDeriv d))))

fitsEqCtx-tail< : {gamma delta : Ctx} {sigma tau : Subst}
    {A : RawType} {t u : RawTerm}
  -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> (dtu : Derivable (termEq gamma t u (subTy sigma A)))
  -> (wfΔ : CtxWF delta)
  -> (dA : Derivable (isType delta A))
  -> mFitsEq fitsEq + mCtxWF wfΔ
     < mFitsEq (fitsEqCons fitsEq dtu) + mCtxWF (wfCons wfΔ dA)
fitsEqCtx-tail< fitsEq dtu wfΔ dA =
  +-mono-<-≤
    (mFitsEq-fitsEqCons-fitsEq< fitsEq dtu)
    (<⇒≤ (mCtxWF-wfCons-wf< wfΔ dA))

fitsEqCtx-headDeriv< : {gamma delta : Ctx} {sigma tau : Subst}
    {A : RawType} {t u : RawTerm}
  -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> (dtu : Derivable (termEq gamma t u (subTy sigma A)))
  -> (wfΔ : CtxWF delta)
  -> (dA : Derivable (isType delta A))
  -> mDeriv dA
     < mFitsEq (fitsEqCons fitsEq dtu) + mCtxWF (wfCons wfΔ dA)
fitsEqCtx-headDeriv< fitsEq dtu wfΔ dA =
  ≤-trans (mCtxWF-wfCons-deriv< wfΔ dA)
    (≤-sum-r {m = mCtxWF (wfCons wfΔ dA)} {n = mFitsEq (fitsEqCons fitsEq dtu)})
