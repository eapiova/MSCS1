{-# OPTIONS --safe #-}

module Tait.Fundamental.Core where

open import Tait.Prelude
open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; _≤_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wf)
import Data.Nat.Properties as NatProps
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; <⇒≤ ; +-mono-≤ ; +-mono-<-≤)
open import Data.Product using (Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc ; acc)

open import Tait.Syntax
open import Tait.Context
open import Tait.Substitution
open import Tait.Evaluation
open import Tait.Derivability
open import Tait.Measure
open import Tait.Computable
open import Tait.CompLemmas
open import Tait.Env
open import Tait.Presupposition
open import Tait.FundMeasure
open import Tait.Fundamental.SumLemmas
open import Tait.Fundamental.Infrastructure
open import Tait.Fundamental.ComputabilityLemmas public
open import Tait.Fundamental.MeasureLemmas public

mutual
  fundTyEqEnv : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> (d : Derivable (isType gamma A)) -> Acc _<_ (mDeriv d) -> EqEnv gamma sigma tau
    -> ComputableTyEq (subTy sigma A) (subTy tau A)
  fundTyEqEnv {sigma = sigma} {tau = tau}
    d@(weakenTy {delta = delta} {A = A} dA wf) (acc rec) ee =
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) A))
      (fundTyEqEnv dA
        (rec {y = mDeriv dA} (mDeriv-summand< d ≤-sum-l))
        (eqEnvDrop {delta = delta} ee))
  fundTyEqEnv {sigma = sigma} {tau = tau}
    d@(substTyRule {sigma = theta} {A = A} dA fits) (acc rec) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      (fundTyEqEnv dA
        (rec {y = mDeriv dA} (mDeriv-summand< d ≤-sum-l))
        (fundFitsSameEq fits
          (rec {y = mFits fits} (mDeriv-summand< d ≤-sum-r))
          ee))
  fundTyEqEnv (fTop wf) _ ee = tt
  fundTyEqEnv {sigma = sigma} {tau = tau} d@(fSigma {A = A} {B = B} dA dB) (acc rec) ee =
    let tyA = fundTyEqEnv dA (rec {y = mDeriv dA} (mDeriv-summand< d ≤-sum-l)) ee in
    computableTyEqSigma-intro
      {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
      {C = subTy tau A} {D = subTy (liftSubst tau) B}
      tyA
    λ a c eq ->
      compTyEq-subst
        (singleLiftTy a sigma B)
        (singleLiftTy c tau B)
        (fundTyEqEnv dB
          (rec {y = mDeriv dB} (mDeriv-summand< d ≤-sum-r))
          (eqEnvCons ee tyA eq))
  fundTyEqEnv {sigma = sigma} {tau = tau} d@(fEq {A = A} {a = a} {b = b} dA da db) (acc rec) ee =
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau A}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau a} {d = subTm tau b}
      (fundTyEqEnv dA
        (rec {y = mDeriv dA}
          (mDeriv-summand< d (≤-sum1-3 (mDeriv dA) (mDeriv da) (mDeriv db))))
        ee)
      (proj₁
        (fundTmEqEnv da
          (rec {y = mDeriv da}
            (mDeriv-summand< d (≤-sum2-3 (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee))
      (proj₁
        (fundTmEqEnv db
          (rec {y = mDeriv db}
            (mDeriv-summand< d (≤-sum3-3 (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee))
  fundTyEqEnv {sigma = sigma} {tau = tau} d@(fQtr {A = A} dA) (acc rec) ee =
    computableTyEqQtr-intro
      {A = subTy sigma A} {C = subTy tau A}
      (fundTyEqEnv dA (rec {y = mDeriv dA} (mDeriv-summand< d ≤-refl)) ee)

  fundTyEqEqEnv : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> (d : Derivable (typeEq gamma A B)) -> Acc _<_ (mDeriv d) -> EqEnv gamma sigma tau
    -> ComputableTyEq (subTy sigma A) (subTy tau B)
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    d@(weakenTyEq {delta = delta} {A = A} {B = B} dAB wf) (acc rec) ee =
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) B))
      (fundTyEqEqEnv dAB
        (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-l))
        (eqEnvDrop {delta = delta} ee))
  fundTyEqEqEnv d@(reflTy dA) (acc rec) ee =
    fundTyEqEnv dA (rec {y = mDeriv dA} (mDeriv-summand< d ≤-refl)) ee
  fundTyEqEqEnv {sigma = sigma} {tau = tau} d@(symTy {A = A} {B = B} dAB dB) (acc rec) ee =
    compTyEq-trans
      {A = subTy sigma B} {B = subTy tau B} {C = subTy tau A}
      (fundTyEqEnv dB (rec {y = mDeriv dB} (mDeriv-summand< d ≤-sum-r)) ee)
      (compTyEq-sym {A = subTy tau A} {B = subTy tau B}
        (fundTyEqEqEnv dAB
          (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-l))
          (eqEnvReflRight ee)))
  fundTyEqEqEnv {sigma = sigma} {tau = tau} d@(transTy {A = A} {B = B} {C = C} dAB dBC) (acc rec) ee =
    compTyEq-trans
      {A = subTy sigma A} {B = subTy tau B} {C = subTy tau C}
      (fundTyEqEqEnv dAB (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-l)) ee)
      (fundTyEqEqEnv dBC
        (rec {y = mDeriv dBC} (mDeriv-summand< d ≤-sum-r))
        (eqEnvReflRight ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    d@(substTyEqRule {sigma = theta} {A = A} {B = B} dAB fits) (acc rec) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta B))
      (fundTyEqEqEnv dAB
        (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-l))
        (fundFitsSameEq fits
          (rec {y = mFits fits} (mDeriv-summand< d ≤-sum-r))
          ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eqSubTyRule {sigma = theta} {tau = eta} {A = A} d fitsEq) (acc rec) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau eta A))
      (fundTyEqEnv d
        (rec {y = mDeriv d} (mDeriv-summand< dAll ≤-sum-l))
        (fundFitsEqEnv fitsEq (derivToCtxWF d)
          (rec {y = mFitsEq fitsEq + mCtxWF (derivToCtxWF d)}
            (fitsEqCtxMeasure<Deriv d fitsEq))
          ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eqSubTyEqRule {sigma = theta} {tau = eta} {A = A} {B = B} d fitsEq) (acc rec) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau eta B))
      (fundTyEqEqEnv d
        (rec {y = mDeriv d} (mDeriv-summand< dAll ≤-sum-l))
        (fundFitsEqEnv fitsEq (derivToCtxWF d)
          (rec {y = mFitsEq fitsEq + mCtxWF (derivToCtxWF d)}
            (fitsEqCtxMeasure<Deriv d fitsEq))
          ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    d@(fSigmaEq {A = A} {B = B} {C = C} {D = D} dAC dB dBD) (acc rec) ee =
    let
      accAC =
        rec {y = mDeriv dAC}
          (mDeriv-summand< d (≤-sum1-3 (mDeriv dAC) (mDeriv dB) (mDeriv dBD)))
      tyAC = fundTyEqEqEnv dAC accAC ee
      tyACτ = fundTyEqEqEnv dAC accAC (eqEnvReflRight ee)
      tyA =
        compTyEq-trans
          {A = subTy sigma A} {B = subTy tau C} {C = subTy tau A}
          tyAC
          (compTyEq-sym {A = subTy tau A} {B = subTy tau C} tyACτ)
    in
    computableTyEqSigma-intro
      {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
      {C = subTy tau C} {D = subTy (liftSubst tau) D}
      tyAC
    λ a c eq ->
      compTyEq-subst
        (singleLiftTy a sigma B)
        (singleLiftTy c tau D)
        (fundTyEqEqEnv dBD
          (rec {y = mDeriv dBD}
            (mDeriv-summand< d (≤-sum3-3 (mDeriv dAC) (mDeriv dB) (mDeriv dBD))))
          (eqEnvCons ee tyA eq))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    d@(fEqEq {A = A} {C = C} {a = a} {b = b} {c = c} {d = d0} dAC daeq dbeq) (acc rec) ee =
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau C}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau c} {d = subTm tau d0}
      (fundTyEqEqEnv dAC
        (rec {y = mDeriv dAC}
          (mDeriv-summand< d (≤-sum1-3 (mDeriv dAC) (mDeriv daeq) (mDeriv dbeq))))
        ee)
      (proj₁
        (fundTmEqEqEnv daeq
          (rec {y = mDeriv daeq}
            (mDeriv-summand< d (≤-sum2-3 (mDeriv dAC) (mDeriv daeq) (mDeriv dbeq))))
          ee))
      (proj₁
        (fundTmEqEqEnv dbeq
          (rec {y = mDeriv dbeq}
            (mDeriv-summand< d (≤-sum3-3 (mDeriv dAC) (mDeriv daeq) (mDeriv dbeq))))
          ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau} d@(fQtrEq {A = A} {B = B} dAB) (acc rec) ee =
    computableTyEqQtr-intro
      {A = subTy sigma A} {C = subTy tau B}
      (fundTyEqEqEnv dAB (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-refl)) ee)

  fundTmEqEnv : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> (d : Derivable (hasTy gamma t A)) -> Acc _<_ (mDeriv d) -> EqEnv gamma sigma tau
    -> ComputableTmEq (subTy sigma A) (subTm sigma t) (subTm tau t)
       × ComputableTyEq (subTy sigma A) (subTy tau A)
  fundTmEqEnv (varStar wf dA) _ ee =
    eqEnvLookup ee , eqEnvLookupTy ee
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(weakenTm {delta = delta} {t = t} {A = A} dt wf) (acc rec) ee =
    let tm , ty = fundTmEqEnv dt
          (rec {y = mDeriv dt} (mDeriv-summand< d ≤-sum-l))
          (eqEnvDrop {delta = delta} ee)
    in
    compTmEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTmRen sigma (addRen (length delta)) t))
      (sym (subTmRen tau (addRen (length delta)) t))
      tm ,
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) A))
      ty
  fundTmEqEnv {A = B} {sigma = sigma} {tau = tau}
    d@(conv {A = A} {B = B} dt dAB) (acc rec) ee =
    let
      tm , tyA = fundTmEqEnv dt
        (rec {y = mDeriv dt} (mDeriv-summand< d ≤-sum-l))
        ee
      accAB = rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-r)
      tyABσ = fundTyEqEqEnv dAB accAB (eqEnvReflLeft ee)
      tyABστ = fundTyEqEqEnv dAB accAB ee
      tyB =
        compTyEq-trans
          {A = subTy sigma B} {B = subTy sigma A} {C = subTy tau B}
          (compTyEq-sym {A = subTy sigma A} {B = subTy sigma B} tyABσ)
          tyABστ
    in
    compTmEq-conv {A = subTy sigma A} {B = subTy sigma B} tyABσ tm , tyB
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(substTmRule {sigma = theta} {t = t} {A = A} dt fits) (acc rec) ee =
    let tm , ty = fundTmEqEnv dt
          (rec {y = mDeriv dt} (mDeriv-summand< d ≤-sum-l))
          (fundFitsSameEq fits
            (rec {y = mFits fits} (mDeriv-summand< d ≤-sum-r))
            ee)
    in
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau theta t))
      tm ,
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      ty
  fundTmEqEnv (iTop wf) _ ee = (evalStar , evalStar) , tt
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(iSigma {a = a} {b = b} {A = A} {B = B} da db dSig) (acc rec) ee =
    let
      caeq , tyA =
        fundTmEqEnv da
          (rec {y = mDeriv da}
            (mDeriv-summand< d (≤-sum1-3 (mDeriv da) (mDeriv db) (mDeriv dSig))))
          ee
      tySig =
        fundTyEqEnv dSig
          (rec {y = mDeriv dSig}
            (mDeriv-summand< d (≤-sum3-3 (mDeriv da) (mDeriv db) (mDeriv dSig))))
          ee
      _ , famB =
        computableTySigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          (proj₁
            (compTyEq-sides
              {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
              {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
              tySig))
      tyB = famB (subTm sigma a) (subTm tau a) caeq
      cbeq =
        compTmEq-subst
          (subTyComp sigma (singleSubst a) B
           ∙ singleLiftTy (subTm sigma a) sigma B)
          refl refl
          (proj₁
            (fundTmEqEnv db
              (rec {y = mDeriv db}
                (mDeriv-summand< d (≤-sum2-3 (mDeriv da) (mDeriv db) (mDeriv dSig))))
              ee))
    in
    computableTmEqSigma-intro
      {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau a} {d = subTm tau b}
      caeq cbeq tyB ,
    tySig
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(eSigma {A = A} {B = B} {M = M} {d = d0} {m = m} dM dd dm) (acc rec) ee =
    let
      accM =
        rec {y = mDeriv dM}
          (mDeriv-summand< d (≤-sum1-3 (mDeriv dM) (mDeriv dd) (mDeriv dm)))
      accd =
        rec {y = mDeriv dd}
          (mDeriv-summand< d (≤-sum2-3 (mDeriv dM) (mDeriv dd) (mDeriv dm)))
      accm =
        rec {y = mDeriv dm}
          (mDeriv-summand< d (≤-sum3-3 (mDeriv dM) (mDeriv dd) (mDeriv dm)))
      ddEq , tySig = fundTmEqEnv dd accd ee
      tyA , famB =
        computableTyEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {C = subTy tau A} {D = subTy (liftSubst tau) B}
          tySig
      cSig =
        proj₁
          (compTyEq-sides
            {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
            {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
            tySig)
      ctyA , famLeft =
        computableTySigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          cSig
      b , c , e , f , evd , eve , eqB , eqCraw , tyCraw =
        computableTmEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {t = subTm sigma d0} {u = subTm tau d0}
          ddEq
      cb = proj₁ (compTmEq-sides {A = subTy sigma A} eqB)
      ccRaw =
        proj₁
          (compTmEq-sides
            {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            eqCraw)
      eqBB = compTmEq-refl {A = subTy sigma A} ctyA cb
      tyBB = famLeft b b eqBB
      ctyB =
        proj₁
          (compTyEq-sides
            {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            {B = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            tyBB)
      eqCC =
        compTmEq-refl
          {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
          ctyB ccRaw
      eqDPair =
        computableTmEqSigma-eval-intro
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {t = subTm sigma d0} {u = tmPair b c}
          {a = b} {b = c} {c = b} {d = c}
          evd evalPair eqBB eqCC tyBB
      tyDPairRaw =
        fundTyEqEnv dM accM
          (eqEnvCons
            (eqEnvReflLeft ee)
            (compTyEq-refl {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)} cSig)
            eqDPair)
      tyDPair =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst d0) M))
          refl
          tyDPairRaw
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst d0) M))
          (sym (subTyComp tau (singleSubst d0) M))
          (fundTyEqEnv dM accM (eqEnvCons ee tySig ddEq))
      tyC =
        compTyEq-subst
          (sym (singleLiftTy b sigma B))
          (sym (singleLiftTy e tau B))
          (famB b e eqB)
      eqC =
        compTmEq-subst (sym (singleLiftTy b sigma B)) refl refl eqCraw
      branchEq =
        proj₁ (fundTmEqEnv dm accm (eqEnvCons (eqEnvCons ee tyA eqB) tyC eqC))
      eqSources =
        compTmEq-subst
          (sigmaBranchTargetTy b c sigma M)
          (sym (sigmaCompLiftTm b c sigma m))
          (sym (sigmaCompLiftTm e f tau m))
          branchEq
    in
    compTmEq-conv
      {A = subTy (consSubst (tmPair b c) sigma) M}
      {B = subTy sigma (subTy (singleSubst d0) M)}
      (compTyEq-sym
        {A = subTy sigma (subTy (singleSubst d0) M)}
        {B = subTy (consSubst (tmPair b c) sigma) M}
        tyDPair)
      (compTmEqElimRight eve (compTmEqElimLeft evd eqSources)) ,
    tyResult
  fundTmEqEnv {sigma = sigma} {tau = tau} d@(iEq {A = A} {a = a} da) (acc rec) ee =
    let
      eqA , tyA =
        fundTmEqEnv da (rec {y = mDeriv da} (mDeriv-summand< d ≤-refl)) ee
      ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} eqA)
    in
    computableTmEqEqForm-intro
      {A = subTy sigma A} {a = subTm sigma a} {b = subTm sigma a}
      {t = tmRefl} {u = tmRefl}
      evalRefl evalRefl (compTmEq-refl {A = subTy sigma A} ctyA ca) ,
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau A}
      {a = subTm sigma a} {b = subTm sigma a}
      {c = subTm tau a} {d = subTm tau a}
      tyA eqA eqA
  fundTmEqEnv {sigma = sigma} {tau = tau} d@(iQtr {A = A} {a = a} da) (acc rec) ee =
    let
      eqA , tyA =
        fundTmEqEnv da (rec {y = mDeriv da} (mDeriv-summand< d ≤-refl)) ee
      ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      ca , ca' = compTmEq-sides {A = subTy sigma A} eqA
    in
    computableTmEqQtr-intro
      {A = subTy sigma A}
      {t = tmClass (subTm sigma a)} {u = tmClass (subTm tau a)}
      {p = subTm sigma a} {q = subTm tau a}
      evalClass evalClass
      (compTmEq-refl {A = subTy sigma A} ctyA ca)
      (compTmEq-refl {A = subTy sigma A} ctyA ca') ,
    computableTyEqQtr-intro {A = subTy sigma A} {C = subTy tau A} tyA
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(eQtr {A = A} {L = L} {l = l} {p = p} dL dp dBranch dl coh) (acc rec) ee =
    let
      accL =
        rec {y = mDeriv dL}
          (mDeriv-summand< d
            (≤-sum1-5 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      accp =
        rec {y = mDeriv dp}
          (mDeriv-summand< d
            (≤-sum2-5 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      accCoh =
        rec {y = mDeriv coh}
          (mDeriv-summand< d
            (≤-sum5-5 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      dpEq , tyQtrEq = fundTmEqEnv dp accp ee
      cQtr =
        proj₁
          (compTyEq-sides
            {A = tyQtr (subTy sigma A)} {B = tyQtr (subTy tau A)}
            tyQtrEq)
      tyQ = computableTyEqQtr-elim {A = subTy sigma A} {C = subTy tau A} tyQtrEq
      cQ = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyQ)
      a , b , evp , evp' , caa , cbb =
        computableTmEqQtr-elim
          {A = subTy sigma A} {t = subTm sigma p} {u = subTm tau p}
          dpEq
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} caa)
      eqAA = compTmEq-refl {A = subTy sigma A} cQ ca
      eqPClass =
        computableTmEqQtr-intro
          {A = subTy sigma A}
          {t = subTm sigma p} {u = tmClass a}
          {p = a} {q = a}
          evp evalClass eqAA eqAA
      tyPClassRaw =
        fundTyEqEnv dL accL
          (eqEnvCons
            (eqEnvReflLeft ee)
            (compTyEq-refl {A = tyQtr (subTy sigma A)} cQtr)
            eqPClass)
      tyPClass =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst p) L))
          refl
          tyPClassRaw
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst p) L))
          (sym (subTyComp tau (singleSubst p) L))
          (fundTyEqEnv dL accL (eqEnvCons ee tyQtrEq dpEq))
      tyHead =
        compTyEq-subst
          (sym (lookupHereTy sigma a A))
          (sym (lookupHereTy tau a A))
          tyQ
      headEq =
        compTmEq-subst
          (sym (lookupHereTy sigma a A))
          refl refl
          cbb
      branchEq =
        proj₁ (fundTmEqEqEnv coh accCoh
          (eqEnvCons
            (eqEnvCons ee tyQ caa)
            tyHead
            headEq))
      eqSources =
        compTmEq-subst
          (qtrCohTargetTy a b sigma L)
          (qtrCohLeftTm a b sigma l ∙ sym (qtrCompLiftTm a sigma l))
          (qtrCohRightTm a b tau l ∙ sym (qtrCompLiftTm b tau l))
          branchEq
    in
    compTmEq-conv
      {A = subTy (consSubst (tmClass a) sigma) L}
      {B = subTy sigma (subTy (singleSubst p) L)}
      (compTyEq-sym
        {A = subTy sigma (subTy (singleSubst p) L)}
        {B = subTy (consSubst (tmClass a) sigma) L}
        tyPClass)
      (compTmEqQtrElimRight evp' (compTmEqQtrElimLeft evp eqSources)) ,
    tyResult

  fundTmEqEqEnv : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> (d : Derivable (termEq gamma t u A)) -> Acc _<_ (mDeriv d) -> EqEnv gamma sigma tau
    -> ComputableTmEq (subTy sigma A) (subTm sigma t) (subTm tau u)
       × ComputableTyEq (subTy sigma A) (subTy tau A)
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(weakenTmEq {delta = delta} {t = t} {u = u} {A = A} dtu wf) (acc rec) ee =
    let tm , ty =
          fundTmEqEqEnv dtu
            (rec {y = mDeriv dtu} (mDeriv-summand< d ≤-sum-l))
            (eqEnvDrop {delta = delta} ee)
    in
    compTmEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTmRen sigma (addRen (length delta)) t))
      (sym (subTmRen tau (addRen (length delta)) u))
      tm ,
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) A))
      ty
  fundTmEqEqEnv d@(reflTm dt) (acc rec) ee =
    fundTmEqEnv dt (rec {y = mDeriv dt} (mDeriv-summand< d ≤-refl)) ee
  fundTmEqEqEnv {A = A} {sigma = sigma} {tau = tau}
    d@(symTm {t = t} {u = u} dtu du dA) (acc rec) ee =
    let
      duEq , tyστ =
        fundTmEqEnv du
          (rec {y = mDeriv du}
            (mDeriv-summand< d (≤-sum2-3 (mDeriv dtu) (mDeriv du) (mDeriv dA))))
          ee
      eqRight =
        proj₁
          (fundTmEqEqEnv dtu
            (rec {y = mDeriv dtu}
              (mDeriv-summand< d (≤-sum1-3 (mDeriv dtu) (mDeriv du) (mDeriv dA))))
            (eqEnvReflRight ee))
    in
    compTmEq-trans
      {A = subTy sigma A} {t = subTm sigma u} {u = subTm tau u} {v = subTm tau t}
      duEq
      (compTmEq-conv
        {A = subTy tau A} {B = subTy sigma A}
        (compTyEq-sym {A = subTy sigma A} {B = subTy tau A} tyστ)
        (compTmEq-sym {A = subTy tau A} eqRight)) ,
    tyστ
  fundTmEqEqEnv {A = A} {sigma = sigma} {tau = tau}
    d@(transTm {t = t} {u = u} {v = v} dtu duv) (acc rec) ee =
    let
      dtuEq , tyστ =
        fundTmEqEqEnv dtu (rec {y = mDeriv dtu} (mDeriv-summand< d ≤-sum-l)) ee
      eqRight =
        proj₁
          (fundTmEqEqEnv duv
            (rec {y = mDeriv duv} (mDeriv-summand< d ≤-sum-r))
            (eqEnvReflRight ee))
    in
    compTmEq-trans
      {A = subTy sigma A} {t = subTm sigma t} {u = subTm tau u} {v = subTm tau v}
      dtuEq
      (compTmEq-conv
        {A = subTy tau A} {B = subTy sigma A}
        (compTyEq-sym {A = subTy sigma A} {B = subTy tau A} tyστ)
        eqRight) ,
    tyστ
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(convEq {t = t} {u = u} {A = A} {B = B} dtu dAB) (acc rec) ee =
    let
      tm , tyA =
        fundTmEqEqEnv dtu (rec {y = mDeriv dtu} (mDeriv-summand< d ≤-sum-l)) ee
      accAB = rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-r)
      tyABσ = fundTyEqEqEnv dAB accAB (eqEnvReflLeft ee)
      tyABστ = fundTyEqEqEnv dAB accAB ee
      tyB =
        compTyEq-trans
          {A = subTy sigma B} {B = subTy sigma A} {C = subTy tau B}
          (compTyEq-sym {A = subTy sigma A} {B = subTy sigma B} tyABσ)
          tyABστ
    in
    compTmEq-conv {A = subTy sigma A} {B = subTy sigma B} tyABσ tm , tyB
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(substTmEqRule {sigma = theta} {t = t} {u = u} {A = A} dtu fits) (acc rec) ee =
    let tm , ty =
          fundTmEqEqEnv dtu
            (rec {y = mDeriv dtu} (mDeriv-summand< d ≤-sum-l))
            (fundFitsSameEq fits
              (rec {y = mFits fits} (mDeriv-summand< d ≤-sum-r))
              ee)
    in
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau theta u))
      tm ,
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      ty
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eqSubTmRule {sigma = theta} {tau = eta} {t = t} {A = A} d fitsEq) (acc rec) ee =
    let
      accD = rec {y = mDeriv d} (mDeriv-summand< dAll ≤-sum-l)
      tm , ty =
        fundTmEqEnv d accD
          (fundFitsEqEnv fitsEq (derivToCtxWF d)
            (rec {y = mFitsEq fitsEq + mCtxWF (derivToCtxWF d)}
              (fitsEqCtxMeasure<Deriv d fitsEq))
            ee)
      tmLeft , tyLeft =
        fundTmEqEnv d accD
          (fundFitsEqLeftEnv fitsEq
            (rec {y = mFitsEq fitsEq} (mDeriv-summand< dAll ≤-sum-r))
            ee)
    in
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau eta t))
      tm ,
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      tyLeft
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eqSubTmEqRule {sigma = theta} {tau = eta} {t = t} {u = u} {A = A} d fitsEq) (acc rec) ee =
    let
      accD = rec {y = mDeriv d} (mDeriv-summand< dAll ≤-sum-l)
      tm , ty =
        fundTmEqEqEnv d accD
          (fundFitsEqEnv fitsEq (derivToCtxWF d)
            (rec {y = mFitsEq fitsEq + mCtxWF (derivToCtxWF d)}
              (fitsEqCtxMeasure<Deriv d fitsEq))
            ee)
      tmLeft , tyLeft =
        fundTmEqEqEnv d accD
          (fundFitsEqLeftEnv fitsEq
            (rec {y = mFitsEq fitsEq} (mDeriv-summand< dAll ≤-sum-r))
            ee)
    in
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau eta u))
      tm ,
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      tyLeft
  fundTmEqEqEnv d@(cTop dt) (acc rec) ee =
    let tm , ty = fundTmEqEnv dt (rec {y = mDeriv dt} (mDeriv-summand< d ≤-refl)) ee in
    (proj₁ tm , evalStar) , tt
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(iSigmaEq {a = a} {b = b} {c = c} {d = d0} {A = A} {B = B} daeq dbeq dA dB) (acc rec) ee =
    let
      caeq , tyA =
        fundTmEqEqEnv daeq
          (rec {y = mDeriv daeq}
            (mDeriv-summand< d
              (≤-sum1-4 (mDeriv daeq) (mDeriv dbeq) (mDeriv dA) (mDeriv dB))))
          ee
      tySig =
        computableTyEqSigma-intro
        {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
        {C = subTy tau A} {D = subTy (liftSubst tau) B}
        tyA
        λ x y eq ->
          compTyEq-subst
            (singleLiftTy x sigma B)
            (singleLiftTy y tau B)
            (fundTyEqEnv dB
              (rec {y = mDeriv dB}
                (mDeriv-summand< d
                  (≤-sum4-4 (mDeriv daeq) (mDeriv dbeq) (mDeriv dA) (mDeriv dB))))
              (eqEnvCons ee tyA eq))
      tyB =
        let _ , famB =
              computableTySigma-elim
                {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
                (proj₁
                  (compTyEq-sides
                    {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
                    {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
                    tySig))
        in
        famB (subTm sigma a) (subTm tau c) caeq
      cbeq =
        compTmEq-subst
          (subTyComp sigma (singleSubst a) B
           ∙ singleLiftTy (subTm sigma a) sigma B)
          refl refl
          (proj₁
            (fundTmEqEqEnv dbeq
              (rec {y = mDeriv dbeq}
                (mDeriv-summand< d
                  (≤-sum2-4 (mDeriv daeq) (mDeriv dbeq) (mDeriv dA) (mDeriv dB))))
              ee))
    in
    computableTmEqSigma-intro
      {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau c} {d = subTm tau d0}
      caeq cbeq tyB ,
    tySig
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eSigmaEq {A = A} {B = B} {M = M} {d = d0} {d' = d1} {m = m} {m' = m'} dM dd dm dmEq) (acc rec) ee =
    let
      accM =
        rec {y = mDeriv dM}
          (mDeriv-summand< dAll (≤-sum1-4 (mDeriv dM) (mDeriv dd) (mDeriv dm) (mDeriv dmEq)))
      accd =
        rec {y = mDeriv dd}
          (mDeriv-summand< dAll (≤-sum2-4 (mDeriv dM) (mDeriv dd) (mDeriv dm) (mDeriv dmEq)))
      accmEq =
        rec {y = mDeriv dmEq}
          (mDeriv-summand< dAll (≤-sum4-4 (mDeriv dM) (mDeriv dd) (mDeriv dm) (mDeriv dmEq)))
      ddEq , tySig = fundTmEqEqEnv dd accd ee
      ddRight = proj₁ (fundTmEqEqEnv dd accd (eqEnvReflRight ee))
      ddSelf =
        compTmEq-trans
          {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
          {t = subTm sigma d0} {u = subTm tau d1} {v = subTm tau d0}
          ddEq
          (compTmEq-conv
            {A = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
            {B = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
            (compTyEq-sym
              {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
              {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
              tySig)
            (compTmEq-sym
              {A = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
              ddRight))
      tyA , famB =
        computableTyEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {C = subTy tau A} {D = subTy (liftSubst tau) B}
          tySig
      cSig =
        proj₁
          (compTyEq-sides
            {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
            {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
            tySig)
      ctyA , famLeft =
        computableTySigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          cSig
      b , c , e , f , evd , eve , eqB , eqCraw , tyCraw =
        computableTmEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {t = subTm sigma d0} {u = subTm tau d1}
          ddEq
      cb = proj₁ (compTmEq-sides {A = subTy sigma A} eqB)
      ccRaw =
        proj₁
          (compTmEq-sides
            {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            eqCraw)
      eqBB = compTmEq-refl {A = subTy sigma A} ctyA cb
      tyBB = famLeft b b eqBB
      ctyB =
        proj₁
          (compTyEq-sides
            {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            {B = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            tyBB)
      eqCC =
        compTmEq-refl
          {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
          ctyB ccRaw
      eqDPair =
        computableTmEqSigma-eval-intro
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {t = subTm sigma d0} {u = tmPair b c}
          {a = b} {b = c} {c = b} {d = c}
          evd evalPair eqBB eqCC tyBB
      tyDPairRaw =
        fundTyEqEnv dM accM
          (eqEnvCons
            (eqEnvReflLeft ee)
            (compTyEq-refl {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)} cSig)
            eqDPair)
      tyDPair =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst d0) M))
          refl
          tyDPairRaw
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst d0) M))
          (sym (subTyComp tau (singleSubst d0) M))
          (fundTyEqEnv dM accM (eqEnvCons ee tySig ddSelf))
      tyC =
        compTyEq-subst
          (sym (singleLiftTy b sigma B))
          (sym (singleLiftTy e tau B))
          (famB b e eqB)
      eqC =
        compTmEq-subst (sym (singleLiftTy b sigma B)) refl refl eqCraw
      branchEq =
        proj₁ (fundTmEqEqEnv dmEq accmEq (eqEnvCons (eqEnvCons ee tyA eqB) tyC eqC))
      eqSources =
        compTmEq-subst
          (sigmaBranchTargetTy b c sigma M)
          (sym (sigmaCompLiftTm b c sigma m))
          (sym (sigmaCompLiftTm e f tau m'))
          branchEq
    in
    compTmEq-conv
      {A = subTy (consSubst (tmPair b c) sigma) M}
      {B = subTy sigma (subTy (singleSubst d0) M)}
      (compTyEq-sym
        {A = subTy sigma (subTy (singleSubst d0) M)}
        {B = subTy (consSubst (tmPair b c) sigma) M}
        tyDPair)
      (compTmEqElimRight eve (compTmEqElimLeft evd eqSources)) ,
    tyResult
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM dSig db dc dm) (acc rec) ee =
    let
      bσ = subTm sigma b
      cσ = subTm sigma c
      bτ = subTm tau b
      cτ = subTm tau c
      accM =
        rec {y = mDeriv dM}
          (mDeriv-summand< d
            (≤-sum1-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      accSig =
        rec {y = mDeriv dSig}
          (mDeriv-summand< d
            (≤-sum2-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      accb =
        rec {y = mDeriv db}
          (mDeriv-summand< d
            (≤-sum3-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      accc =
        rec {y = mDeriv dc}
          (mDeriv-summand< d
            (≤-sum4-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      accm =
        rec {y = mDeriv dm}
          (mDeriv-summand< d
            (≤-sum5-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      tySig = fundTyEqEnv dSig accSig ee
      tyA , famB =
        computableTyEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {C = subTy tau A} {D = subTy (liftSubst tau) B}
          tySig
      cSig =
        proj₁
          (compTyEq-sides
            {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
            {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
            tySig)
      ctyA , famLeft =
        computableTySigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          cSig
      eqB , tyA' = fundTmEqEnv db accb ee
      tyC =
        compTyEq-subst
          (sym (singleLiftTy bσ sigma B))
          (sym (singleLiftTy bτ tau B))
          (famB bσ bτ eqB)
      tyCpair = famLeft bσ bτ eqB
      eqC =
        compTmEq-subst
          (subTyComp sigma (singleSubst b) B)
          refl refl
          (proj₁ (fundTmEqEnv dc accc ee))
      eqCpair =
        compTmEq-subst
          (subTyComp sigma (singleSubst b) B
           ∙ singleLiftTy bσ sigma B)
          refl refl
          (proj₁ (fundTmEqEnv dc accc ee))
      pairEq =
        computableTmEqSigma-intro
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {a = bσ} {b = cσ} {c = bτ} {d = cτ}
          eqB eqCpair tyCpair
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst (tmPair b c)) M))
          (sym (subTyComp tau (singleSubst (tmPair b c)) M))
          (fundTyEqEnv dM accM (eqEnvCons ee tySig pairEq))
      branchEq =
        proj₁ (fundTmEqEnv dm accm (eqEnvCons (eqEnvCons ee tyA eqB) tyC eqC))
      eqSources =
        compTmEq-subst
          (sigmaBranchTargetTy bσ cσ sigma M
           ∙ sym (subTyComp sigma (singleSubst (tmPair b c)) M))
          (sym (sigmaCompLiftTm bσ cσ sigma m))
          (sym (subTmComp tau (sigmaCompSub b c) m))
          branchEq
    in
    compTmEqElimLeft evalPair eqSources , tyResult
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(iEqEq {A = A} {a = a} {b = b} daeq) (acc rec) ee =
    let
      accA = rec {y = mDeriv daeq} (mDeriv-summand< d ≤-refl)
      eqA , tyA = fundTmEqEqEnv daeq accA ee
      eqARight = proj₁ (fundTmEqEqEnv daeq accA (eqEnvReflRight ee))
      eqAAcross =
        compTmEq-trans
          {A = subTy sigma A} {t = subTm sigma a} {u = subTm tau b} {v = subTm tau a}
          eqA
          (compTmEq-conv
            {A = subTy tau A} {B = subTy sigma A}
            (compTyEq-sym {A = subTy sigma A} {B = subTy tau A} tyA)
            (compTmEq-sym {A = subTy tau A} eqARight))
      ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} eqA)
    in
    computableTmEqEqForm-intro
      {A = subTy sigma A} {a = subTm sigma a} {b = subTm sigma a}
      {t = tmRefl} {u = tmRefl}
      evalRefl evalRefl (compTmEq-refl {A = subTy sigma A} ctyA ca) ,
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau A}
      {a = subTm sigma a} {b = subTm sigma a}
      {c = subTm tau a} {d = subTm tau a}
      tyA eqAAcross eqAAcross
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(eEqStar {A = A} {a = a} {b = b} {p = p} dp dA da db) (acc rec) ee =
    let
      dpEq , tyEqAB =
        fundTmEqEnv dp
          (rec {y = mDeriv dp}
            (mDeriv-summand< d (≤-sum1-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
      _ , _ , eqab =
        computableTmEqEqForm-elim
          {A = subTy sigma A}
          {a = subTm sigma a} {b = subTm sigma b}
          {t = subTm sigma p} {u = subTm tau p}
          dpEq
      eqb , tyA =
        fundTmEqEnv db
          (rec {y = mDeriv db}
            (mDeriv-summand< d (≤-sum4-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
    in
    compTmEq-trans
      {A = subTy sigma A} {t = subTm sigma a} {u = subTm sigma b} {v = subTm tau b}
      eqab eqb ,
    tyA
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(cEq {A = A} {a = a} {b = b} {p = p} dp dA da db) (acc rec) ee =
    let
      dpEq , tyEqAB =
        fundTmEqEnv dp
          (rec {y = mDeriv dp}
            (mDeriv-summand< d (≤-sum1-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
      evp , eqab =
        computableEq-elim
          {A = subTy sigma A}
          {a = subTm sigma a} {b = subTm sigma b}
          {t = subTm sigma p}
          (proj₁
            (compTmEq-sides
              {A = tyEq (subTy sigma A) (subTm sigma a) (subTm sigma b)}
              dpEq))
      eqa , tyA =
        fundTmEqEnv da
          (rec {y = mDeriv da}
            (mDeriv-summand< d (≤-sum3-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
      eqb , tyA' =
        fundTmEqEnv db
          (rec {y = mDeriv db}
            (mDeriv-summand< d (≤-sum4-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
    in
    computableTmEqEqForm-intro
      {A = subTy sigma A} {a = subTm sigma a} {b = subTm sigma b}
      {t = subTm sigma p} {u = tmRefl}
      evp evalRefl eqab ,
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau A}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau a} {d = subTm tau b}
      tyA eqa eqb
  fundTmEqEqEnv {sigma = sigma} {tau = tau} d@(iQtrEq {A = A} {a = a} {b = b} da db) (acc rec) ee =
    let
      eqa , tyA =
        fundTmEqEnv da (rec {y = mDeriv da} (mDeriv-summand< d ≤-sum-l)) ee
      ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} eqa)
      eqb , tyA' =
        fundTmEqEnv db (rec {y = mDeriv db} (mDeriv-summand< d ≤-sum-r)) ee
      cb = proj₂ (compTmEq-sides {A = subTy sigma A} eqb)
    in
    computableTmEqQtr-intro
      {A = subTy sigma A}
      {t = tmClass (subTm sigma a)} {u = tmClass (subTm tau b)}
      {p = subTm sigma a} {q = subTm tau b}
      evalClass evalClass
      (compTmEq-refl {A = subTy sigma A} ctyA ca)
      (compTmEq-refl {A = subTy sigma A} ctyA cb) ,
    computableTyEqQtr-intro {A = subTy sigma A} {C = subTy tau A} tyA
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(eQtrEq {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'} dL dpEq dBranch dl dl' dlEq coh coh') (acc rec) ee =
    let
      accL =
        rec {y = mDeriv dL}
          (mDeriv-summand< d
            (≤-sum1-8 (mDeriv dL) (mDeriv dpEq) (mDeriv dBranch) (mDeriv dl)
              (mDeriv dl') (mDeriv dlEq) (mDeriv coh) (mDeriv coh')))
      accp =
        rec {y = mDeriv dpEq}
          (mDeriv-summand< d
            (≤-sum2-8 (mDeriv dL) (mDeriv dpEq) (mDeriv dBranch) (mDeriv dl)
              (mDeriv dl') (mDeriv dlEq) (mDeriv coh) (mDeriv coh')))
      accDlEq =
        rec {y = mDeriv dlEq}
          (mDeriv-summand< d
            (≤-sum6-8 (mDeriv dL) (mDeriv dpEq) (mDeriv dBranch) (mDeriv dl)
              (mDeriv dl') (mDeriv dlEq) (mDeriv coh) (mDeriv coh')))
      accCoh' =
        rec {y = mDeriv coh'}
          (mDeriv-summand< d
            (≤-sum8-8 (mDeriv dL) (mDeriv dpEq) (mDeriv dBranch) (mDeriv dl)
              (mDeriv dl') (mDeriv dlEq) (mDeriv coh) (mDeriv coh')))
      dpMain , tyQtrEq = fundTmEqEqEnv dpEq accp ee
      dpRight = proj₁ (fundTmEqEqEnv dpEq accp (eqEnvReflRight ee))
      dpSelf =
        compTmEq-trans
          {A = tyQtr (subTy sigma A)}
          {t = subTm sigma p} {u = subTm tau p'} {v = subTm tau p}
          dpMain
          (compTmEq-conv
            {A = tyQtr (subTy tau A)} {B = tyQtr (subTy sigma A)}
            (compTyEq-sym
              {A = tyQtr (subTy sigma A)} {B = tyQtr (subTy tau A)}
              tyQtrEq)
            (compTmEq-sym {A = tyQtr (subTy tau A)} dpRight))
      cQtr =
        proj₁
          (compTyEq-sides
            {A = tyQtr (subTy sigma A)} {B = tyQtr (subTy tau A)}
            tyQtrEq)
      tyQ = computableTyEqQtr-elim {A = subTy sigma A} {C = subTy tau A} tyQtrEq
      cQ = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyQ)
      a , b , evp , evp' , caa , cbb =
        computableTmEqQtr-elim
          {A = subTy sigma A} {t = subTm sigma p} {u = subTm tau p'}
          dpMain
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} caa)
      eqAA = compTmEq-refl {A = subTy sigma A} cQ ca
      eqPClass =
        computableTmEqQtr-intro
          {A = subTy sigma A}
          {t = subTm sigma p} {u = tmClass a}
          {p = a} {q = a}
          evp evalClass eqAA eqAA
      tyPClassRaw =
        fundTyEqEnv dL accL
          (eqEnvCons
            (eqEnvReflLeft ee)
            (compTyEq-refl {A = tyQtr (subTy sigma A)} cQtr)
            eqPClass)
      tyPClass =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst p) L))
          refl
          tyPClassRaw
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst p) L))
          (sym (subTyComp tau (singleSubst p) L))
          (fundTyEqEnv dL accL (eqEnvCons ee tyQtrEq dpSelf))
      eeLeft =
        eqEnvReflLeft ee
      branchLeft =
        proj₁
          (fundTmEqEqEnv dlEq accDlEq
            (eqEnvCons eeLeft (compTyEq-refl {A = subTy sigma A} cQ) caa))
      branchLeftSource =
        compTmEq-subst
          (qtrBranchTargetTy a sigma L)
          (sym (qtrCompLiftTm a sigma l))
          (sym (qtrCompLiftTm a sigma l'))
          branchLeft
      tyHead =
        compTyEq-subst
          (sym (lookupHereTy sigma a A))
          (sym (lookupHereTy tau a A))
          tyQ
      headEq =
        compTmEq-subst
          (sym (lookupHereTy sigma a A))
          refl refl
          cbb
      branchCoh =
        proj₁ (fundTmEqEqEnv coh' accCoh'
          (eqEnvCons
            (eqEnvCons ee tyQ caa)
            tyHead
            headEq))
      branchCohSource =
        compTmEq-subst
          (qtrCohTargetTy a b sigma L)
          (qtrCohLeftTm a b sigma l' ∙ sym (qtrCompLiftTm a sigma l'))
          (qtrCohRightTm a b tau l' ∙ sym (qtrCompLiftTm b tau l'))
          branchCoh
      eqSources =
        compTmEq-trans
          {A = subTy (consSubst (tmClass a) sigma) L}
          {t = subTm (qtrCompSub a) (subTm (liftSubst sigma) l)}
          {u = subTm (qtrCompSub a) (subTm (liftSubst sigma) l')}
          {v = subTm (qtrCompSub b) (subTm (liftSubst tau) l')}
          branchLeftSource branchCohSource
    in
    compTmEq-conv
      {A = subTy (consSubst (tmClass a) sigma) L}
      {B = subTy sigma (subTy (singleSubst p) L)}
      (compTyEq-sym
        {A = subTy sigma (subTy (singleSubst p) L)}
        {B = subTy (consSubst (tmClass a) sigma) L}
        tyPClass)
      (compTmEqQtrElimRight evp' (compTmEqQtrElimLeft evp eqSources)) ,
    tyResult
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(cQtr {A = A} {L = L} {a = a} {l = l} dL da dBranch dl coh) (acc rec) ee =
    let
      aσ = subTm sigma a
      aτ = subTm tau a
      accL =
        rec {y = mDeriv dL}
          (mDeriv-summand< d
            (≤-sum1-5 (mDeriv dL) (mDeriv da) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      acca =
        rec {y = mDeriv da}
          (mDeriv-summand< d
            (≤-sum2-5 (mDeriv dL) (mDeriv da) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      accl =
        rec {y = mDeriv dl}
          (mDeriv-summand< d
            (≤-sum4-5 (mDeriv dL) (mDeriv da) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      eqA , tyA = fundTmEqEnv da acca ee
      cA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      caσ = proj₁ (compTmEq-sides {A = subTy sigma A} eqA)
      caτ = proj₂ (compTmEq-sides {A = subTy sigma A} eqA)
      tyQtrEq = computableTyEqQtr-intro {A = subTy sigma A} {C = subTy tau A} tyA
      classEq =
        computableTmEqQtr-intro
          {A = subTy sigma A}
          {t = tmClass aσ} {u = tmClass aτ}
          {p = aσ} {q = aτ}
          evalClass evalClass
          (compTmEq-refl {A = subTy sigma A} cA caσ)
          (compTmEq-refl {A = subTy sigma A} cA caτ)
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst (tmClass a)) L))
          (sym (subTyComp tau (singleSubst (tmClass a)) L))
          (fundTyEqEnv dL accL (eqEnvCons ee tyQtrEq classEq))
      branchEq =
        proj₁ (fundTmEqEnv dl accl (eqEnvCons ee tyA eqA))
      eqSources =
        compTmEq-subst
          (qtrBranchTargetTy aσ sigma L
           ∙ sym (subTyComp sigma (singleSubst (tmClass a)) L))
          (sym (qtrCompLiftTm aσ sigma l))
          (sym (subTmComp tau (qtrCompSub a) l))
          branchEq
    in
    compTmEqQtrElimLeft evalClass eqSources , tyResult

  fundFitsSameEq : {gamma delta : Ctx} {theta sigma tau : Subst}
    -> (fits : FitsSubst gamma delta theta) -> Acc _<_ (mFits fits) -> EqEnv gamma sigma tau
    -> EqEnv delta (compSub sigma theta) (compSub tau theta)
  fundFitsSameEq (fitsNil wf) _ ee = eqEnvNil
  fundFitsSameEq {sigma = sigma} {tau = tau}
    fs@(fitsCons {sigma = theta} {A = A} fits dt) (acc rec) ee =
    let
      eeΔ =
        fundFitsSameEq fits
          (rec {y = mFits fits} (mFits-fitsCons-fits< fits dt))
          ee
      tm , ty =
        fundTmEqEnv dt
          (rec {y = mDeriv dt} (mFits-fitsCons-deriv< fits dt))
          ee
    in
    eqEnvCons eeΔ
      (compTyEq-subst
        (subTyComp sigma theta A)
        (subTyComp tau theta A)
        ty)
      (compTmEq-subst
        (subTyComp sigma theta A)
        refl refl
        tm)

  fundFitsEqLeftEnv : {gamma delta : Ctx} {theta eta sigma tau : Subst}
    -> (fitsEq : FitsEqSubst gamma delta theta eta) -> Acc _<_ (mFitsEq fitsEq)
    -> EqEnv gamma sigma tau
    -> EqEnv delta (compSub sigma theta) (compSub tau theta)
  fundFitsEqLeftEnv (fitsEqNil wf) _ ee = eqEnvNil
  fundFitsEqLeftEnv {sigma = sigma} {tau = tau}
    fs@(fitsEqCons {sigma = theta} {tau = eta} {A = A} {t = t} {u = u} fitsEq dtu) (acc rec) ee =
    let
      eeΔ =
        fundFitsEqLeftEnv fitsEq
          (rec {y = mFitsEq fitsEq} (mFitsEq-fitsEqCons-fitsEq< fitsEq dtu))
          ee
      accDtu = rec {y = mDeriv dtu} (mFitsEq-fitsEqCons-deriv< fitsEq dtu)
      tm , ty = fundTmEqEqEnv dtu accDtu ee
      tmRight = proj₁ (fundTmEqEqEnv dtu accDtu (eqEnvReflRight ee))
      tmSelf =
        compTmEq-trans
          {A = subTy sigma (subTy theta A)}
          {t = subTm sigma t} {u = subTm tau u} {v = subTm tau t}
          tm
          (compTmEq-conv
            {A = subTy tau (subTy theta A)}
            {B = subTy sigma (subTy theta A)}
            (compTyEq-sym
              {A = subTy sigma (subTy theta A)}
              {B = subTy tau (subTy theta A)}
              ty)
            (compTmEq-sym {A = subTy tau (subTy theta A)} tmRight))
    in
    eqEnvCons eeΔ
      (compTyEq-subst
        (subTyComp sigma theta A)
        (subTyComp tau theta A)
        ty)
      (compTmEq-subst
        (subTyComp sigma theta A)
        refl refl
        tmSelf)

  fundFitsEqEnv : {gamma delta : Ctx} {theta eta sigma tau : Subst}
    -> (fitsEq : FitsEqSubst gamma delta theta eta) -> (wfΔ : CtxWF delta)
    -> Acc _<_ (mFitsEq fitsEq + mCtxWF wfΔ) -> EqEnv gamma sigma tau
    -> EqEnv delta (compSub sigma theta) (compSub tau eta)
  fundFitsEqEnv (fitsEqNil wf) wfΔ _ ee = eqEnvNil
  fundFitsEqEnv {sigma = sigma} {tau = tau}
    fs@(fitsEqCons {sigma = theta} {tau = eta} {A = A} fitsEq dtu)
    (wfCons wfΔ dA) (acc rec) ee =
    let
      eeΔ =
        fundFitsEqEnv fitsEq wfΔ
          (rec {y = mFitsEq fitsEq + mCtxWF wfΔ}
            (fitsEqCtx-tail< fitsEq dtu wfΔ dA))
          ee
      tm , ty =
        fundTmEqEqEnv dtu
          (rec {y = mDeriv dtu}
            (≤-trans (mFitsEq-fitsEqCons-deriv< fitsEq dtu) ≤-sum-l))
          ee
    in
    eqEnvCons eeΔ
      (fundTyEqEnv dA
        (rec {y = mDeriv dA} (fitsEqCtx-headDeriv< fitsEq dtu wfΔ dA))
        eeΔ)
      (compTmEq-subst
        (subTyComp sigma theta A)
        refl refl
        tm)

fundTyEq : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
  -> Derivable (typeEq gamma A B) -> EqEnv gamma sigma tau
  -> ComputableTyEq (subTy sigma A) (subTy tau B)
fundTyEq d ee = fundTyEqEqEnv d (<-wellFounded (mDeriv d)) ee

fundTmTyEnv : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
  -> Derivable (hasTy gamma t A) -> EqEnv gamma sigma tau
  -> ComputableTyEq (subTy sigma A) (subTy tau A)
fundTmTyEnv d ee = proj₂ (fundTmEqEnv d (<-wellFounded (mDeriv d)) ee)

fundTmEq : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
  -> Derivable (termEq gamma t u A) -> EqEnv gamma sigma tau
  -> ComputableTmEq (subTy sigma A) (subTm sigma t) (subTm tau u)
fundTmEq d ee = proj₁ (fundTmEqEqEnv d (<-wellFounded (mDeriv d)) ee)

fundFitsEq : {gamma delta : Ctx} {theta eta sigma tau : Subst}
  -> FitsEqSubst gamma delta theta eta -> CtxWF delta -> EqEnv gamma sigma tau
  -> EqEnv delta (compSub sigma theta) (compSub tau eta)
fundFitsEq fitsEq wfΔ ee =
  fundFitsEqEnv fitsEq wfΔ (<-wellFounded (mFitsEq fitsEq + mCtxWF wfΔ)) ee

fundTyClosed : {A : RawType}
  -> Derivable (isType [] A) -> ComputableTy A
fundTyClosed {A = A} d =
  compTy-subst {A = subTy idSubst A} {B = A} (subTyId A)
    (proj₁
      (compTyEq-sides
        {A = subTy idSubst A} {B = subTy idSubst A}
        (fundTyEqEnv d (<-wellFounded (mDeriv d)) eqEnvNil)))

fundTmClosed : {t : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t A) -> Computable A t
fundTmClosed {t = t} {A = A} d =
  compTm-subst
    {A = subTy idSubst A} {B = A}
    {t = subTm idSubst t} {u = t}
    (subTyId A) (subTmId t)
    (proj₁
      (compTmEq-sides
        {A = subTy idSubst A}
        {t = subTm idSubst t} {u = subTm idSubst t}
        (proj₁ (fundTmEqEnv d (<-wellFounded (mDeriv d)) eqEnvNil))))

fundTyEqClosed : {A B : RawType}
  -> Derivable (typeEq [] A B) -> ComputableTyEq A B
fundTyEqClosed {A = A} {B = B} d =
  compTyEq-subst
    {A = subTy idSubst A} {A' = A}
    {B = subTy idSubst B} {B' = B}
    (subTyId A) (subTyId B)
    (fundTyEqEqEnv d (<-wellFounded (mDeriv d)) eqEnvNil)

fundTmEqClosed : {t u : RawTerm} {A : RawType}
  -> Derivable (termEq [] t u A) -> ComputableTmEq A t u
fundTmEqClosed {t = t} {u = u} {A = A} d =
  compTmEq-subst
    {A = subTy idSubst A} {B = A}
    {t = subTm idSubst t} {t' = t}
    {u = subTm idSubst u} {u' = u}
    (subTyId A) (subTmId t) (subTmId u)
    (proj₁ (fundTmEqEqEnv d (<-wellFounded (mDeriv d)) eqEnvNil))
