{-# OPTIONS --safe #-}

module Tait.Fundamental.Infrastructure where

open import Tait.Prelude
open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (proj₁ ; proj₂)

open import Tait.Syntax
open import Tait.Context
open import Tait.Substitution
open import Tait.Evaluation
open import Tait.Derivability
open import Tait.Computable
open import Tait.CompLemmas
open import Tait.Env

compTy-subst : {A B : RawType} -> A ≡ B -> ComputableTy A -> ComputableTy B
compTy-subst refl c = c

compTm-subst : {A B : RawType} {t u : RawTerm}
  -> A ≡ B -> t ≡ u -> Computable A t -> Computable B u
compTm-subst refl refl c = c

compTyEq-subst : {A A' B B' : RawType}
  -> A ≡ A' -> B ≡ B' -> ComputableTyEq A B -> ComputableTyEq A' B'
compTyEq-subst refl refl c = c

compTmEq-subst : {A B : RawType} {t t' u u' : RawTerm}
  -> A ≡ B -> t ≡ t' -> u ≡ u'
  -> ComputableTmEq A t u -> ComputableTmEq B t' u'
compTmEq-subst refl refl refl c = c

envDrop : {gamma delta : Ctx} {sigma : Subst}
  -> Env (delta ++ gamma) sigma -> Env gamma (dropSub (length delta) sigma)
envDrop {delta = []} rho = rho
envDrop {delta = A ∷ delta} (envCons rho ca) = envDrop {delta = delta} rho

data EqEnv : Ctx -> Subst -> Subst -> Type where
  eqEnvNil : {sigma tau : Subst} -> EqEnv [] sigma tau
  eqEnvCons : {gamma : Ctx} {A : RawType} {sigma tau : Subst} {a b : RawTerm}
    -> EqEnv gamma sigma tau
    -> ComputableTyEq (subTy sigma A) (subTy tau A)
    -> ComputableTmEq (subTy sigma A) a b
    -> EqEnv (A ∷ gamma) (consSubst a sigma) (consSubst b tau)

eqEnvLeft : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> Env gamma sigma
eqEnvLeft eqEnvNil = envNil
eqEnvLeft (eqEnvCons {A = A} {sigma = sigma} {tau = tau} ee ctyEq eq) =
  envCons (eqEnvLeft ee)
    (proj₁ (compTmEq-sides {A = subTy sigma A} eq))

eqEnvRight : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> Env gamma tau
eqEnvRight eqEnvNil = envNil
eqEnvRight (eqEnvCons {A = A} {sigma = sigma} {tau = tau} ee ctyEq eq) =
  envCons (eqEnvRight ee)
    (compTm-conv ctyEq (proj₂ (compTmEq-sides eq)))

eqEnvReflLeft : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> EqEnv gamma sigma sigma
eqEnvReflLeft eqEnvNil = eqEnvNil
eqEnvReflLeft (eqEnvCons {A = A} {sigma = sigma} {tau = tau} ee ctyEq eq) =
  let
    ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} ctyEq)
    ca = proj₁ (compTmEq-sides {A = subTy sigma A} eq)
  in
  eqEnvCons (eqEnvReflLeft ee)
    (compTyEq-refl {A = subTy sigma A} ctyA)
    (compTmEq-refl {A = subTy sigma A} ctyA ca)

eqEnvReflRight : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> EqEnv gamma tau tau
eqEnvReflRight eqEnvNil = eqEnvNil
eqEnvReflRight (eqEnvCons {A = A} {sigma = sigma} {tau = tau} ee ctyEq eq) =
  let
    ctyA = proj₂ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} ctyEq)
    ca = compTm-conv ctyEq (proj₂ (compTmEq-sides {A = subTy sigma A} eq))
  in
  eqEnvCons (eqEnvReflRight ee)
    (compTyEq-refl {A = subTy tau A} ctyA)
    (compTmEq-refl {A = subTy tau A} ctyA ca)

eqEnvDrop : {gamma delta : Ctx} {sigma tau : Subst}
  -> EqEnv (delta ++ gamma) sigma tau
  -> EqEnv gamma (dropSub (length delta) sigma) (dropSub (length delta) tau)
eqEnvDrop {delta = []} ee = ee
eqEnvDrop {delta = A ∷ delta} (eqEnvCons ee ctyEq eq) = eqEnvDrop {delta = delta} ee

eqEnvLookup : {gamma delta : Ctx} {A : RawType} {sigma tau : Subst}
  -> EqEnv (delta ++ (A ∷ gamma)) sigma tau
  -> ComputableTmEq (subTy sigma (wkTyBy (suc (length delta)) A))
       (applySubst sigma (length delta)) (applySubst tau (length delta))
eqEnvLookup {delta = []} {A = A} (eqEnvCons {sigma = sigma} {a = a} ee ctyEq eq) =
  compTmEq-subst (sym (lookupHereTy sigma a A)) refl refl eq
eqEnvLookup {delta = D ∷ delta} {A = A}
  (eqEnvCons {sigma = sigma} {a = a} ee ctyEq eq) =
  compTmEq-subst
    (sym (lookupWkCancel sigma a (suc (length delta)) A))
    refl refl
    (eqEnvLookup {delta = delta} ee)

eqEnvLookupTy : {gamma delta : Ctx} {A : RawType} {sigma tau : Subst}
  -> EqEnv (delta ++ (A ∷ gamma)) sigma tau
  -> ComputableTyEq (subTy sigma (wkTyBy (suc (length delta)) A))
       (subTy tau (wkTyBy (suc (length delta)) A))
eqEnvLookupTy {delta = []} {A = A}
  (eqEnvCons {sigma = sigma} {tau = tau} {a = a} {b = b} ee ctyEq eq) =
  compTyEq-subst (sym (lookupHereTy sigma a A)) (sym (lookupHereTy tau b A)) ctyEq
eqEnvLookupTy {delta = D ∷ delta} {A = A}
  (eqEnvCons {sigma = sigma} {tau = tau} {a = a} {b = b} ee ctyEq eq) =
  compTyEq-subst
    (sym (lookupWkCancel sigma a (suc (length delta)) A))
    (sym (lookupWkCancel tau b (suc (length delta)) A))
    (eqEnvLookupTy {delta = delta} ee)

singleSubstWkCancel : (a t : RawTerm)
  -> subTm (singleSubst a) (renTm sucRen t) ≡ t
singleSubstWkCancel a t =
  subTmRen (singleSubst a) sucRen t ∙ subTmId t

singleLift-apply : (a : RawTerm) (sigma : Subst) (n : ℕ)
  -> applySubst (consSubst a sigma) n
       ≡ applySubst (compSub (singleSubst a) (liftSubst sigma)) n
singleLift-apply a sigma zero = refl
singleLift-apply a sigma (suc n) =
  sym (singleSubstWkCancel a (applySubst sigma n))
  ∙ cong (subTm (singleSubst a)) (sym (liftSubst-apply-suc sigma n))
  ∙ sym (applySubst-compSub (singleSubst a) (liftSubst sigma) (suc n))

singleLiftTy : (a : RawTerm) (sigma : Subst) (B : RawType)
  -> subTy (consSubst a sigma) B
       ≡ subTy (singleSubst a) (subTy (liftSubst sigma) B)
singleLiftTy a sigma B =
  subTyEq (singleLift-apply a sigma) B
  ∙ sym (subTyComp (singleSubst a) (liftSubst sigma) B)

singleLiftTm : (a : RawTerm) (sigma : Subst) (t : RawTerm)
  -> subTm (consSubst a sigma) t
       ≡ subTm (singleSubst a) (subTm (liftSubst sigma) t)
singleLiftTm a sigma t =
  subTmEq (singleLift-apply a sigma) t
  ∙ sym (subTmComp (singleSubst a) (liftSubst sigma) t)

sigmaBranchTarget-apply : (b c : RawTerm) (sigma : Subst)
  -> (n : ℕ)
  -> applySubst (compSub (consSubst c (consSubst b sigma)) sigmaMotSub) n
       ≡ applySubst (consSubst (tmPair b c) sigma) n
sigmaBranchTarget-apply b c sigma zero = refl
sigmaBranchTarget-apply b c sigma (suc n) = refl

sigmaBranchTargetTy : (b c : RawTerm) (sigma : Subst) (M : RawType)
  -> subTy (consSubst c (consSubst b sigma)) (sigmaBranchTy M)
       ≡ subTy (consSubst (tmPair b c) sigma) M
sigmaBranchTargetTy b c sigma M =
  subTyComp (consSubst c (consSubst b sigma)) sigmaMotSub M
  ∙ subTyEq (sigmaBranchTarget-apply b c sigma) M

twoLiftCancelTm : (b c t : RawTerm)
  -> subTm (sigmaCompSub b c) (renTm sucRen (renTm sucRen t)) ≡ t
twoLiftCancelTm b c t =
  subTmRen (sigmaCompSub b c) sucRen (renTm sucRen t)
  ∙ subTmRen (consSubst b idSubst) sucRen t
  ∙ subTmId t

sigmaCompLift-apply : (b c : RawTerm) (sigma : Subst) (n : ℕ)
  -> applySubst (compSub (sigmaCompSub b c) (liftSubst (liftSubst sigma))) n
       ≡ applySubst (consSubst c (consSubst b sigma)) n
sigmaCompLift-apply b c sigma zero = refl
sigmaCompLift-apply b c sigma (suc zero) = refl
sigmaCompLift-apply b c sigma (suc (suc n)) =
  applySubst-compSub (sigmaCompSub b c) (liftSubst (liftSubst sigma)) (suc (suc n))
  ∙ cong (subTm (sigmaCompSub b c))
      (liftSubst-apply-suc (liftSubst sigma) (suc n)
       ∙ cong (renTm sucRen) (liftSubst-apply-suc sigma n))
  ∙ twoLiftCancelTm b c (applySubst sigma n)

sigmaCompLiftTm : (b c : RawTerm) (sigma : Subst) (m : RawTerm)
  -> subTm (sigmaCompSub b c) (subTm (liftSubst (liftSubst sigma)) m)
       ≡ subTm (consSubst c (consSubst b sigma)) m
sigmaCompLiftTm b c sigma m =
  subTmComp (sigmaCompSub b c) (liftSubst (liftSubst sigma)) m
  ∙ subTmEq (sigmaCompLift-apply b c sigma) m

qtrBranchTarget-apply : (a : RawTerm) (sigma : Subst) (n : ℕ)
  -> applySubst (compSub (consSubst a sigma) qtrBranchSub) n
       ≡ applySubst (consSubst (tmClass a) sigma) n
qtrBranchTarget-apply a sigma zero = refl
qtrBranchTarget-apply a sigma (suc n) = refl

qtrBranchTargetTy : (a : RawTerm) (sigma : Subst) (L : RawType)
  -> subTy (consSubst a sigma) (qtrBranchTy L)
       ≡ subTy (consSubst (tmClass a) sigma) L
qtrBranchTargetTy a sigma L =
  subTyComp (consSubst a sigma) qtrBranchSub L
  ∙ subTyEq (qtrBranchTarget-apply a sigma) L

qtrCompLiftTm : (a : RawTerm) (sigma : Subst) (l : RawTerm)
  -> subTm (qtrCompSub a) (subTm (liftSubst sigma) l)
       ≡ subTm (consSubst a sigma) l
qtrCompLiftTm a sigma l = sym (singleLiftTm a sigma l)

qtrCohTarget-apply : (a b : RawTerm) (sigma : Subst) (n : ℕ)
  -> applySubst (compSub (consSubst b (consSubst a sigma)) qtrCohSub) n
       ≡ applySubst (consSubst (tmClass a) sigma) n
qtrCohTarget-apply a b sigma zero = refl
qtrCohTarget-apply a b sigma (suc n) = refl

qtrCohTargetTy : (a b : RawTerm) (sigma : Subst) (L : RawType)
  -> subTy (consSubst b (consSubst a sigma)) (qtrCohTy L)
       ≡ subTy (consSubst (tmClass a) sigma) L
qtrCohTargetTy a b sigma L =
  subTyComp (consSubst b (consSubst a sigma)) qtrCohSub L
  ∙ subTyEq (qtrCohTarget-apply a b sigma) L

qtrCohLeftTm : (a b : RawTerm) (sigma : Subst) (l : RawTerm)
  -> subTm (consSubst b (consSubst a sigma)) (wkTmBy 1 l)
       ≡ subTm (consSubst a sigma) l
qtrCohLeftTm a b sigma l =
  subTmRen (consSubst b (consSubst a sigma)) (addRen 1) l ∙ refl

qtrCohRightTm : (a b : RawTerm) (sigma : Subst) (l : RawTerm)
  -> subTm (consSubst b (consSubst a sigma)) (renTm qtrSecondBranchRen l)
       ≡ subTm (consSubst b sigma) l
qtrCohRightTm a b sigma l =
  subTmRen (consSubst b (consSubst a sigma)) qtrSecondBranchRen l ∙ refl
