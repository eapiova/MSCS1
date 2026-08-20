{-# OPTIONS --safe #-}

module Recursive.Evaluation where

open import Recursive.Prelude
open import Data.Empty as Empty using () renaming (⊥-elim to rec)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.Base using (_<_) renaming (s≤s to suc-≤-suc)
open import Data.Nat.Properties using (≤-trans)
  renaming (m≤m+n to ≤SumLeft ; m≤n+m to ≤SumRight)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wellfounded)
open import Induction.WellFounded using (Acc ; acc)

open import Recursive.Syntax
open import Recursive.Substitution

infix 40 _=>e_

sigmaCompSub : RawTerm -> RawTerm -> Subst
sigmaCompSub a b = consSubst b (consSubst a idSubst)

qtrCompSub : RawTerm -> Subst
qtrCompSub a = consSubst a idSubst

data _=>e_ : RawTerm -> RawTerm -> Type where
  evalStar : tmStar =>e tmStar
  evalPair : {a b : RawTerm} -> tmPair a b =>e tmPair a b
  evalRefl : tmRefl =>e tmRefl
  evalEqTm : {A : RawType} {a : RawTerm} -> tmEq A a =>e tmEq A a
  evalClass : {a : RawTerm} -> tmClass a =>e tmClass a
  evalElSigma : {d m b c g : RawTerm}
    -> d =>e tmPair b c
    -> subTm (sigmaCompSub b c) m =>e g
    -> tmElSigma d m =>e g
  evalElQtr : {l p a g : RawTerm}
    -> p =>e tmClass a
    -> subTm (qtrCompSub a) l =>e g
    -> tmElQtr l p =>e g
  evalZero : tmZero =>e tmZero
  evalSucV : {k : RawTerm} -> tmSuc k =>e tmSuc k
  evalElNatZ : {a l p g : RawTerm}
    -> p =>e tmZero
    -> a =>e g
    -> tmElNat a l p =>e g
  evalElNatS : {a l p k recVal g : RawTerm}
    -> p =>e tmSuc k
    -> tmElNat a l k =>e recVal
    -> subTm (consSubst recVal (consSubst k idSubst)) l =>e g
    -> tmElNat a l p =>e g

tmPairFst : RawTerm -> RawTerm
tmPairFst (tmPair a _) = a
tmPairFst _ = tmStar

tmPairSnd : RawTerm -> RawTerm
tmPairSnd (tmPair _ b) = b
tmPairSnd _ = tmStar

tmPairInj₁ : {a b c d : RawTerm} -> tmPair a b ≡ tmPair c d -> a ≡ c
tmPairInj₁ p = cong tmPairFst p

tmPairInj₂ : {a b c d : RawTerm} -> tmPair a b ≡ tmPair c d -> b ≡ d
tmPairInj₂ p = cong tmPairSnd p

tmClassRepr : RawTerm -> RawTerm
tmClassRepr (tmClass a) = a
tmClassRepr _ = tmStar

tmClassInj : {a b : RawTerm} -> tmClass a ≡ tmClass b -> a ≡ b
tmClassInj p = cong tmClassRepr p

tmSucPred : RawTerm -> RawTerm
tmSucPred (tmSuc k) = k
tmSucPred _ = tmStar

tmSucInj : {k k' : RawTerm} -> tmSuc k ≡ tmSuc k' -> k ≡ k'
tmSucInj p = cong tmSucPred p

-- Size measure for evaluation proofs
evalSize : {t g : RawTerm} -> t =>e g -> ℕ
evalSize evalStar = 0
evalSize evalPair = 0
evalSize evalRefl = 0
evalSize evalEqTm = 0
evalSize evalClass = 0
evalSize (evalElSigma evd evm) = suc (evalSize evd + evalSize evm)
evalSize (evalElQtr evp evl) = suc (evalSize evp + evalSize evl)
evalSize evalZero = 0
evalSize evalSucV = 0
evalSize (evalElNatZ evp eva) = suc (evalSize evp + evalSize eva)
evalSize (evalElNatS evp evRec evStep) =
  suc (evalSize evp + evalSize evRec + evalSize evStep)

private
  evalDetTmAcc : {t g g' : RawTerm}
    -> (ev₁ : t =>e g) -> Acc _<_ (evalSize ev₁) -> (ev₂ : t =>e g') -> g ≡ g'
  evalDetTmAcc evalStar _ evalStar = refl
  evalDetTmAcc evalPair _ evalPair = refl
  evalDetTmAcc evalRefl _ evalRefl = refl
  evalDetTmAcc evalEqTm _ evalEqTm = refl
  evalDetTmAcc evalClass _ evalClass = refl
  evalDetTmAcc
    {g = g} {g' = g'}
    (evalElSigma {m = m} {b = b} {c = c} evd₁ evm₁) (acc step)
    (evalElSigma {b = b'} {c = c'} evd₂ evm₂) =
    let
      acD : Acc _<_ (evalSize evd₁)
      acD = step (suc-≤-suc (≤SumLeft (evalSize evd₁) (evalSize evm₁)))
      pairEq = evalDetTmAcc evd₁ acD evd₂
      bEq = tmPairInj₁ pairEq
      cEq = tmPairInj₂ pairEq
      srcEq = cong₂ (λ x y -> subTm (sigmaCompSub x y) m) bEq cEq
      acM : Acc _<_ (evalSize evm₁)
      acM = step (suc-≤-suc (≤SumRight (evalSize evm₁) (evalSize evd₁)))
    in
    evalDetTmAcc evm₁ acM (subst (λ x -> x =>e g') (sym srcEq) evm₂)
  evalDetTmAcc
    {g = g} {g' = g'}
    (evalElQtr {l = l} {a = a} evp₁ evl₁) (acc step)
    (evalElQtr {a = a'} evp₂ evl₂) =
    let
      acP : Acc _<_ (evalSize evp₁)
      acP = step (suc-≤-suc (≤SumLeft (evalSize evp₁) (evalSize evl₁)))
      classEq = evalDetTmAcc evp₁ acP evp₂
      aEq = tmClassInj classEq
      srcEq = cong (λ x -> subTm (qtrCompSub x) l) aEq
      acL : Acc _<_ (evalSize evl₁)
      acL = step (suc-≤-suc (≤SumRight (evalSize evl₁) (evalSize evp₁)))
    in
    evalDetTmAcc evl₁ acL (subst (λ x -> x =>e g') (sym srcEq) evl₂)
  evalDetTmAcc evalZero _ evalZero = refl
  evalDetTmAcc evalSucV _ evalSucV = refl
  evalDetTmAcc
    {g = g} {g' = g'}
    (evalElNatZ evp₁ eva₁) (acc step)
    (evalElNatZ evp₂ eva₂) =
    let
      acA : Acc _<_ (evalSize eva₁)
      acA = step (suc-≤-suc (≤SumRight (evalSize eva₁) (evalSize evp₁)))
    in
    evalDetTmAcc eva₁ acA eva₂
  evalDetTmAcc
    (evalElNatZ evp₁ eva₁) (acc step)
    (evalElNatS {k = k'} evp₂ evRec₂ evStep₂)
    with evalDetTmAcc evp₁ (step (suc-≤-suc (≤SumLeft (evalSize evp₁) (evalSize eva₁)))) evp₂
  ... | ()
  evalDetTmAcc
    (evalElNatS {k = k} evp₁ evRec₁ evStep₁) (acc step)
    (evalElNatZ evp₂ eva₂)
    with evalDetTmAcc evp₁
      (step
        (suc-≤-suc
          (≤-trans
            (≤SumLeft (evalSize evp₁) (evalSize evRec₁))
            (≤SumLeft (evalSize evp₁ + evalSize evRec₁) (evalSize evStep₁)))))
      evp₂
  ... | ()
  evalDetTmAcc
    {g = g} {g' = g'}
    (evalElNatS {a = a} {l = l} {k = k} {recVal = recVal} evp₁ evRec₁ evStep₁) (acc step)
    (evalElNatS {k = k'} {recVal = recVal'} evp₂ evRec₂ evStep₂) =
    let
      acP : Acc _<_ (evalSize evp₁)
      acP =
        step
          (suc-≤-suc
            (≤-trans
              (≤SumLeft (evalSize evp₁) (evalSize evRec₁))
              (≤SumLeft (evalSize evp₁ + evalSize evRec₁) (evalSize evStep₁))))
      sucEq = evalDetTmAcc evp₁ acP evp₂
      kEq = tmSucInj sucEq
      srcRecEq = cong (λ x -> tmElNat a l x) kEq
      acRec : Acc _<_ (evalSize evRec₁)
      acRec =
        step
          (suc-≤-suc
            (≤-trans
              (≤SumRight (evalSize evRec₁) (evalSize evp₁))
              (≤SumLeft (evalSize evp₁ + evalSize evRec₁) (evalSize evStep₁))))
      recEq =
        evalDetTmAcc evRec₁ acRec
          (subst (λ x -> x =>e recVal') (sym srcRecEq) evRec₂)
      srcStepEq =
        cong₂ (λ r x -> subTm (consSubst r (consSubst x idSubst)) l) recEq kEq
      acStep : Acc _<_ (evalSize evStep₁)
      acStep =
        step
          (suc-≤-suc
            (≤SumRight (evalSize evStep₁) (evalSize evp₁ + evalSize evRec₁)))
    in
    evalDetTmAcc evStep₁ acStep (subst (λ x -> x =>e g') (sym srcStepEq) evStep₂)

evalDetTm : {t g g' : RawTerm} -> t =>e g -> t =>e g' -> g ≡ g'
evalDetTm ev₁ ev₂ = evalDetTmAcc ev₁ (<-wellfounded (evalSize ev₁)) ev₂
