{-# OPTIONS --safe #-}

module Recursive.Fundamental.ComputabilityLemmas where

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

natZeroTargetTy : (sigma : Subst) (L : RawType)
  -> subTy sigma (subTy (singleSubst tmZero) L)
       ≡ subTy (consSubst tmZero sigma) L
natZeroTargetTy sigma L = subTyComp sigma (singleSubst tmZero) L

natStepArgTarget-apply : (n : RawTerm) (sigma : Subst) (k : ℕ)
  -> applySubst (compSub (consSubst n sigma) natStepArgSub) k
       ≡ applySubst (consSubst n sigma) k
natStepArgTarget-apply n sigma zero = refl
natStepArgTarget-apply n sigma (suc k) = refl

natStepArgTargetTy : (n : RawTerm) (sigma : Subst) (L : RawType)
  -> subTy (consSubst n sigma) (natStepArgTy L)
       ≡ subTy (consSubst n sigma) L
natStepArgTargetTy n sigma L =
  subTyComp (consSubst n sigma) natStepArgSub L
  ∙ subTyEq (natStepArgTarget-apply n sigma) L

natStepTarget-apply : (n rec : RawTerm) (sigma : Subst) (k : ℕ)
  -> applySubst (compSub (consSubst rec (consSubst n sigma)) natStepSub) k
       ≡ applySubst (consSubst (tmSuc n) sigma) k
natStepTarget-apply n rec sigma zero = refl
natStepTarget-apply n rec sigma (suc k) = refl

natStepTargetTy : (n rec : RawTerm) (sigma : Subst) (L : RawType)
  -> subTy (consSubst rec (consSubst n sigma)) (natStepTy L)
       ≡ subTy (consSubst (tmSuc n) sigma) L
natStepTargetTy n rec sigma L =
  subTyComp (consSubst rec (consSubst n sigma)) natStepSub L
  ∙ subTyEq (natStepTarget-apply n rec sigma) L

canonicalNatEq-leftEval : {t t' u : RawTerm}
  -> ({g : RawTerm} -> t =>e g -> t' =>e g)
  -> CanonicalNatEq t u
  -> CanonicalNatEq t' u
canonicalNatEq-leftEval f (cZeroVEq evt evu) =
  cZeroVEq (f evt) evu
canonicalNatEq-leftEval f (cSucVEq evt evu eqk) =
  cSucVEq (f evt) evu eqk

canonicalNatEq-rightEval : {t u u' : RawTerm}
  -> ({g : RawTerm} -> u =>e g -> u' =>e g)
  -> CanonicalNatEq t u
  -> CanonicalNatEq t u'
canonicalNatEq-rightEval f (cZeroVEq evt evu) =
  cZeroVEq evt (f evu)
canonicalNatEq-rightEval f (cSucVEq evt evu eqk) =
  cSucVEq evt (f evu) eqk

compTmEq-=>e-back-left : {A : RawType} {t g u : RawTerm}
  -> t =>e g -> ComputableTmEq A g u -> ComputableTmEq A t u
compTmEq-=>e-back-left {A = tyTop} ev (evg , evu) =
  eval-=>e-back ev evg , evu
compTmEq-=>e-back-left {A = tySigma A B} ev eq =
  let a , b , c , d , evg , evu , eqA , eqB , tyB = eq in
  a , b , c , d , eval-=>e-back ev evg , evu , eqA , eqB , tyB
compTmEq-=>e-back-left {A = tyEq A a b} ev (evg , evu , eqab) =
  eval-=>e-back ev evg , evu , eqab
compTmEq-=>e-back-left {A = tyQtr A} ev (a , b , evg , evu , caa , cbb) =
  a , b , eval-=>e-back ev evg , evu , caa , cbb
compTmEq-=>e-back-left {A = tyNat} ev eq =
  canonicalNatEq-leftEval (λ evg -> eval-=>e-back ev evg) eq

compTmEq-=>e-back-right : {A : RawType} {t u g : RawTerm}
  -> u =>e g -> ComputableTmEq A t g -> ComputableTmEq A t u
compTmEq-=>e-back-right {A = tyTop} ev (evt , evg) =
  evt , eval-=>e-back ev evg
compTmEq-=>e-back-right {A = tySigma A B} ev eq =
  let a , b , c , d , evt , evg , eqA , eqB , tyB = eq in
  a , b , c , d , evt , eval-=>e-back ev evg , eqA , eqB , tyB
compTmEq-=>e-back-right {A = tyEq A a b} ev (evt , evg , eqab) =
  evt , eval-=>e-back ev evg , eqab
compTmEq-=>e-back-right {A = tyQtr A} ev (a , b , evt , evg , caa , cbb) =
  a , b , evt , eval-=>e-back ev evg , caa , cbb
compTmEq-=>e-back-right {A = tyNat} ev eq =
  canonicalNatEq-rightEval (λ evg -> eval-=>e-back ev evg) eq

compTmEq-=>e-fwd-left : {A : RawType} {t g u : RawTerm}
  -> t =>e g -> ComputableTmEq A t u -> ComputableTmEq A g u
compTmEq-=>e-fwd-left {A = tyTop} ev (evt , evu) =
  eval-=>e-fwd ev evt , evu
compTmEq-=>e-fwd-left {A = tySigma A B} ev eq =
  let a , b , c , d , evt , evu , eqA , eqB , tyB = eq in
  a , b , c , d , eval-=>e-fwd ev evt , evu , eqA , eqB , tyB
compTmEq-=>e-fwd-left {A = tyEq A a b} ev (evt , evu , eqab) =
  eval-=>e-fwd ev evt , evu , eqab
compTmEq-=>e-fwd-left {A = tyQtr A} ev (a , b , evt , evu , caa , cbb) =
  a , b , eval-=>e-fwd ev evt , evu , caa , cbb
compTmEq-=>e-fwd-left {A = tyNat} ev eq =
  canonicalNatEq-leftEval (λ evt -> eval-=>e-fwd ev evt) eq

compTmEq-=>e-fwd-right : {A : RawType} {t u g : RawTerm}
  -> u =>e g -> ComputableTmEq A t u -> ComputableTmEq A t g
compTmEq-=>e-fwd-right {A = tyTop} ev (evt , evu) =
  evt , eval-=>e-fwd ev evu
compTmEq-=>e-fwd-right {A = tySigma A B} ev eq =
  let a , b , c , d , evt , evu , eqA , eqB , tyB = eq in
  a , b , c , d , evt , eval-=>e-fwd ev evu , eqA , eqB , tyB
compTmEq-=>e-fwd-right {A = tyEq A a b} ev (evt , evu , eqab) =
  evt , eval-=>e-fwd ev evu , eqab
compTmEq-=>e-fwd-right {A = tyQtr A} ev (a , b , evt , evu , caa , cbb) =
  a , b , evt , eval-=>e-fwd ev evu , caa , cbb
compTmEq-=>e-fwd-right {A = tyNat} ev eq =
  canonicalNatEq-rightEval (λ evu -> eval-=>e-fwd ev evu) eq

computableResult : {A : RawType} {t : RawTerm}
  -> Computable A t -> Σ[ g ∈ RawTerm ] (t =>e g) × Computable A g
computableResult {A = tyTop} ct = tmStar , ct , evalStar
computableResult {A = tySigma A B} ct =
  let a , b , ev , ca , cb = computableSigma-elim ct in
  tmPair a b , ev , computableSigma-intro (a , b , evalPair , ca , cb)
computableResult {A = tyEq A a b} ct =
  let ev , eqab = computableEq-elim ct in
  tmRefl , ev , computableEq-intro (evalRefl , eqab)
computableResult {A = tyQtr A} ct =
  let a , ev , ca = computableQtr-elim ct in
  tmClass a , ev , computableQtr-intro (a , evalClass , ca)
computableResult {A = tyNat} (cZeroV ev) =
  tmZero , ev , cZeroV evalZero
computableResult {A = tyNat} (cSucV {k = k} ev ck) =
  tmSuc k , ev , cSucV evalSucV ck

computableTySigma-introAcc : {A B : RawType}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> ComputableTy A
  -> ((a c : RawTerm) -> ComputableTmEq A a c
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B))
  -> ComputableTyAcc (tySigma A B) p
computableTySigma-introAcc {A} {B} (acc rs) cA fam =
  ComputableTyAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) cA ,
  λ a c eq ->
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
      (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a))
      (<-wf (tyDepth (subTy (singleSubst c) B))) (rs (subTy-snd< A B c))
      (fam a c
        (ComputableTmEqAcc-cast A
          (rs (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a c eq))

computableTySigma-intro : {A B : RawType}
  -> ComputableTy A
  -> ((a c : RawTerm) -> ComputableTmEq A a c
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B))
  -> ComputableTy (tySigma A B)
computableTySigma-intro {A} {B} =
  computableTySigma-introAcc (<-wf (tyDepth (tySigma A B)))

computableTyEqSigma-introAcc : {A B C D : RawType}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> (q : Acc _<_ (tyDepth (tySigma C D)))
  -> ComputableTyEq A C
  -> ((a c : RawTerm) -> ComputableTmEq A a c
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) D))
  -> ComputableTyEqAcc (tySigma A B) (tySigma C D) p q
computableTyEqSigma-introAcc {A} {B} {C} {D} (acc rsAB) (acc rsCD) eqAC fam =
  ComputableTyEqAcc-cast A C
    (<-wf (tyDepth A)) (rsAB (tyDepth-fst<Sigma A B))
    (<-wf (tyDepth C)) (rsCD (tyDepth-fst<Sigma C D))
    eqAC ,
  λ a c eq ->
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) D)
      (<-wf (tyDepth (subTy (singleSubst a) B))) (rsAB (subTy-snd< A B a))
      (<-wf (tyDepth (subTy (singleSubst c) D))) (rsCD (subTy-snd< C D c))
      (fam a c
        (ComputableTmEqAcc-cast A
          (rsAB (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a c eq))

computableTyEqSigma-intro : {A B C D : RawType}
  -> ComputableTyEq A C
  -> ((a c : RawTerm) -> ComputableTmEq A a c
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) D))
  -> ComputableTyEq (tySigma A B) (tySigma C D)
computableTyEqSigma-intro {A} {B} {C} {D} =
  computableTyEqSigma-introAcc
    (<-wf (tyDepth (tySigma A B))) (<-wf (tyDepth (tySigma C D)))

computableTmEqSigma-introAcc : {A B : RawType} {a b c d : RawTerm}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)
  -> ComputableTmEqAcc (tySigma A B) p (tmPair a b) (tmPair c d)
computableTmEqSigma-introAcc {A} {B} {a} {b} {c} {d} (acc rs) eqA eqB tyB =
  a , b , c , d , evalPair , evalPair ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) a c eqA ,
  ComputableTmEqAcc-cast (subTy (singleSubst a) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a)) b d eqB ,
  ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a))
    (<-wf (tyDepth (subTy (singleSubst c) B))) (rs (subTy-snd< A B c))
    tyB

computableTmEqSigma-intro : {A B : RawType} {a b c d : RawTerm}
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)
  -> ComputableTmEq (tySigma A B) (tmPair a b) (tmPair c d)
computableTmEqSigma-intro {A} {B} =
  computableTmEqSigma-introAcc (<-wf (tyDepth (tySigma A B)))

computableTmEqSigma-eval-introAcc : {A B : RawType} {t u a b c d : RawTerm}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> t =>e tmPair a b
  -> u =>e tmPair c d
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)
  -> ComputableTmEqAcc (tySigma A B) p t u
computableTmEqSigma-eval-introAcc {A} {B} {a = a} {b} {c} {d} (acc rs) evt evu eqA eqB tyB =
  a , b , c , d , evt , evu ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) a c eqA ,
  ComputableTmEqAcc-cast (subTy (singleSubst a) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a)) b d eqB ,
  ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a))
    (<-wf (tyDepth (subTy (singleSubst c) B))) (rs (subTy-snd< A B c))
    tyB

computableTmEqSigma-eval-intro : {A B : RawType} {t u a b c d : RawTerm}
  -> t =>e tmPair a b
  -> u =>e tmPair c d
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)
  -> ComputableTmEq (tySigma A B) t u
computableTmEqSigma-eval-intro {A} {B} =
  computableTmEqSigma-eval-introAcc (<-wf (tyDepth (tySigma A B)))

SigmaComputableTmEq : RawType -> RawType -> RawTerm -> RawTerm -> Type
SigmaComputableTmEq A B t u =
  Σ[ a ∈ RawTerm ] Σ[ b ∈ RawTerm ] Σ[ c ∈ RawTerm ] Σ[ d ∈ RawTerm ]
      (t =>e tmPair a b)
    × (u =>e tmPair c d)
    × ComputableTmEq A a c
    × ComputableTmEq (subTy (singleSubst a) B) b d
    × ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)

computableTmEqSigma-elimAcc : (A B : RawType)
  -> (p : Acc _<_ (tyDepth (tySigma A B))) (t u : RawTerm)
  -> ComputableTmEqAcc (tySigma A B) p t u
  -> SigmaComputableTmEq A B t u
computableTmEqSigma-elimAcc A B (acc rs) t u
  (a , b , c , d , evt , evu , eqA , eqB , tyB) =
  a , b , c , d , evt , evu ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a c eqA ,
  ComputableTmEqAcc-cast (subTy (singleSubst a) B)
    (rs (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B))) b d eqB ,
  ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
    (rs (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B)))
    (rs (subTy-snd< A B c)) (<-wf (tyDepth (subTy (singleSubst c) B)))
    tyB

computableTmEqSigma-elim : {A B : RawType} {t u : RawTerm}
  -> ComputableTmEq (tySigma A B) t u
  -> SigmaComputableTmEq A B t u
computableTmEqSigma-elim {A} {B} {t} {u} =
  computableTmEqSigma-elimAcc A B (<-wf (tyDepth (tySigma A B))) t u

SigmaComputableTy : RawType -> RawType -> Type
SigmaComputableTy A B =
    ComputableTy A
  × ((a c : RawTerm) -> ComputableTmEq A a c
      -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B))

computableTySigma-elimAcc : (A B : RawType)
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> ComputableTyAcc (tySigma A B) p
  -> SigmaComputableTy A B
computableTySigma-elimAcc A B (acc rs) (ctA , fam) =
  ComputableTyAcc-cast A
    (rs (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) ctA ,
  λ a c eq ->
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
      (rs (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B)))
      (rs (subTy-snd< A B c)) (<-wf (tyDepth (subTy (singleSubst c) B)))
      (fam a c
        (ComputableTmEqAcc-cast A
          (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) a c eq))

computableTySigma-elim : {A B : RawType}
  -> ComputableTy (tySigma A B)
  -> SigmaComputableTy A B
computableTySigma-elim {A} {B} =
  computableTySigma-elimAcc A B (<-wf (tyDepth (tySigma A B)))

SigmaComputableTyEq : RawType -> RawType -> RawType -> RawType -> Type
SigmaComputableTyEq A B C D =
    ComputableTyEq A C
  × ((a c : RawTerm) -> ComputableTmEq A a c
      -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) D))

computableTyEqSigma-elimAcc : (A B C D : RawType)
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> (q : Acc _<_ (tyDepth (tySigma C D)))
  -> ComputableTyEqAcc (tySigma A B) (tySigma C D) p q
  -> SigmaComputableTyEq A B C D
computableTyEqSigma-elimAcc A B C D (acc rsAB) (acc rsCD) (tyAC , fam) =
  ComputableTyEqAcc-cast A C
    (rsAB (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A))
    (rsCD (tyDepth-fst<Sigma C D)) (<-wf (tyDepth C))
    tyAC ,
  λ a c eq ->
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) D)
      (rsAB (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B)))
      (rsCD (subTy-snd< C D c)) (<-wf (tyDepth (subTy (singleSubst c) D)))
      (fam a c
        (ComputableTmEqAcc-cast A
          (<-wf (tyDepth A)) (rsAB (tyDepth-fst<Sigma A B)) a c eq))

computableTyEqSigma-elim : {A B C D : RawType}
  -> ComputableTyEq (tySigma A B) (tySigma C D)
  -> SigmaComputableTyEq A B C D
computableTyEqSigma-elim {A} {B} {C} {D} =
  computableTyEqSigma-elimAcc A B C D
    (<-wf (tyDepth (tySigma A B))) (<-wf (tyDepth (tySigma C D)))

computableTyEqForm-introAcc : {A : RawType} {a b : RawTerm}
  -> (p : Acc _<_ (tyDepth (tyEq A a b)))
  -> ComputableTy A
  -> Computable A a
  -> Computable A b
  -> ComputableTyAcc (tyEq A a b) p
computableTyEqForm-introAcc {A} {a} {b} (acc rs) cA ca cb =
  ComputableTyAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Eq A a b)) cA ,
  ca ,
  cb

computableTyEqForm-intro : {A : RawType} {a b : RawTerm}
  -> ComputableTy A
  -> Computable A a
  -> Computable A b
  -> ComputableTy (tyEq A a b)
computableTyEqForm-intro {A} {a} {b} =
  computableTyEqForm-introAcc (<-wf (tyDepth (tyEq A a b)))

computableTyQtr-introAcc : {A : RawType}
  -> (p : Acc _<_ (tyDepth (tyQtr A)))
  -> ComputableTy A
  -> ComputableTyAcc (tyQtr A) p
computableTyQtr-introAcc {A} (acc rs) cA =
  ComputableTyAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Qtr A)) cA

computableTyQtr-intro : {A : RawType}
  -> ComputableTy A
  -> ComputableTy (tyQtr A)
computableTyQtr-intro {A} =
  computableTyQtr-introAcc (<-wf (tyDepth (tyQtr A)))

computableTyQtr-elimAcc : (A : RawType)
  -> (p : Acc _<_ (tyDepth (tyQtr A)))
  -> ComputableTyAcc (tyQtr A) p
  -> ComputableTy A
computableTyQtr-elimAcc A (acc rs) cA =
  ComputableTyAcc-cast A
    (rs (tyDepth-base<Qtr A)) (<-wf (tyDepth A)) cA

computableTyQtr-elim : {A : RawType}
  -> ComputableTy (tyQtr A)
  -> ComputableTy A
computableTyQtr-elim {A} =
  computableTyQtr-elimAcc A (<-wf (tyDepth (tyQtr A)))

computableTyEqEqForm-introAcc : {A C : RawType} {a b c d : RawTerm}
  -> (p : Acc _<_ (tyDepth (tyEq A a b)))
  -> (q : Acc _<_ (tyDepth (tyEq C c d)))
  -> ComputableTyEq A C
  -> ComputableTmEq A a c
  -> ComputableTmEq A b d
  -> ComputableTyEqAcc (tyEq A a b) (tyEq C c d) p q
computableTyEqEqForm-introAcc {A} {C} {a} {b} {c} {d} (acc rsL) (acc rsR) tyAC eqac eqbd =
  ComputableTyEqAcc-cast A C
    (<-wf (tyDepth A)) (rsL (tyDepth-base<Eq A a b))
    (<-wf (tyDepth C)) (rsR (tyDepth-base<Eq C c d))
    tyAC ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rsL (tyDepth-base<Eq A a b)) a c eqac ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rsL (tyDepth-base<Eq A a b)) b d eqbd

computableTyEqEqForm-intro : {A C : RawType} {a b c d : RawTerm}
  -> ComputableTyEq A C
  -> ComputableTmEq A a c
  -> ComputableTmEq A b d
  -> ComputableTyEq (tyEq A a b) (tyEq C c d)
computableTyEqEqForm-intro {A} {C} {a} {b} {c} {d} =
  computableTyEqEqForm-introAcc
    (<-wf (tyDepth (tyEq A a b))) (<-wf (tyDepth (tyEq C c d)))

computableTyEqQtr-introAcc : {A C : RawType}
  -> (p : Acc _<_ (tyDepth (tyQtr A)))
  -> (q : Acc _<_ (tyDepth (tyQtr C)))
  -> ComputableTyEq A C
  -> ComputableTyEqAcc (tyQtr A) (tyQtr C) p q
computableTyEqQtr-introAcc {A} {C} (acc rsL) (acc rsR) tyAC =
  ComputableTyEqAcc-cast A C
    (<-wf (tyDepth A)) (rsL (tyDepth-base<Qtr A))
    (<-wf (tyDepth C)) (rsR (tyDepth-base<Qtr C))
    tyAC

computableTyEqQtr-intro : {A C : RawType}
  -> ComputableTyEq A C
  -> ComputableTyEq (tyQtr A) (tyQtr C)
computableTyEqQtr-intro {A} {C} =
  computableTyEqQtr-introAcc (<-wf (tyDepth (tyQtr A))) (<-wf (tyDepth (tyQtr C)))

computableTyEqQtr-elimAcc : (A C : RawType)
  -> (p : Acc _<_ (tyDepth (tyQtr A)))
  -> (q : Acc _<_ (tyDepth (tyQtr C)))
  -> ComputableTyEqAcc (tyQtr A) (tyQtr C) p q
  -> ComputableTyEq A C
computableTyEqQtr-elimAcc A C (acc rsA) (acc rsC) tyAC =
  ComputableTyEqAcc-cast A C
    (rsA (tyDepth-base<Qtr A)) (<-wf (tyDepth A))
    (rsC (tyDepth-base<Qtr C)) (<-wf (tyDepth C))
    tyAC

computableTyEqQtr-elim : {A C : RawType}
  -> ComputableTyEq (tyQtr A) (tyQtr C)
  -> ComputableTyEq A C
computableTyEqQtr-elim {A} {C} =
  computableTyEqQtr-elimAcc A C (<-wf (tyDepth (tyQtr A))) (<-wf (tyDepth (tyQtr C)))

computableTmEqEqForm-introAcc : {A : RawType} {a b t u : RawTerm}
  -> (p : Acc _<_ (tyDepth (tyEq A a b)))
  -> t =>e tmRefl
  -> u =>e tmRefl
  -> ComputableTmEq A a b
  -> ComputableTmEqAcc (tyEq A a b) p t u
computableTmEqEqForm-introAcc {A} {a} {b} (acc rs) evt evu eqab =
  evt , evu ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Eq A a b)) a b eqab

computableTmEqEqForm-intro : {A : RawType} {a b t u : RawTerm}
  -> t =>e tmRefl
  -> u =>e tmRefl
  -> ComputableTmEq A a b
  -> ComputableTmEq (tyEq A a b) t u
computableTmEqEqForm-intro {A} {a} {b} =
  computableTmEqEqForm-introAcc (<-wf (tyDepth (tyEq A a b)))

EqFormComputableTmEq : RawType -> RawTerm -> RawTerm -> RawTerm -> RawTerm -> Type
EqFormComputableTmEq A a b t u =
  (t =>e tmRefl) × (u =>e tmRefl) × ComputableTmEq A a b

computableTmEqEqForm-elimAcc : (A : RawType) (a b : RawTerm)
  -> (p : Acc _<_ (tyDepth (tyEq A a b))) (t u : RawTerm)
  -> ComputableTmEqAcc (tyEq A a b) p t u
  -> EqFormComputableTmEq A a b t u
computableTmEqEqForm-elimAcc A a b (acc rs) t u (evt , evu , eqab) =
  evt , evu ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-base<Eq A a b)) (<-wf (tyDepth A)) a b eqab

computableTmEqEqForm-elim : {A : RawType} {a b t u : RawTerm}
  -> ComputableTmEq (tyEq A a b) t u
  -> EqFormComputableTmEq A a b t u
computableTmEqEqForm-elim {A} {a} {b} {t} {u} =
  computableTmEqEqForm-elimAcc A a b (<-wf (tyDepth (tyEq A a b))) t u

computableTmEqQtr-introAcc : {A : RawType} {t u p q : RawTerm}
  -> (accQ : Acc _<_ (tyDepth (tyQtr A)))
  -> t =>e tmClass p
  -> u =>e tmClass q
  -> ComputableTmEq A p p
  -> ComputableTmEq A q q
  -> ComputableTmEqAcc (tyQtr A) accQ t u
computableTmEqQtr-introAcc {A} {p = p} {q = q} (acc rs) evt evu epp eqq =
  p , q , evt , evu ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Qtr A)) p p epp ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Qtr A)) q q eqq

computableTmEqQtr-intro : {A : RawType} {t u p q : RawTerm}
  -> t =>e tmClass p
  -> u =>e tmClass q
  -> ComputableTmEq A p p
  -> ComputableTmEq A q q
  -> ComputableTmEq (tyQtr A) t u
computableTmEqQtr-intro {A} =
  computableTmEqQtr-introAcc (<-wf (tyDepth (tyQtr A)))

QtrComputableTmEq : RawType -> RawTerm -> RawTerm -> Type
QtrComputableTmEq A t u =
  Σ[ p ∈ RawTerm ] Σ[ q ∈ RawTerm ]
      (t =>e tmClass p) × (u =>e tmClass q)
    × ComputableTmEq A p p
    × ComputableTmEq A q q

computableTmEqQtr-elimAcc : (A : RawType)
  -> (accQ : Acc _<_ (tyDepth (tyQtr A))) (t u : RawTerm)
  -> ComputableTmEqAcc (tyQtr A) accQ t u
  -> QtrComputableTmEq A t u
computableTmEqQtr-elimAcc A (acc rs) t u (p , q , evt , evu , epp , eqq) =
  p , q , evt , evu ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-base<Qtr A)) (<-wf (tyDepth A)) p p epp ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-base<Qtr A)) (<-wf (tyDepth A)) q q eqq

computableTmEqQtr-elim : {A : RawType} {t u : RawTerm}
  -> ComputableTmEq (tyQtr A) t u
  -> QtrComputableTmEq A t u
computableTmEqQtr-elim {A} {t} {u} =
  computableTmEqQtr-elimAcc A (<-wf (tyDepth (tyQtr A))) t u

compTmEqElimLeft : {A : RawType} {d m u b c : RawTerm}
  -> d =>e tmPair b c
  -> ComputableTmEq A (subTm (sigmaCompSub b c) m) u
  -> ComputableTmEq A (tmElSigma d m) u
compTmEqElimLeft {A = tyTop} evd (evm , evu) =
  evalElSigma evd evm , evu
compTmEqElimLeft {A = tySigma A B} evd eq =
  let a , b , c , d , evm , evu , eqA , eqB , tyB = eq in
  a , b , c , d , evalElSigma evd evm , evu , eqA , eqB , tyB
compTmEqElimLeft {A = tyEq A a b} evd (evm , evu , eqab) =
  evalElSigma evd evm , evu , eqab
compTmEqElimLeft {A = tyQtr A} evd (a , b , evm , evu , caa , cbb) =
  a , b , evalElSigma evd evm , evu , caa , cbb
compTmEqElimLeft {A = tyNat} evd eq =
  canonicalNatEq-leftEval (λ evm -> evalElSigma evd evm) eq

compTmEqElimRight : {A : RawType} {t d m b c : RawTerm}
  -> d =>e tmPair b c
  -> ComputableTmEq A t (subTm (sigmaCompSub b c) m)
  -> ComputableTmEq A t (tmElSigma d m)
compTmEqElimRight {A = tyTop} evd (evt , evm) =
  evt , evalElSigma evd evm
compTmEqElimRight {A = tySigma A B} evd eq =
  let a , b , c , d , evt , evm , eqA , eqB , tyB = eq in
  a , b , c , d , evt , evalElSigma evd evm , eqA , eqB , tyB
compTmEqElimRight {A = tyEq A a b} evd (evt , evm , eqab) =
  evt , evalElSigma evd evm , eqab
compTmEqElimRight {A = tyQtr A} evd (a , b , evt , evm , caa , cbb) =
  a , b , evt , evalElSigma evd evm , caa , cbb
compTmEqElimRight {A = tyNat} evd eq =
  canonicalNatEq-rightEval (λ evm -> evalElSigma evd evm) eq

compTmEqQtrElimLeft : {A : RawType} {p l u a : RawTerm}
  -> p =>e tmClass a
  -> ComputableTmEq A (subTm (qtrCompSub a) l) u
  -> ComputableTmEq A (tmElQtr l p) u
compTmEqQtrElimLeft {A = tyTop} evp (evl , evu) =
  evalElQtr evp evl , evu
compTmEqQtrElimLeft {A = tySigma A B} evp eq =
  let a , b , c , d , evl , evu , eqA , eqB , tyB = eq in
  a , b , c , d , evalElQtr evp evl , evu , eqA , eqB , tyB
compTmEqQtrElimLeft {A = tyEq A a b} evp (evl , evu , eqab) =
  evalElQtr evp evl , evu , eqab
compTmEqQtrElimLeft {A = tyQtr A} evp (a , b , evl , evu , caa , cbb) =
  a , b , evalElQtr evp evl , evu , caa , cbb
compTmEqQtrElimLeft {A = tyNat} evp eq =
  canonicalNatEq-leftEval (λ evl -> evalElQtr evp evl) eq

compTmEqQtrElimRight : {A : RawType} {t p l a : RawTerm}
  -> p =>e tmClass a
  -> ComputableTmEq A t (subTm (qtrCompSub a) l)
  -> ComputableTmEq A t (tmElQtr l p)
compTmEqQtrElimRight {A = tyTop} evp (evt , evl) =
  evt , evalElQtr evp evl
compTmEqQtrElimRight {A = tySigma A B} evp eq =
  let a , b , c , d , evt , evl , eqA , eqB , tyB = eq in
  a , b , c , d , evt , evalElQtr evp evl , eqA , eqB , tyB
compTmEqQtrElimRight {A = tyEq A a b} evp (evt , evl , eqab) =
  evt , evalElQtr evp evl , eqab
compTmEqQtrElimRight {A = tyQtr A} evp (a , b , evt , evl , caa , cbb) =
  a , b , evt , evalElQtr evp evl , caa , cbb
compTmEqQtrElimRight {A = tyNat} evp eq =
  canonicalNatEq-rightEval (λ evl -> evalElQtr evp evl) eq

compTmEqElNatZLeft : {A : RawType} {a l p u : RawTerm}
  -> p =>e tmZero
  -> ComputableTmEq A a u
  -> ComputableTmEq A (tmElNat a l p) u
compTmEqElNatZLeft {A = tyTop} evp (eva , evu) =
  evalElNatZ evp eva , evu
compTmEqElNatZLeft {A = tySigma A B} evp eq =
  let a , b , c , d , eva , evu , eqA , eqB , tyB = eq in
  a , b , c , d , evalElNatZ evp eva , evu , eqA , eqB , tyB
compTmEqElNatZLeft {A = tyEq A a b} evp (eva , evu , eqab) =
  evalElNatZ evp eva , evu , eqab
compTmEqElNatZLeft {A = tyQtr A} evp eq =
  let a , b , eva , evu , caa , cbb = eq in
  a , b , evalElNatZ evp eva , evu , caa , cbb
compTmEqElNatZLeft {A = tyNat} evp eq =
  canonicalNatEq-leftEval (λ eva -> evalElNatZ evp eva) eq

compTmEqElNatZRight : {A : RawType} {t a l p : RawTerm}
  -> p =>e tmZero
  -> ComputableTmEq A t a
  -> ComputableTmEq A t (tmElNat a l p)
compTmEqElNatZRight {A = tyTop} evp (evt , eva) =
  evt , evalElNatZ evp eva
compTmEqElNatZRight {A = tySigma A B} evp eq =
  let a , b , c , d , evt , eva , eqA , eqB , tyB = eq in
  a , b , c , d , evt , evalElNatZ evp eva , eqA , eqB , tyB
compTmEqElNatZRight {A = tyEq A a b} evp (evt , eva , eqab) =
  evt , evalElNatZ evp eva , eqab
compTmEqElNatZRight {A = tyQtr A} evp eq =
  let a , b , evt , eva , caa , cbb = eq in
  a , b , evt , evalElNatZ evp eva , caa , cbb
compTmEqElNatZRight {A = tyNat} evp eq =
  canonicalNatEq-rightEval (λ eva -> evalElNatZ evp eva) eq

compTmEqElNatSLeft : {A : RawType} {a l p k rec u : RawTerm}
  -> p =>e tmSuc k
  -> tmElNat a l k =>e rec
  -> ComputableTmEq A (subTm (natStepCompSub k rec) l) u
  -> ComputableTmEq A (tmElNat a l p) u
compTmEqElNatSLeft {A = tyTop} evp evRec (evStep , evu) =
  evalElNatS evp evRec evStep , evu
compTmEqElNatSLeft {A = tySigma A B} evp evRec eq =
  let a , b , c , d , evStep , evu , eqA , eqB , tyB = eq in
  a , b , c , d , evalElNatS evp evRec evStep , evu , eqA , eqB , tyB
compTmEqElNatSLeft {A = tyEq A a b} evp evRec (evStep , evu , eqab) =
  evalElNatS evp evRec evStep , evu , eqab
compTmEqElNatSLeft {A = tyQtr A} evp evRec eq =
  let a , b , evStep , evu , caa , cbb = eq in
  a , b , evalElNatS evp evRec evStep , evu , caa , cbb
compTmEqElNatSLeft {A = tyNat} evp evRec eq =
  canonicalNatEq-leftEval (λ evStep -> evalElNatS evp evRec evStep) eq

compTmEqElNatSRight : {A : RawType} {t a l p k rec : RawTerm}
  -> p =>e tmSuc k
  -> tmElNat a l k =>e rec
  -> ComputableTmEq A t (subTm (natStepCompSub k rec) l)
  -> ComputableTmEq A t (tmElNat a l p)
compTmEqElNatSRight {A = tyTop} evp evRec (evt , evStep) =
  evt , evalElNatS evp evRec evStep
compTmEqElNatSRight {A = tySigma A B} evp evRec eq =
  let a , b , c , d , evt , evStep , eqA , eqB , tyB = eq in
  a , b , c , d , evt , evalElNatS evp evRec evStep , eqA , eqB , tyB
compTmEqElNatSRight {A = tyEq A a b} evp evRec (evt , evStep , eqab) =
  evt , evalElNatS evp evRec evStep , eqab
compTmEqElNatSRight {A = tyQtr A} evp evRec eq =
  let a , b , evt , evStep , caa , cbb = eq in
  a , b , evt , evalElNatS evp evRec evStep , caa , cbb
compTmEqElNatSRight {A = tyNat} evp evRec eq =
  canonicalNatEq-rightEval (λ evStep -> evalElNatS evp evRec evStep) eq
