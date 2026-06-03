{-# OPTIONS --safe #-}

module Recursive.Minimal.Renaming.Lookup where

open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to length++)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.Properties using (+-suc) renaming (+-identityʳ to +-zero)

open import Recursive.Prelude
open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Substitution
open import Recursive.Evaluation
open import Recursive.Derivability
open import Recursive.Presupposition using
  ( keepSubstCtx ; keepSubstCtx-subTy ; singleSubstCtx ; singleSubstCtx-subTy
  ; singleSubstCtx-subTm ; singleSubstCtx-apply
  ; sigmaCompSubCtx ; sigmaCompSubCtx-subTy ; sigmaCompSubCtx-subTm
  ; headSubstCtx ; headSubstCtx-subTy )

open import Recursive.Minimal.Base public
renFitsTargetWF : {gamma delta : Ctx} {rho : Ren}
  -> RenFits gamma delta rho
  -> MinCtxWF gamma
renFitsTargetWF (renFitsNil wf) = wf
renFitsTargetWF (renFitsKeep fits dA) =
  minWfCons (renFitsTargetWF fits) dA
renFitsTargetWF (renFitsSkip fits dB) =
  minWfCons (renFitsTargetWF fits) dB

infix 4 _∋_∶_

data _∋_∶_ : Ctx -> ℕ -> RawType -> Type where
  here : {gamma : Ctx} {A : RawType}
    -> (A ∷ gamma) ∋ zero ∶ wkTyBy 1 A
  there : {gamma : Ctx} {B T : RawType} {n : ℕ}
    -> gamma ∋ n ∶ T
    -> (B ∷ gamma) ∋ suc n ∶ wkTyBy 1 T

mkMember : (delta : Ctx) {A : RawType} {gamma : Ctx}
  -> (delta ++ (A ∷ gamma)) ∋ length delta ∶ wkTyBy (suc (length delta)) A
mkMember [] = here
mkMember (B ∷ delta) {A = A} {gamma = gamma} =
  subst
    (λ T -> (B ∷ (delta ++ (A ∷ gamma))) ∋ suc (length delta) ∶ T)
    (wkTyBy-suc (suc (length delta)) A)
    (there (mkMember delta))

memberOpe :
  {gamma delta : Ctx} {rho : Ren} {n : ℕ} {T : RawType}
  -> RenFits gamma delta rho
  -> delta ∋ n ∶ T
  -> gamma ∋ applyRen rho n ∶ renTy rho T
memberOpe (renFitsNil wf) ()
memberOpe (renFitsKeep {gamma = gamma} {rho = rho} {A = A} fits dA) here =
  subst
    (λ T -> (renTy rho A ∷ gamma) ∋ zero ∶ T)
    (sym (renTyKeepWk1 rho A))
    here
memberOpe
  (renFitsKeep {gamma = gamma} {rho = rho} {A = A} fits dA)
  (there {T = T} {n = n} mem) =
  subst
    (λ i -> (renTy rho A ∷ gamma) ∋ i ∶ renTy (raiseRen rho) (wkTyBy 1 T))
    (sym (applyRen-raise-suc rho n))
    (subst
      (λ Ty -> (renTy rho A ∷ gamma) ∋ suc (applyRen rho n) ∶ Ty)
      (sym (renTyKeepWk1 rho T))
      (there (memberOpe fits mem)))
memberOpe {n = n} {T = T}
  (renFitsSkip {gamma = gamma} {rho = rho} {B = B} fits dB)
  mem =
  subst
    (λ i -> (B ∷ gamma) ∋ i ∶ renTy (compRen sucRen rho) T)
    (sym (applyRen-compRen sucRen rho n))
    (subst
      (λ Ty -> (B ∷ gamma) ∋ suc (applyRen rho n) ∶ Ty)
      (sym (renTySkip rho T))
      (there (memberOpe fits mem)))

record MemberSplit (gamma : Ctx) (n : ℕ) (T : RawType) : Type where
  constructor memberSplit
  field
    sourceDelta : Ctx
    sourceTail : Ctx
    sourceA : RawType
    sourceCtxEq : gamma ≡ sourceDelta ++ (sourceA ∷ sourceTail)
    sourceIndexEq : n ≡ length sourceDelta
    sourceTypeEq : T ≡ wkTyBy (suc (length sourceDelta)) sourceA
    sourceAType : Minimal (isType sourceTail sourceA)
    sourceWF : MinCtxWF gamma

open MemberSplit public

memberSplitOf :
  {gamma : Ctx} {n : ℕ} {T : RawType}
  -> MinCtxWF gamma
  -> gamma ∋ n ∶ T
  -> MemberSplit gamma n T
memberSplitOf (minWfCons {gamma = gamma} {A = A} wf dA) here =
  memberSplit [] gamma A refl refl refl dA (minWfCons wf dA)
memberSplitOf (minWfCons {A = B} wf dB) (there mem)
  with memberSplitOf wf mem
... | memberSplit delta tail A ctxEq indexEq tyEqp dA _ =
  memberSplit
    (B ∷ delta)
    tail
    A
    (cong (B ∷_) ctxEq)
    (cong suc indexEq)
    (cong (wkTyBy 1) tyEqp ∙ wkTyBy-suc (suc (length delta)) A)
    dA
    (minWfCons wf dB)

memberToVarStar :
  {gamma : Ctx} {n : ℕ} {T : RawType}
  -> MinCtxWF gamma
  -> gamma ∋ n ∶ T
  -> Minimal (hasTy gamma (var n) T)
memberToVarStar {gamma = gamma} {n = n} {T = T} wf mem
  with memberSplitOf wf mem
... | memberSplit delta tail A ctxEq indexEq tyEqp dA wfGamma =
  subst
    (λ gamma -> Minimal (hasTy gamma (var n) T))
    (sym ctxEq)
    (subst
      (λ n -> Minimal (hasTy (delta ++ (A ∷ tail)) (var n) T))
      (sym indexEq)
      (subst
        (λ T -> Minimal (hasTy (delta ++ (A ∷ tail)) (var (length delta)) T))
        (sym tyEqp)
        (minVarStar (subst MinCtxWF ctxEq wfGamma) dA)))

renFitsLookupByMember :
  {target delta tail : Ctx} {rho : Ren} {A : RawType}
  -> RenFits target (delta ++ (A ∷ tail)) rho
  -> Minimal (isType tail A)
  -> Minimal
       (hasTy target
         (var (applyRen rho (length delta)))
         (renTy rho (wkTyBy (suc (length delta)) A)))
renFitsLookupByMember {delta = delta} fits dA =
  memberToVarStar (renFitsTargetWF fits) (memberOpe fits (mkMember delta))

renFitsLookup :
  {target delta tail : Ctx} {rho : Ren} {A : RawType}
  -> RenFits target (delta ++ (A ∷ tail)) rho
  -> Minimal (isType tail A)
  -> Minimal
       (hasTy target
         (var (applyRen rho (length delta)))
         (renTy rho (wkTyBy (suc (length delta)) A)))
renFitsLookup fits dA =
  renFitsLookupByMember fits dA

renFitsCastRen : {gamma delta : Ctx} {rho tau : Ren}
  -> rho ≡ tau
  -> RenFits gamma delta rho
  -> RenFits gamma delta tau
renFitsCastRen refl fits = fits

compRen-suc-drop-skip : (rho : Ren)
  -> compRen sucRen (compRen rho sucRen)
       ≡ compRen (compRen sucRen rho) sucRen
compRen-suc-drop-skip (shiftRen zero) = refl
compRen-suc-drop-skip (shiftRen (suc k)) =
  cong shiftRen (sym (+-assoc 1 (suc k) 1))
compRen-suc-drop-skip (consRen m rho) = refl

compRen-drop-add : (rho : Ren) (k : ℕ)
  -> compRen (compRen rho sucRen) (addRen k)
       ≡ compRen rho (addRen (suc k))
compRen-drop-add rho zero = refl
compRen-drop-add (shiftRen j) (suc k) =
  cong shiftRen (+-assoc j 1 (suc k))
compRen-drop-add (consRen m rho) k = refl

renFitsDrop1 : {target gamma : Ctx} {rho : Ren} {A : RawType}
  -> RenFits target (A ∷ gamma) rho
  -> RenFits target gamma (compRen rho sucRen)
renFitsDrop1 (renFitsKeep {rho = rho} fits dA) =
  renFitsCastRen (shiftCompRen rho) (renFitsSkip fits dA)
renFitsDrop1 (renFitsSkip {rho = rho} fits dB) =
  renFitsCastRen
    (compRen-suc-drop-skip rho)
    (renFitsSkip (renFitsDrop1 fits) dB)

renFitsDropBy : (delta : Ctx)
  -> {target gamma : Ctx} {rho : Ren}
  -> RenFits target (delta ++ gamma) rho
  -> RenFits target gamma (compRen rho (addRen (length delta)))
renFitsDropBy [] fits = fits
renFitsDropBy (B ∷ delta) {rho = rho} fits =
  renFitsCastRen
    (compRen-drop-add rho (length delta))
    (renFitsDropBy delta (renFitsDrop1 fits))

renFitsDropVar : (delta : Ctx)
  -> {target gamma : Ctx} {rho : Ren} {A : RawType}
  -> RenFits target (delta ++ (A ∷ gamma)) rho
  -> RenFits target gamma (compRen rho (addRen (suc (length delta))))
renFitsDropVar [] fits =
  renFitsDrop1 fits
renFitsDropVar (B ∷ delta) {rho = rho} fits =
  renFitsCastRen
    (compRen-drop-add rho (suc (length delta)))
    (renFitsDropVar delta (renFitsDrop1 fits))

minRenQtrCoherence :
  {target : Ctx} {rho : Ren} {A L : RawType} {l : RawTerm}
  -> Minimal
       (termEq (renTy (raiseRen rho) (wkTyBy 1 A) ∷ renTy rho A ∷ target)
         (renTm (raiseRen (raiseRen rho)) (wkTmBy 1 l))
         (renTm (raiseRen (raiseRen rho)) (renTm qtrSecondBranchRen l))
         (renTy (raiseRen (raiseRen rho)) (qtrCohTy L)))
  -> Minimal
       (termEq (wkTyBy 1 (renTy rho A) ∷ renTy rho A ∷ target)
         (wkTmBy 1 (renTm (raiseRen rho) l))
         (renTm qtrSecondBranchRen (renTm (raiseRen rho) l))
         (qtrCohTy (renTy (raiseRen rho) L)))
minRenQtrCoherence {target = target} {rho = rho} {A = A} {L = L} {l = l} cohRen =
  subst
    (λ H -> Minimal
      (termEq (H ∷ renTy rho A ∷ target)
        (wkTmBy 1 (renTm (raiseRen rho) l))
        (renTm qtrSecondBranchRen (renTm (raiseRen rho) l))
        (qtrCohTy (renTy (raiseRen rho) L))))
    (renTyKeepWk1 rho A)
    cohTermTy
  where
  cohLeft : Minimal
    (termEq (renTy (raiseRen rho) (wkTyBy 1 A) ∷ renTy rho A ∷ target)
      (wkTmBy 1 (renTm (raiseRen rho) l))
      (renTm (raiseRen (raiseRen rho)) (renTm qtrSecondBranchRen l))
      (renTy (raiseRen (raiseRen rho)) (qtrCohTy L)))
  cohLeft =
    subst
      (λ t -> Minimal
        (termEq (renTy (raiseRen rho) (wkTyBy 1 A) ∷ renTy rho A ∷ target)
          t
          (renTm (raiseRen (raiseRen rho)) (renTm qtrSecondBranchRen l))
          (renTy (raiseRen (raiseRen rho)) (qtrCohTy L))))
      (renQtrCohLeftTm rho l)
      cohRen

  cohRight : Minimal
    (termEq (renTy (raiseRen rho) (wkTyBy 1 A) ∷ renTy rho A ∷ target)
      (wkTmBy 1 (renTm (raiseRen rho) l))
      (renTm qtrSecondBranchRen (renTm (raiseRen rho) l))
      (renTy (raiseRen (raiseRen rho)) (qtrCohTy L)))
  cohRight =
    subst
      (λ t -> Minimal
        (termEq (renTy (raiseRen rho) (wkTyBy 1 A) ∷ renTy rho A ∷ target)
          (wkTmBy 1 (renTm (raiseRen rho) l))
          t
          (renTy (raiseRen (raiseRen rho)) (qtrCohTy L))))
      (renQtrCohRightTm rho l)
      cohLeft

  cohTermTy : Minimal
    (termEq (renTy (raiseRen rho) (wkTyBy 1 A) ∷ renTy rho A ∷ target)
      (wkTmBy 1 (renTm (raiseRen rho) l))
      (renTm qtrSecondBranchRen (renTm (raiseRen rho) l))
      (qtrCohTy (renTy (raiseRen rho) L)))
  cohTermTy =
    subst
      (λ T -> Minimal
        (termEq (renTy (raiseRen rho) (wkTyBy 1 A) ∷ renTy rho A ∷ target)
          (wkTmBy 1 (renTm (raiseRen rho) l))
          (renTm qtrSecondBranchRen (renTm (raiseRen rho) l))
          T))
      (renQtrCohTy rho L)
      cohRight
