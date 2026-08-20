
{-# OPTIONS --without-K #-}

module Inductive.MainTheorem where

open import Inductive.Prelude
open import Data.Product using (Σ-syntax ; _×_ ; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.List.Base using ([] ; _∷_)

open import Inductive.Syntax
open import Inductive.Context
open import Inductive.Evaluation
open import Inductive.Derivability
open import Data.Nat using (ℕ)
open import Inductive.Computability
open import Inductive.Inversion

canonicalType : {n : ℕ} ->
  {A : RawType} ->
  Computable n (isType [] A) ->
  Unit
canonicalType _ = tt

canonicalTypeEq : {n : ℕ} ->
  {A B : RawType} ->
  Computable n (typeEq [] A B) ->
  Unit
canonicalTypeEq _ = tt

canonicalTerm : {n : ℕ} ->
  {t : RawTerm} {A : RawType} ->
  Computable n (hasTy [] t A) ->
  Σ[ g ∈ RawTerm ] (t =>e g)
canonicalTerm (compTmClosedTop _ _ _ evt _) =
  tmStar , evt
canonicalTerm (compTmClosedSigma {a = a} {b = b} _ _ _ evt _ _ _) =
  tmPair a b , evt
canonicalTerm (compTmClosedEq _ _ _ evt _ _) =
  tmRefl , evt
canonicalTerm (compTmClosedQtr {a = a} _ _ _ evt _ _) =
  tmClass a , evt

canonicalTermEq : {n : ℕ} ->
  {t u : RawTerm} {A : RawType} ->
  Computable n (termEq [] t u A) ->
  Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] (t =>e g) × (u =>e h)
canonicalTermEq (compTmEqClosedTop _ _ _ _ evt evu) =
  tmStar , tmStar , evt , evu
canonicalTermEq (compTmEqClosedSigma {a = a} {b = b} {c = c} {d = d}
  _ _ _ _ evt evu _ _) =
  tmPair a b , tmPair c d , evt , evu
canonicalTermEq (compTmEqClosedEq _ _ _ _ evt evu _) =
  tmRefl , tmRefl , evt , evu
canonicalTermEq (compTmEqClosedQtr {a = a} {b = b} _ _ _ _ evt evu _ _) =
  tmClass a , tmClass b , evt , evu
