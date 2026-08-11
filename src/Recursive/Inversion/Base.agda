{-# OPTIONS --safe #-}

module Recursive.Inversion.Base where

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

data Maybe (A : Type) : Type where
  nothing : Maybe A
  just : A -> Maybe A

IsJust : {A : Type} -> Maybe A -> Type
IsJust nothing = ⊥
IsJust (just _) = ⊤

data TyHead : Type where
  headTop : TyHead
  headSigma : TyHead
  headEq : TyHead
  headQtr : TyHead
  headNat : TyHead

tyHead : RawType -> TyHead
tyHead tyTop = headTop
tyHead (tySigma _ _) = headSigma
tyHead (tyEq _ _ _) = headEq
tyHead (tyQtr _) = headQtr
tyHead tyNat = headNat

minimalTyEqHead : {gamma : Ctx} {A B : RawType}
  -> Minimal (typeEq gamma A B)
  -> tyHead A ≡ tyHead B
minimalTyEqHead (minReflTy _) = refl
minimalTyEqHead (minSymTy d _) = sym (minimalTyEqHead d)
minimalTyEqHead (minTransTy d e) = minimalTyEqHead d ∙ minimalTyEqHead e
minimalTyEqHead (minFSigmaEq _ _ _ _) = refl
minimalTyEqHead (minFEqEq _ _ _ _) = refl
minimalTyEqHead (minFQtrEq _) = refl
