{-# OPTIONS --safe #-}

module Inductive.Syntax where

open import Inductive.Prelude
open import Data.Nat using (ℕ ; zero ; suc)

-- Object-language syntax for the regular fragment of Maietti's calculus.
-- The constructor prefixes keep object syntax distinct from Agda syntax:
--
--   Maietti notation    Agda constructor
--   ⊤                   tyTop
--   Σx∈A B(x)           tySigma A B
--   Eq(A , a , b)       tyEq A a b
--   A/⊤                 tyQtr A
--   x                   var n
--   ⋆                   tmStar
--   ⟨a , b⟩             tmPair a b
--   El Σ(d , m)         tmElSigma d m
--   eq_A(a)             tmRefl
--   [a]                 tmClass a
--   El Q(l , p)         tmElQtr l p
--
-- Binders are represented by de Bruijn indices; for example, the B in
-- tySigma A B is a raw type in the context extended by A.
mutual
  data RawType : Type where
    tyTop : RawType
    tySigma : RawType -> RawType -> RawType
    tyEq : RawType -> RawTerm -> RawTerm -> RawType
    tyQtr : RawType -> RawType

  data RawTerm : Type where
    var : ℕ -> RawTerm
    tmStar : RawTerm
    tmPair : RawTerm -> RawTerm -> RawTerm
    tmElSigma : RawTerm -> RawTerm -> RawTerm
    tmRefl : RawTerm
    tmEq : RawType -> RawTerm -> RawTerm
    tmClass : RawTerm -> RawTerm
    tmElQtr : RawTerm -> RawTerm -> RawTerm
