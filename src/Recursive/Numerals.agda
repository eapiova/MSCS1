{-# OPTIONS --safe #-}

-- Numerals: the spine-level canonicity statement for N.
--
-- The canonical form theorem gives, for a closed derivable term of N,
-- a value that is either tmZero or tmSuc n with n itself closed and
-- derivable -- one constructor deep.  The statement one actually wants
-- is that the term is judgementally equal to a NUMERAL s^k(0), and that
-- distinct numerals are never judgementally equal.  Both follow, but
-- neither is definitionally the canonical-form output: the spine needs a
-- structural recursion, and it is provided here by CanonicalNat, the
-- computability predicate at N, whose cSucV constructor recurses into
-- the predecessor.  That is what makes numeralForm terminate.

module Recursive.Numerals where

open import Data.Empty using (⊥)
open import Data.List.Base using ([])
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product using (Σ-syntax ; _×_ ; _,_ ; proj₂)
open import Relation.Nullary using (¬_)

open import Recursive.Prelude
open import Recursive.Syntax
open import Recursive.Context
open import Recursive.Evaluation
open import Recursive.Derivability
open import Recursive.Computable using (CanonicalNat ; cZeroV ; cSucV
                                       ; CanonicalNatEq ; cZeroVEq ; cSucVEq
                                       ; Computable ; ComputableTmEq)
open import Recursive.EvalSound using (evalSoundTm ; invSucAtNat)
open import Recursive.Fundamental using (fundTmClosed ; fundTmEqClosed)

-- ── Numerals ─────────────────────────────────────────────────────

numeral : ℕ -> RawTerm
numeral zero = tmZero
numeral (suc k) = tmSuc (numeral k)

numeralTy : (k : ℕ) -> Derivable (hasTy [] (numeral k) tyNat)
numeralTy zero = iZero wfNil
numeralTy (suc k) = iSuc (numeralTy k)

-- ── Every closed term of N is judgementally equal to a numeral ────
--
-- Structural on the CanonicalNat proof: cSucV carries the predecessor's
-- own CanonicalNat, so the recursive call is on a strict subterm.  The
-- typing of the predecessor comes from evaluation soundness followed by
-- suc-inversion, and the equalities are chained with the rule iSucEq.

numeralFormAux :
  {t : RawTerm}
  -> Derivable (hasTy [] t tyNat)
  -> CanonicalNat t
  -> Σ[ k ∈ ℕ ] Derivable (termEq [] t (numeral k) tyNat)
numeralFormAux d (cZeroV ev) =
  zero , proj₂ (evalSoundTm d ev)
numeralFormAux d (cSucV ev cn) =
  suc k , transTm evSuc (iSucEq eqPred)
  where
  sound = evalSoundTm d ev

  evSuc : Derivable (termEq [] _ (tmSuc _) tyNat)
  evSuc = proj₂ sound

  dPred : Derivable (hasTy [] _ tyNat)
  dPred = invSucAtNat (Data.Product.proj₁ sound)

  rec = numeralFormAux dPred cn

  k : ℕ
  k = Data.Product.proj₁ rec

  eqPred : Derivable (termEq [] _ (numeral k) tyNat)
  eqPred = proj₂ rec

numeralForm :
  {t : RawTerm}
  -> Derivable (hasTy [] t tyNat)
  -> Σ[ k ∈ ℕ ] Derivable (termEq [] t (numeral k) tyNat)
numeralForm d = numeralFormAux d (fundTmClosed d)

-- ── Distinct numerals are not judgementally equal ─────────────────
--
-- Via CanonicalNatEq, the computability relation for term equality at
-- N, which peels the two spines in lockstep.  A zero/suc mismatch is
-- refuted at the evaluation level: the only rule with a tmZero subject
-- is evalZero and the only one with a tmSuc subject is evalSucV, so the
-- offending evaluation has no constructor.

canonicalNatEqDistinct :
  (m n : ℕ)
  -> ¬ (m ≡ n)
  -> CanonicalNatEq (numeral m) (numeral n)
  -> ⊥
canonicalNatEqDistinct zero zero neq _ =
  neq refl
canonicalNatEqDistinct zero (suc n) neq (cZeroVEq _ ())
canonicalNatEqDistinct zero (suc n) neq (cSucVEq () _ _)
canonicalNatEqDistinct (suc m) zero neq (cZeroVEq () _)
canonicalNatEqDistinct (suc m) zero neq (cSucVEq _ () _)
canonicalNatEqDistinct (suc m) (suc n) neq (cZeroVEq () _)
canonicalNatEqDistinct (suc m) (suc n) neq (cSucVEq evalSucV evalSucV cne) =
  canonicalNatEqDistinct m n (λ eq -> neq (cong suc eq)) cne

numeralDistinct :
  (m n : ℕ)
  -> ¬ (m ≡ n)
  -> Derivable (termEq [] (numeral m) (numeral n) tyNat)
  -> ⊥
numeralDistinct m n neq d =
  canonicalNatEqDistinct m n neq (fundTmEqClosed d)

-- ── Numerical consistency ─────────────────────────────────────────
--
-- A false numeric equation has no closed proof.  The content is
-- numeralDistinct; equality reflection (eEqStar) only repackages it as
-- uninhabitability of the corresponding Eq type.
--
-- This is the statement the calculus can actually make.  The same shape
-- at Top is empty: Eq Top tt u is well formed only for u : Top, and the
-- Top reflection rule then forces u == tt, so no instance satisfies a
-- side condition asking u and tt to differ.

noEqProofDistinctNumerals :
  (m n : ℕ)
  -> ¬ (m ≡ n)
  -> {p : RawTerm}
  -> Derivable (hasTy [] p (tyEq tyNat (numeral m) (numeral n)))
  -> ⊥
noEqProofDistinctNumerals m n neq d =
  numeralDistinct m n neq
    (eEqStar d (fNat wfNil) (numeralTy m) (numeralTy n))

-- The converse direction: a judgemental equation between numerals
-- would inhabit the corresponding Eq type, by introduction at the
-- left numeral followed by conversion along the congruence.  So the
-- judgemental statement (numeralDistinct) and the propositional one
-- (noEqProofDistinctNumerals) are interderivable in this calculus:
-- reflection carries one way, introduction the other.

numeralEqInhabits :
  (m n : ℕ)
  -> Derivable (termEq [] (numeral m) (numeral n) tyNat)
  -> Derivable (hasTy [] tmRefl (tyEq tyNat (numeral m) (numeral n)))
numeralEqInhabits m n d =
  conv (iEq (numeralTy m))
    (fEqEq (reflTy (fNat wfNil)) (reflTm (numeralTy m)) d)

numeralDistinctFromConsistency :
  ((m n : ℕ) -> ¬ (m ≡ n) -> {p : RawTerm}
    -> Derivable (hasTy [] p (tyEq tyNat (numeral m) (numeral n))) -> ⊥)
  -> (m n : ℕ) -> ¬ (m ≡ n)
  -> Derivable (termEq [] (numeral m) (numeral n) tyNat)
  -> ⊥
numeralDistinctFromConsistency cons m n neq d =
  cons m n neq (numeralEqInhabits m n d)
