{-# OPTIONS --safe #-}

module Inductive.SigmaComp where

open import Inductive.FitsHelpers public
  using
    ( compFSigmaClosed
    ; compISigmaClosed
    ; compCSigmaClosed
    )

open import Inductive.OpenHyp public
  using
    ( compESigmaClosed
    )
