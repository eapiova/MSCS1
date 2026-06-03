{-# OPTIONS --safe #-}

module Recursive.Minimal.Renaming.Core where

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

open import Recursive.Minimal.Renaming.Lookup public
mutual
  minRen : {J : JForm} {target : Ctx} {rho : Ren}
    -> Minimal J
    -> RenFits target (ctxOf J) rho
    -> Minimal (renJTo target rho J)
  minRen d@(minVarStar wf dA) fits =
    renFitsLookup fits dA
  minRen (minReflTy d) fits =
    minReflTy (minRen d fits)
  minRen (minReflTm d) fits =
    minReflTm (minRen d fits)
  minRen (minSymTy d dB) fits =
    minSymTy (minRen d fits) (minRen dB fits)
  minRen (minSymTm d du dA) fits =
    minSymTm (minRen d fits) (minRen du fits) (minRen dA fits)
  minRen (minTransTy d e) fits =
    minTransTy (minRen d fits) (minRen e fits)
  minRen (minTransTm d e) fits =
    minTransTm (minRen d fits) (minRen e fits)
  minRen (minConv d dAB) fits =
    minConv (minRen d fits) (minRen dAB fits)
  minRen (minConvEq d dAB) fits =
    minConvEq (minRen d fits) (minRen dAB fits)
  minRen (minFTop wf) fits =
    minFTop (renFitsTargetWF fits)
  minRen (minITop wf) fits =
    minITop (renFitsTargetWF fits)
  minRen (minCTop d) fits =
    minCTop (minRen d fits)
  minRen (minFSigma dA dB) fits =
    minFSigma dA' dB'
    where
    dA' = minRen dA fits
    dB' = minRen dB (renFitsKeep fits dA')
  minRen (minFSigmaEq dAC dB dBD dRight) fits =
    minFSigmaEq dAC' dB' dBD' dRight'
    where
    dAC' = minRen dAC fits
    dA' = minRenTyEqLeft dAC fits
    dB' = minRen dB (renFitsKeep fits dA')
    dBD' = minRen dBD (renFitsKeep fits dA')
    dRight' = minRen dRight fits
  minRen {rho = rho}
    (minISigma {gamma = gamma} {a = a} {b = b} {A = A} {B = B} da db dSigma) fits =
    minISigma da' db' dSigma'
    where
    da' = minRen da fits
    dbRen = minRen db fits
    db' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renSingleSubstTy rho a B)
        dbRen
    dSigma' = minRen dSigma fits
  minRen {rho = rho}
    (minISigmaEq {gamma = gamma} {a = a} {b = b} {c = c} {d = d} {A = A} {B = B}
      dac dbd dA dB) fits =
    minISigmaEq dac' dbd' dA' dB'
    where
    dac' = minRen dac fits
    dbdRen = minRen dbd fits
    dbd' =
      subst
        (λ T -> Minimal (termEq _ _ _ T))
        (renSingleSubstTy rho a B)
        dbdRen
    dA' = minRen dA fits
    dB' = minRen dB (renFitsKeep fits dA')
  minRen {target = target} {rho = rho}
    (minESigma {gamma = gamma} {A = A} {B = B} {M = M} {d = d} {m = m}
      dM dd dSigma dm dTy) fits =
    subst
      (λ T -> Minimal
        (hasTy target
          (tmElSigma (renTm rho d) (renTm (raiseRen (raiseRen rho)) _))
          T))
      (sym (renSingleSubstTy rho d M))
      (minESigma dM' dd' dSigma' dm' dTy')
    where
    dd' = minRen dd fits
    dSigma' = minRen dSigma fits
    dA' = minSigmaLeft dSigma'
    dB' = minSigmaRight dSigma'
    dM' = minRen dM (renFitsKeep fits dSigma')
    dmRen = minRen dm (renFitsKeep (renFitsKeep fits dA') dB')
    dm' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renSigmaBranchTy rho M)
        dmRen
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho d M)
        dTyRen
  minRen {target = target} {rho = rho}
    (minESigmaEq {gamma = gamma} {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'}
      dM dd dSigma dm dmm dTy) fits =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElSigma (renTm rho _) (renTm (raiseRen (raiseRen rho)) _))
          (tmElSigma (renTm rho _) (renTm (raiseRen (raiseRen rho)) _))
          T))
      (sym (renSingleSubstTy rho d M))
      (minESigmaEq dM' dd' dSigma' dm' dmm' dTy')
    where
    dd' = minRen dd fits
    dSigma' = minRen dSigma fits
    dA' = minSigmaLeft dSigma'
    dB' = minSigmaRight dSigma'
    dM' = minRen dM (renFitsKeep fits dSigma')
    dmRen = minRen dm (renFitsKeep (renFitsKeep fits dA') dB')
    dm' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renSigmaBranchTy rho M)
        dmRen
    dmmRen = minRen dmm (renFitsKeep (renFitsKeep fits dA') dB')
    dmm' =
      subst
        (λ T -> Minimal (termEq _ _ _ T))
        (renSigmaBranchTy rho M)
        dmmRen
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho d M)
        dTyRen
  minRen {target = target} {rho = rho}
    (minCSigma {gamma = gamma} {A = A} {B = B} {M = M} {b = b} {c = c} {m = m}
      dM dSigma db dc dm dTy) fits =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElSigma (tmPair (renTm rho b) (renTm rho c)) (renTm (raiseRen (raiseRen rho)) m))
          (renTm rho (subTm (sigmaCompSub b c) m))
          T))
      (sym (renSingleSubstTy rho (tmPair b c) M))
      (subst
        (λ u -> Minimal
          (termEq target
            (tmElSigma (tmPair (renTm rho b) (renTm rho c)) (renTm (raiseRen (raiseRen rho)) m))
            u
            (subTy (singleSubst (tmPair (renTm rho b) (renTm rho c))) (renTy (raiseRen rho) M))))
        (sym (renSigmaCompSubTm rho b c m))
        (minCSigma dM' dSigma' db' dc' dm' dTy'))
    where
    dSigma' = minRen dSigma fits
    dA' = minSigmaLeft dSigma'
    dB' = minSigmaRight dSigma'
    dM' = minRen dM (renFitsKeep fits dSigma')
    db' = minRen db fits
    dcRen = minRen dc fits
    dc' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renSingleSubstTy rho b B)
        dcRen
    dmRen = minRen dm (renFitsKeep (renFitsKeep fits dA') dB')
    dm' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renSigmaBranchTy rho M)
        dmRen
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho (tmPair b c) M)
        dTyRen
  minRen (minFEq dA da db) fits =
    minFEq (minRen dA fits) (minRen da fits) (minRen db fits)
  minRen (minFEqEq dAC dac dbd dRight) fits =
    minFEqEq (minRen dAC fits) (minRen dac fits) (minRen dbd fits) (minRen dRight fits)
  minRen (minIEq da) fits =
    minIEq (minRen da fits)
  minRen (minIEqEq d) fits =
    minIEqEq (minRen d fits)
  minRen (minEEqStar dp dA da db) fits =
    minEEqStar (minRen dp fits) (minRen dA fits) (minRen da fits) (minRen db fits)
  minRen (minCEq dp dA da db) fits =
    minCEq (minRen dp fits) (minRen dA fits) (minRen da fits) (minRen db fits)
  minRen (minFQtr dA) fits =
    minFQtr (minRen dA fits)
  minRen (minFQtrEq dAB) fits =
    minFQtrEq (minRen dAB fits)
  minRen (minIQtr da) fits =
    minIQtr (minRen da fits)
  minRen (minIQtrEq da db) fits =
    minIQtrEq (minRen da fits) (minRen db fits)
  minRen {target = target} {rho = rho}
    (minEQtr {A = A} {L = L} {l = l} {p = p} dL dp dA dBranchTy dl dWkA coh dTy) fits =
    subst
      (λ T -> Minimal
        (hasTy target (tmElQtr (renTm (raiseRen rho) l) (renTm rho p)) T))
      (sym (renSingleSubstTy rho p L))
      (minEQtr dL' dp' dA' dBranchTy' dl' dWkA' coh' dTy')
    where
    dp' = minRen dp fits
    dA' = minRen dA fits
    dQtr' = minFQtr dA'
    fitsA = renFitsKeep fits dA'
    dL' = minRen dL (renFitsKeep fits dQtr')
    dBranchTyRen = minRen dBranchTy fitsA
    dBranchTy' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renQtrBranchTy rho L)
        dBranchTyRen
    dlRen = minRen dl fitsA
    dl' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renQtrBranchTy rho L)
        dlRen
    dWkARen = minRen dWkA fitsA
    dWkA' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renTyKeepWk1 rho A)
        dWkARen
    fitsCoh = renFitsKeep fitsA dWkARen
    coh' = minRenQtrCoherence (minRen coh fitsCoh)
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho p L)
        dTyRen
  minRen {target = target} {rho = rho}
    (minEQtrEq {A = A} {L = L} {l = l} {l' = l'} {p = p}
      dL dp dA dBranchTy dl dl' dll' dWkA coh coh' dTy) fits =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElQtr (renTm (raiseRen rho) l) (renTm rho p))
          (tmElQtr (renTm (raiseRen rho) l') _)
          T))
      (sym (renSingleSubstTy rho p L))
      (minEQtrEq dL' dp' dA' dBranchTy' dlL' dlR' dll'' dWkA' cohL' cohR' dTy')
    where
    dp' = minRen dp fits
    dA' = minRen dA fits
    dQtr' = minFQtr dA'
    fitsA = renFitsKeep fits dA'
    dL' = minRen dL (renFitsKeep fits dQtr')
    dBranchTyRen = minRen dBranchTy fitsA
    dBranchTy' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renQtrBranchTy rho L)
        dBranchTyRen
    dlLRen = minRen dl fitsA
    dlL' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renQtrBranchTy rho L)
        dlLRen
    dlRRen = minRen dl' fitsA
    dlR' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renQtrBranchTy rho L)
        dlRRen
    dllRen = minRen dll' fitsA
    dll'' =
      subst
        (λ T -> Minimal (termEq _ _ _ T))
        (renQtrBranchTy rho L)
        dllRen
    dWkARen = minRen dWkA fitsA
    dWkA' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renTyKeepWk1 rho A)
        dWkARen
    fitsCoh = renFitsKeep fitsA dWkARen
    cohL' = minRenQtrCoherence (minRen coh fitsCoh)
    cohR' = minRenQtrCoherence (minRen coh' fitsCoh)
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho p L)
        dTyRen
  minRen {target = target} {rho = rho}
    (minCQtr {A = A} {L = L} {a = a} {l = l} dL da dA dBranchTy dl dWkA coh dTy) fits =
    subst
      (λ T -> Minimal
        (termEq target
          (tmElQtr (renTm (raiseRen rho) l) (tmClass (renTm rho a)))
          (renTm rho (subTm (qtrCompSub a) l))
          T))
      (sym (renSingleSubstTy rho (tmClass a) L))
      (subst
        (λ u -> Minimal
          (termEq target
            (tmElQtr (renTm (raiseRen rho) l) (tmClass (renTm rho a)))
            u
            (subTy (singleSubst (tmClass (renTm rho a))) (renTy (raiseRen rho) L))))
        (sym (renQtrCompSubTm rho a l))
        (minCQtr dL' da' dA' dBranchTy' dl' dWkA' coh' dTy'))
    where
    da' = minRen da fits
    dA' = minRen dA fits
    fitsA = renFitsKeep fits dA'
    dL' = minRen dL (renFitsKeep fits (minFQtr dA'))
    dBranchTyRen = minRen dBranchTy fitsA
    dBranchTy' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renQtrBranchTy rho L)
        dBranchTyRen
    dlRen = minRen dl fitsA
    dl' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renQtrBranchTy rho L)
        dlRen
    dWkARen = minRen dWkA fitsA
    dWkA' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renTyKeepWk1 rho A)
        dWkARen
    fitsCoh = renFitsKeep fitsA dWkARen
    coh' = minRenQtrCoherence (minRen coh fitsCoh)
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho (tmClass a) L)
        dTyRen

  minRenTmTy : {gamma target : Ctx} {rho : Ren} {t : RawTerm} {A : RawType}
    -> Minimal (hasTy gamma t A)
    -> RenFits target gamma rho
    -> Minimal (isType target (renTy rho A))
  minRenTmTy {rho = rho}
    (minVarStar {gamma = gamma} {delta = delta} {A = A} wf dA) fits =
    subst
      (λ T -> Minimal (isType _ T))
      (sym (renTyComp rho (addRen (suc (length delta))) A))
      (minRen dA (renFitsDropVar delta fits))
  minRenTmTy (minConv d dAB) fits =
    minRenTyEqRight dAB fits
  minRenTmTy (minITop wf) fits =
    minFTop (renFitsTargetWF fits)
  minRenTmTy (minISigma da db dSigma) fits =
    minRen dSigma fits
  minRenTmTy (minESigma _ _ _ _ dTy) fits =
    minRen dTy fits
  minRenTmTy (minIEq da) fits =
    minFEq (minRenTmTy da fits) (minRen da fits) (minRen da fits)
  minRenTmTy (minIQtr da) fits =
    minFQtr (minRenTmTy da fits)
  minRenTmTy (minEQtr _ _ _ _ _ _ _ dTy) fits =
    minRen dTy fits

  minRenTyEqLeft : {gamma target : Ctx} {rho : Ren} {A B : RawType}
    -> Minimal (typeEq gamma A B)
    -> RenFits target gamma rho
    -> Minimal (isType target (renTy rho A))
  minRenTyEqLeft (minReflTy d) fits =
    minRen d fits
  minRenTyEqLeft (minSymTy _ dB) fits =
    minRen dB fits
  minRenTyEqLeft (minTransTy d _) fits =
    minRenTyEqLeft d fits
  minRenTyEqLeft (minFSigmaEq dAC dB _ _) fits =
    minFSigma dA' dB'
    where
    dA' = minRenTyEqLeft dAC fits
    dB' = minRen dB (renFitsKeep fits dA')
  minRenTyEqLeft (minFEqEq dAC dac dbd _) fits =
    minFEq (minRenTyEqLeft dAC fits)
      (minRenTmEqLeft dac fits)
      (minRenTmEqLeft dbd fits)
  minRenTyEqLeft (minFQtrEq d) fits =
    minFQtr (minRenTyEqLeft d fits)

  minRenTyEqRight : {gamma target : Ctx} {rho : Ren} {A B : RawType}
    -> Minimal (typeEq gamma A B)
    -> RenFits target gamma rho
    -> Minimal (isType target (renTy rho B))
  minRenTyEqRight (minReflTy d) fits =
    minRen d fits
  minRenTyEqRight (minSymTy d _) fits =
    minRenTyEqLeft d fits
  minRenTyEqRight (minTransTy _ d) fits =
    minRenTyEqRight d fits
  minRenTyEqRight (minFSigmaEq _ _ _ dRight) fits =
    minRen dRight fits
  minRenTyEqRight (minFEqEq _ _ _ dRight) fits =
    minRen dRight fits
  minRenTyEqRight (minFQtrEq d) fits =
    minFQtr (minRenTyEqRight d fits)

  minRenTmEqLeft : {gamma target : Ctx} {rho : Ren} {t u : RawTerm} {A : RawType}
    -> Minimal (termEq gamma t u A)
    -> RenFits target gamma rho
    -> Minimal (hasTy target (renTm rho t) (renTy rho A))
  minRenTmEqLeft (minReflTm d) fits =
    minRen d fits
  minRenTmEqLeft (minSymTm _ du _) fits =
    minRen du fits
  minRenTmEqLeft (minTransTm d _) fits =
    minRenTmEqLeft d fits
  minRenTmEqLeft (minConvEq d dAB) fits =
    minConv (minRenTmEqLeft d fits) (minRen dAB fits)
  minRenTmEqLeft (minCTop d) fits =
    minRen d fits
  minRenTmEqLeft {rho = rho}
    (minISigmaEq {gamma = gamma} {a = a} {b = b} {c = c} {d = d} {A = A} {B = B}
      dac dbd dA dB) fits =
    minISigma da' db' dSigma'
    where
    da' = minRenTmEqLeft dac fits
    dbRen = minRenTmEqLeft dbd fits
    db' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renSingleSubstTy rho a B)
        dbRen
    dA' = minRen dA fits
    dB' = minRen dB (renFitsKeep fits dA')
    dSigma' = minFSigma dA' dB'
  minRenTmEqLeft {target = target} {rho = rho}
    (minESigmaEq {gamma = gamma} {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'}
      dM dd dSigma dm dmm dTy) fits =
    subst
      (λ T -> Minimal
        (hasTy target
          (tmElSigma (renTm rho d) (renTm (raiseRen (raiseRen rho)) _))
          T))
      (sym (renSingleSubstTy rho d M))
      (minESigma dM' ddL' dSigma' dm' dTy')
    where
    ddL' = minRenTmEqLeft dd fits
    dSigma' = minRen dSigma fits
    dA' = minSigmaLeft dSigma'
    dB' = minSigmaRight dSigma'
    dM' = minRen dM (renFitsKeep fits dSigma')
    dmRen = minRen dm (renFitsKeep (renFitsKeep fits dA') dB')
    dm' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renSigmaBranchTy rho M)
        dmRen
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho d M)
        dTyRen
  minRenTmEqLeft {target = target} {rho = rho}
    (minCSigma {gamma = gamma} {A = A} {B = B} {M = M} {b = b} {c = c} {m = m}
      dM dSigma db dc dm dTy) fits =
    subst
      (λ T -> Minimal
        (hasTy target
          (tmElSigma (tmPair (renTm rho b) (renTm rho c)) (renTm (raiseRen (raiseRen rho)) m))
          T))
      (sym (renSingleSubstTy rho (tmPair b c) M))
      (minESigma dM' dPair' dSigma' dm' dTy')
    where
    dSigma' = minRen dSigma fits
    dA' = minSigmaLeft dSigma'
    dB' = minSigmaRight dSigma'
    dM' = minRen dM (renFitsKeep fits dSigma')
    db' = minRen db fits
    dcRen = minRen dc fits
    dc' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renSingleSubstTy rho b B)
        dcRen
    dPair' = minISigma db' dc' dSigma'
    dmRen = minRen dm (renFitsKeep (renFitsKeep fits dA') dB')
    dm' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renSigmaBranchTy rho M)
        dmRen
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho (tmPair b c) M)
        dTyRen
  minRenTmEqLeft (minIEqEq d) fits =
    minIEq (minRenTmEqLeft d fits)
  minRenTmEqLeft (minEEqStar _ _ da _) fits =
    minRen da fits
  minRenTmEqLeft (minCEq p _ _ _) fits =
    minRen p fits
  minRenTmEqLeft (minIQtrEq da _) fits =
    minIQtr (minRen da fits)
  minRenTmEqLeft {target = target} {rho = rho}
    (minEQtrEq {gamma = gamma} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
      dL dp dA dBranchTy dl _ _ dWkA coh _ dTy) fits =
    subst
      (λ T -> Minimal
        (hasTy target (tmElQtr (renTm (raiseRen rho) l) (renTm rho p)) T))
      (sym (renSingleSubstTy rho p L))
      (minEQtr dL' dpL' dA' dBranchTy' dl' dWkA' coh' dTy')
    where
    dpL' = minRenTmEqLeft dp fits
    dA' = minRen dA fits
    dQtr' = minFQtr dA'
    fitsA = renFitsKeep fits dA'
    dL' = minRen dL (renFitsKeep fits dQtr')
    dBranchTyRen = minRen dBranchTy fitsA
    dBranchTy' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renQtrBranchTy rho L)
        dBranchTyRen
    dlRen = minRen dl fitsA
    dl' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renQtrBranchTy rho L)
        dlRen
    dWkARen = minRen dWkA fitsA
    dWkA' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renTyKeepWk1 rho A)
        dWkARen
    fitsCoh = renFitsKeep fitsA dWkARen
    coh' = minRenQtrCoherence (minRen coh fitsCoh)
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho p L)
        dTyRen
  minRenTmEqLeft {target = target} {rho = rho}
    (minCQtr {gamma = gamma} {A = A} {L = L} {a = a} {l = l}
      dL da dA dBranchTy dl dWkA coh dTy) fits =
    subst
      (λ T -> Minimal
        (hasTy target (tmElQtr (renTm (raiseRen rho) l) (tmClass (renTm rho a))) T))
      (sym (renSingleSubstTy rho (tmClass a) L))
      (minEQtr dL' dp' dA' dBranchTy' dl' dWkA' coh' dTy')
    where
    da' = minRen da fits
    dA' = minRen dA fits
    fitsA = renFitsKeep fits dA'
    dL' = minRen dL (renFitsKeep fits (minFQtr dA'))
    dp' = minIQtr da'
    dBranchTyRen = minRen dBranchTy fitsA
    dBranchTy' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renQtrBranchTy rho L)
        dBranchTyRen
    dlRen = minRen dl fitsA
    dl' =
      subst
        (λ T -> Minimal (hasTy _ _ T))
        (renQtrBranchTy rho L)
        dlRen
    dWkARen = minRen dWkA fitsA
    dWkA' =
      subst
        (λ T -> Minimal (isType (renTy rho A ∷ target) T))
        (renTyKeepWk1 rho A)
        dWkARen
    fitsCoh = renFitsKeep fitsA dWkARen
    coh' = minRenQtrCoherence (minRen coh fitsCoh)
    dTyRen = minRen dTy fits
    dTy' =
      subst
        (λ T -> Minimal (isType target T))
        (renSingleSubstTy rho (tmClass a) L)
        dTyRen

  minRenTmEqTy : {gamma target : Ctx} {rho : Ren} {t u : RawTerm} {A : RawType}
    -> Minimal (termEq gamma t u A)
    -> RenFits target gamma rho
    -> Minimal (isType target (renTy rho A))
  minRenTmEqTy (minReflTm d) fits =
    minRenTmTy d fits
  minRenTmEqTy (minSymTm _ _ dA) fits =
    minRen dA fits
  minRenTmEqTy (minTransTm d _) fits =
    minRenTmEqTy d fits
  minRenTmEqTy (minConvEq _ dAB) fits =
    minRenTyEqRight dAB fits
  minRenTmEqTy (minCTop d) fits =
    minFTop (renFitsTargetWF fits)
  minRenTmEqTy (minISigmaEq _ _ dA dB) fits =
    minFSigma dA' dB'
    where
    dA' = minRen dA fits
    dB' = minRen dB (renFitsKeep fits dA')
  minRenTmEqTy (minESigmaEq _ _ _ _ _ dTy) fits =
    minRen dTy fits
  minRenTmEqTy (minCSigma _ _ _ _ _ dTy) fits =
    minRen dTy fits
  minRenTmEqTy (minIEqEq d) fits =
    minFEq (minRenTmEqTy d fits) (minRenTmEqLeft d fits) (minRenTmEqLeft d fits)
  minRenTmEqTy (minEEqStar _ dA _ _) fits =
    minRen dA fits
  minRenTmEqTy (minCEq _ dA da db) fits =
    minFEq (minRen dA fits) (minRen da fits) (minRen db fits)
  minRenTmEqTy (minIQtrEq da _) fits =
    minFQtr (minRenTmTy da fits)
  minRenTmEqTy (minEQtrEq _ _ _ _ _ _ _ _ _ _ dTy) fits =
    minRen dTy fits
  minRenTmEqTy (minCQtr _ _ _ _ _ _ _ dTy) fits =
    minRen dTy fits

renJToEq : {target : Ctx} {rho tau : Ren}
  -> ((n : ℕ) -> applyRen rho n ≡ applyRen tau n)
  -> (J : JForm)
  -> renJTo target rho J ≡ renJTo target tau J
renJToEq h (isType _ A) =
  cong (isType _) (renTyEq h A)
renJToEq h (typeEq _ A B) =
  cong₂ (typeEq _) (renTyEq h A) (renTyEq h B)
renJToEq h (hasTy _ t A) =
  cong₂ (hasTy _) (renTmEq h t) (renTyEq h A)
renJToEq h (termEq _ t u A) =
  cong₃ (termEq _) (renTmEq h t) (renTmEq h u) (renTyEq h A)

minWeaken : (delta : Ctx) {J : JForm}
  -> Minimal J
  -> MinCtxWF (delta ++ ctxOf J)
  -> Minimal (renJTo (delta ++ ctxOf J) (addRen (length delta)) J)
minWeaken delta {J = J} d wf with renFitsWeakenTo delta wf
... | renFitsTo rho fits rhoShift =
  subst Minimal (renJToEq rhoShift J) (minRen d fits)

minWeakenTy : {gamma delta : Ctx} {A : RawType}
  -> Minimal (isType gamma A)
  -> MinCtxWF (delta ++ gamma)
  -> Minimal (isType (delta ++ gamma) (wkTyBy (length delta) A))
minWeakenTy {delta = delta} d wf =
  minWeaken delta d wf

minWeakenTyEq : {gamma delta : Ctx} {A B : RawType}
  -> Minimal (typeEq gamma A B)
  -> MinCtxWF (delta ++ gamma)
  -> Minimal
       (typeEq (delta ++ gamma)
         (wkTyBy (length delta) A)
         (wkTyBy (length delta) B))
minWeakenTyEq {delta = delta} d wf =
  minWeaken delta d wf

minWeakenTm : {gamma delta : Ctx} {t : RawTerm} {A : RawType}
  -> Minimal (hasTy gamma t A)
  -> MinCtxWF (delta ++ gamma)
  -> Minimal
       (hasTy (delta ++ gamma)
         (wkTmBy (length delta) t)
         (wkTyBy (length delta) A))
minWeakenTm {delta = delta} d wf =
  minWeaken delta d wf

minWeakenTmEq : {gamma delta : Ctx} {t u : RawTerm} {A : RawType}
  -> Minimal (termEq gamma t u A)
  -> MinCtxWF (delta ++ gamma)
  -> Minimal
       (termEq (delta ++ gamma)
         (wkTmBy (length delta) t)
         (wkTmBy (length delta) u)
         (wkTyBy (length delta) A))
minWeakenTmEq {delta = delta} d wf =
  minWeaken delta d wf

minWeakenFitsOne : {gamma delta : Ctx} {sigma : Subst} {B : RawType}
  -> MinFitsSubst gamma delta sigma
  -> MinCtxWF (B ∷ gamma)
  -> MinFitsSubst (B ∷ gamma) delta (renSub sucRen sigma)
minWeakenFitsOne (minFitsNil _) wf =
  minFitsNil wf
minWeakenFitsOne {B = B} (minFitsCons {sigma = sigma} {A = A} fits dt) wf =
  minFitsCons
    (minWeakenFitsOne fits wf)
    (subst
      (λ T -> Minimal (hasTy _ _ T))
      (renTySub sucRen sigma A)
      (minWeakenTm {delta = B ∷ []} dt wf))

liftMinFits : {gamma delta : Ctx} {sigma : Subst} {A : RawType}
  -> MinFitsSubst gamma delta sigma
  -> Minimal (isType gamma (subTy sigma A))
  -> MinFitsSubst (subTy sigma A ∷ gamma) (A ∷ delta) (liftSubst sigma)
liftMinFits {gamma = gamma} {sigma = sigma} {A = A} fits dA =
  minFitsCons
    (minWeakenFitsOne fits (minWfCons (minFitsSubstCtxWF fits) dA))
    dVar
  where
  wf : MinCtxWF (subTy sigma A ∷ gamma)
  wf = minWfCons (minFitsSubstCtxWF fits) dA

  dVarWk : Minimal
    (hasTy (subTy sigma A ∷ gamma)
      (var zero)
      (wkTyBy 1 (subTy sigma A)))
  dVarWk =
    minVarStar {delta = []} wf dA

  dVar : Minimal
    (hasTy (subTy sigma A ∷ gamma)
      (var zero)
      (subTy (renSub sucRen sigma) A))
  dVar =
    subst
      (λ T -> Minimal (hasTy (subTy sigma A ∷ gamma) (var zero) T))
      (renTySub sucRen sigma A)
      dVarWk

minWeakenFitsEqOne : {gamma delta : Ctx} {sigma tau : Subst} {B : RawType}
  -> MinFitsEqSubst gamma delta sigma tau
  -> MinCtxWF (B ∷ gamma)
  -> MinFitsEqSubst (B ∷ gamma) delta (renSub sucRen sigma) (renSub sucRen tau)
minWeakenFitsEqOne (minFitsEqNil _) wf =
  minFitsEqNil wf
minWeakenFitsEqOne {B = B} (minFitsEqCons {sigma = sigma} {tau = tau} {A = A} fits dtu dRight dRightS) wf =
  minFitsEqCons
    (minWeakenFitsEqOne fits wf)
    (subst
      (λ T -> Minimal (termEq _ _ _ T))
      (renTySub sucRen sigma A)
      (minWeakenTmEq {delta = B ∷ []} dtu wf))
    (subst
      (λ T -> Minimal (hasTy _ _ T))
      (renTySub sucRen tau A)
      (minWeakenTm {delta = B ∷ []} dRight wf))
    (subst
      (λ T -> Minimal (hasTy _ _ T))
      (renTySub sucRen sigma A)
      (minWeakenTm {delta = B ∷ []} dRightS wf))

liftMinFitsEq : {gamma delta : Ctx} {sigma tau : Subst} {A : RawType}
  -> MinFitsEqSubst gamma delta sigma tau
  -> Minimal (isType gamma (subTy sigma A))
  -> Minimal (typeEq gamma (subTy sigma A) (subTy tau A))
  -> MinFitsEqSubst (subTy sigma A ∷ gamma) (A ∷ delta) (liftSubst sigma) (liftSubst tau)
liftMinFitsEq {gamma = gamma} {sigma = sigma} {tau = tau} {A = A} fits dA dAeq =
  minFitsEqCons
    (minWeakenFitsEqOne fits wf)
    (minReflTm dVar)
    dVarTau
    dVar
  where
  wf : MinCtxWF (subTy sigma A ∷ gamma)
  wf = minWfCons (minFitsEqSubstCtxWF fits) dA

  dVarWk : Minimal
    (hasTy (subTy sigma A ∷ gamma)
      (var zero)
      (wkTyBy 1 (subTy sigma A)))
  dVarWk =
    minVarStar {delta = []} wf dA

  dVar : Minimal
    (hasTy (subTy sigma A ∷ gamma)
      (var zero)
      (subTy (renSub sucRen sigma) A))
  dVar =
    subst
      (λ T -> Minimal (hasTy (subTy sigma A ∷ gamma) (var zero) T))
      (renTySub sucRen sigma A)
      dVarWk

  dVarTau : Minimal
    (hasTy (subTy sigma A ∷ gamma)
      (var zero)
      (subTy (renSub sucRen tau) A))
  dVarTau =
    subst
      (λ T -> Minimal (hasTy (subTy sigma A ∷ gamma) (var zero) T))
      (renTySub sucRen tau A)
      (minConv dVarWk (minWeakenTyEq {delta = subTy sigma A ∷ []} dAeq wf))
