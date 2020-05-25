open import Syntax
open import Generic

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)

module WellScoped (Op : Set) (sig : Op → List ℕ) where

  open OpSig Op sig hiding (rename)
  open Rename Op sig
  
  𝒫 : Op → List ⊤ → ⊤ → Set
  𝒫 op Γ A = ⊤

  open ABTPred Op sig 𝒫
  open RenamePres Op sig 𝒫
  
  len : ∀{bs} → Args bs → ℕ
  len nil = 0
  len (cons _ args) = suc (len args)

  mk-list : ℕ → List ⊤
  mk-list 0 = []
  mk-list (suc n) = tt ∷ mk-list n

  WS : ℕ → ABT → Set
  WS n M = (mk-list n) ⊢ M ⦂ tt
  
  WS-Rename : ℕ → Rename → ℕ → Set
  WS-Rename Γ ρ Δ = ρ ⦂ (mk-list Γ) ⇒ (mk-list Δ)

  WS-rename : ∀ {Γ Δ ρ M} → WS-Rename Γ ρ Δ → WS Γ M → WS Δ (rename ρ M)
  WS-rename {Γ}{Δ}{ρ}{M} ΓρΔ WSM = preserve {M}{ρ}{mk-list Γ}{mk-list Δ} WSM ΓρΔ

