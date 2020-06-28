open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n; _≤?_)
open import Data.Nat.Properties using (+-comm; +-suc; ≤-pred)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)

module Syntax where

open import Var public

open import Substitution public

module OpSig (Op : Set) (sig : Op → List ℕ)  where

  open import Environment
  open Env {{...}}
  open ABTOps Op sig public

  open import WellScoped Op sig public
  
  {----------------------------------------------------------------------------
   Free variables
  ----------------------------------------------------------------------------}

  FV? : ABT → Var → Bool
  FV-arg? : ∀{b} → Arg b → Var → Bool
  FV-args? : ∀{bs} → Args bs → Var → Bool
  FV? (` x) y
      with x ≟ y
  ... | yes xy = true
  ... | no xy = false
  FV? (op ⦅ As ⦆) y = FV-args? As y
  FV-arg? (ast M) y = FV? M y
  FV-arg? (bind A) y = FV-arg? A (suc y)
  FV-args? nil y = false
  FV-args? (cons A As) y = FV-arg? A y ∨ FV-args? As y

  {----------------------------------------------------------------------------
   Convert (Var → Var) Function to Renaming
  ----------------------------------------------------------------------------}

  private
    make-ren : (Var → Var) → ℕ → ℕ → Rename
    make-ren ρ x zero = ↑ 0
    make-ren ρ x (suc m) = ρ x • make-ren ρ (suc x) m

    ⟅make-ren⟆ : ∀{m}{x}{i}{ρ}
       → x < m
       → ⟅ make-ren ρ i m ⟆ x ≡ ρ (x + i)
    ⟅make-ren⟆ {suc m} {zero} {i} {ρ} x<m = refl
    ⟅make-ren⟆ {suc m} {suc x} {i} {ρ} x<m
        with ⟅make-ren⟆ {m} {x} {suc i} {ρ} (≤-pred x<m)
    ... | IH rewrite +-suc x i = 
        IH
     
  make-renaming : (Var → Var) → ℕ → Rename
  make-renaming ρ Γ = make-ren ρ 0 Γ

  ⟅make-renaming⟆ : ∀{Γ}{x}{ρ}
     → x < Γ
     → ⟅ make-renaming ρ Γ ⟆ x ≡ ρ x
  ⟅make-renaming⟆ {Γ}{x}{ρ} x<Γ
      with ⟅make-ren⟆ {i = 0}{ρ} x<Γ
  ... | mr rewrite +-comm x 0 = mr

