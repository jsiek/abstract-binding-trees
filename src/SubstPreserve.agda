open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Renaming
open import Sig
open import Substitution
open import Var

module SubstPreserve (Op : Set) (sig : Op → List Sig)
  (I : Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set)
  where

private
  𝑉 : List I → Var → I → Set
  𝑉 = λ Γ x A → ⊤

open import AbstractBindingTree Op sig
open import MapPreserve Op sig I 𝑉 𝑃
open import ABTPredicate Op sig 𝑉 𝑃 

open Renaming.WithOpSig Op sig

private
  quote-v : ∀ {Γ : List I} {x : Var} {A : I}
     → Γ ∋ x ⦂ A
     → Γ ⊢ ` x ⦂ A
  quote-v ∋x = var-p ∋x tt

  instance
    _ : MapPreservable Var
    _ = record { _⊢v_⦂_ = _∋_⦂_ ; ⊢v0 = refl
               ; shift-⊢v = λ x → x ; quote-⊢v = λ ∋x → var-p ∋x tt }

preserve-rename : ∀{Γ Δ : List I}{ρ : Rename}{A : I} (M : ABT)
   → Γ ⊢ M ⦂ A → ρ ⦂ Γ ⇒ Δ → Δ ⊢ rename ρ M ⦂ A
preserve-rename = preserve-map

private
  instance
    _ : MapPreservable ABT
    _ = record { _⊢v_⦂_ = _⊢_⦂_ ; ⊢v0 = var-p refl tt
          ; shift-⊢v = λ {A}{B}{Γ}{M} ⊢M → preserve-rename M ⊢M (λ z → z)
          ; quote-⊢v = λ ⊢v⦂ → ⊢v⦂ }

open import Substitution
open Substitution.ABTOps Op sig

preserve-subst : ∀{Γ Δ : List I}{σ : Subst}{A : I} (M : ABT)
 → Γ ⊢ M ⦂ A → σ ⦂ Γ ⇒ Δ → Δ ⊢ ⟪ σ ⟫ M ⦂ A
preserve-subst = preserve-map

preserve-substitution : ∀{Γ : List I}{A B : I} (N M : ABT)
  → (A ∷ Γ) ⊢ N ⦂ B
  → Γ ⊢ M ⦂ A
  → Γ ⊢ N [ M ] ⦂ B
preserve-substitution {Γ}{A} N M ⊢N ⊢M =
  preserve-subst {σ = M • id} N ⊢N
    (λ { {zero} refl → ⊢M ; {suc x} ∋x → var-p ∋x tt })

