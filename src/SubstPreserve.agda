{-# OPTIONS --without-K #-}
import ABTPredicate
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax)
    renaming (_,_ to ⟨_,_⟩ )
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
  (𝑉 : List I → Var → I → I → Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set)
  (𝑉-refl : ∀ {Γ x A} → Γ ∋ x ⦂ A → 𝑉 Γ x A A)
  (𝑉-trans : ∀{x y A B C Γ₁ Γ₂} → 𝑉 Γ₁ x A B → 𝑉 Γ₂ y B C → 𝑉 Γ₁ x A C)
  (𝑉-suc : ∀{x A B C Δ} → 𝑉 Δ x A B → 𝑉 (C ∷ Δ) (suc x) A B)
  (𝑉-⊢ : ∀{x M A B Γ Δ} → 𝑉 Γ x A B
     → ABTPredicate._⊢_⦂_ Op sig 𝑉 𝑃 Δ M A
     → ABTPredicate._⊢_⦂_ Op sig 𝑉 𝑃 Δ M B)
  where

open import AbstractBindingTree Op sig
open Renaming.WithOpSig Op sig

module _ where
  open import MapPreserve Op sig I 𝑉 𝑃
  open import ABTPredicate Op sig 𝑉 𝑃 

  private
    _⊢v_⦂_ : List I → Var → I → Set
    Γ ⊢v x ⦂ B = Σ[ A ∈ I ] Γ ∋ x ⦂ A × 𝑉 Γ x A B

    quote-v : ∀ {Γ : List I} {x : Var} {A : I} → Γ ⊢v x ⦂ A → Γ ⊢ ` x ⦂ A
    quote-v ⟨ B , ⟨ ∋x , Vx ⟩ ⟩ = var-p ∋x Vx

    instance
      _ : MapPreservable Var
      _ = record { _⊢v_⦂_ = _⊢v_⦂_
              ; ⊢v-var→val0 = λ {A}{Δ} → ⟨ A , ⟨ refl , 𝑉-refl refl ⟩ ⟩
              ; shift-⊢v = λ { ⟨ A , ⟨ ∋x , Vx ⟩ ⟩ → ⟨ A , ⟨ ∋x , 𝑉-suc Vx ⟩ ⟩ }
              ; quote-⊢v = λ { ⟨ B , ⟨ ∋x , Vx ⟩ ⟩ → var-p ∋x Vx }
              ; 𝑉-⊢v = λ { {x}{x'}{A}{B} Vx ⟨ C , ⟨ ∋x , Vx' ⟩ ⟩ →
                         ⟨ C , ⟨ ∋x , 𝑉-trans Vx' Vx ⟩ ⟩ } }

  preserve-rename : ∀{Γ Δ : List I}{ρ : Rename}{A : I} (M : ABT)
     → Γ ⊢ M ⦂ A → ρ ⦂ Γ ⇒ Δ → Δ ⊢ rename ρ M ⦂ A
  preserve-rename = preserve-map

open import MapPreserve Op sig I 𝑉 𝑃
open import ABTPredicate Op sig 𝑉 𝑃 

private
  instance
    _ : MapPreservable ABT
    _ = record { _⊢v_⦂_ = _⊢_⦂_
          ; ⊢v-var→val0 = var-p refl (𝑉-refl refl)
          ; shift-⊢v = λ {A}{B}{Γ}{M} ⊢M →
                  preserve-rename M ⊢M λ {x}{C} ∋x → ⟨ C , ⟨ ∋x , 𝑉-refl ∋x ⟩ ⟩
          ; quote-⊢v = λ ⊢v⦂ → ⊢v⦂
          ; 𝑉-⊢v = λ {x}{M}{A}{B} Vx ⊢M⦂ → 𝑉-⊢ Vx ⊢M⦂
          }

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
        λ { {0}{A} refl → ⊢M ; {suc x}{A} ∋x → var-p ∋x (𝑉-refl ∋x) }
