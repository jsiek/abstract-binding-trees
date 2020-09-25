{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties
open import Structures
open import GSubst
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var

module GenericSubstitution where

module _ where

  _≊_ : ∀{ℓ₁ ℓ₂}{V₁ : Set ℓ₁}{V₂ : Set ℓ₂}
     {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
     {{_ : Relatable V₁ V₂}}
     → GSubst V₁ → GSubst V₂ → Set (ℓ₁ ⊔ ℓ₂)
  σ₁ ≊ σ₂ = ∀ (x : Var) → σ₁ x ≈ σ₂ x                

  inc-≊ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
            {{_ : Relatable V₁ V₂}} {σ₁}{σ₂}
     → σ₁ ≊ σ₂ → ⟰ σ₁ ≊ ⟰ σ₂
  inc-≊ {σ₁ = σ₁}{σ₂} σ₁≊σ₂ x = shift≈ (σ₁≊σ₂ x)

  ext-≊ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
           {{_ : Relatable V₁ V₂}}
      {σ₁ σ₂} → σ₁ ≊ σ₂ → ext σ₁ ≊ ext σ₂
  ext-≊ {σ₁ = σ₁} {σ₂} σ₁≊σ₂ zero = var→val≈ 0
  ext-≊ {σ₁ = σ₁} {σ₂} σ₁≊σ₂ (suc x) = shift≈ (σ₁≊σ₂ x)

  lookup∼ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
      {{_ : Relatable V₁ V₂}} {σ₁ σ₂}
     → (x : Var) → σ₁ ≊ σ₂ → σ₁ x ≈ σ₂ x
  lookup∼ x σ₁≊σ₂ = σ₁≊σ₂ x
  
module GSubstPred {ℓ}{V : Set ℓ}{I : Set} (S : Shiftable V)
  (_⊢v_⦂_ : List I → V → I → Set) where
  instance _ : Shiftable V ; _ = S
  
  _⦂_⇒_ : GSubst V → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v σ x ⦂ A
  
module Composition (Op : Set) (sig : Op → List Sig)   where
  open import AbstractBindingTree Op sig
  open import Map Op sig

  record ComposableProps {ℓ}(V₁ V₂ V₃ : Set ℓ)
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}}
       : Set ℓ
    where
    field var→val₂₃ : ∀ (x : Var)
             → var→val{ℓ}{V₃} x ≡ val₂₃ (var→val{ℓ}{V₂} x)
          quote-val₂₃ : ∀ (v₂ : V₂) → “ val₂₃ v₂ ” ≡ “ v₂ ”
          val₂₃-shift : ∀ (v₂ : V₂)
             → val₂₃ (⇑{ℓ}{V₂} v₂) ≡ ⇑{ℓ}{V₃} (val₂₃ v₂)
          quote-var→val₁ : ∀ x → “ var→val{ℓ}{V₁} x ” ≡ ` x
          quote-map : ∀ (σ₂ : GSubst V₂) (v₁ : V₁)
             → “ ⌈ σ₂ ⌉ v₁ ” ≡ map σ₂ “ v₁ ”
  

  open ComposableProps {{...}}

  map-sub-⟅·⟆ : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ}
      {{S₁ : Shiftable V₁}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{E₂ : Shiftable V₂}} {{E₃ : Shiftable V₃}}
      {{_ : Composable V₁ V₂ V₃}} {{_ : ComposableProps V₁ V₂ V₃}}
     {x : Var} (σ : GSubst V₂)
     → (map-sub val₂₃ σ) x ≡ val₂₃ (σ x)
  map-sub-⟅·⟆ {x = x} σ = refl

  drop-seq : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}} {{_ : ComposableProps V₁ V₂ V₃}}
      k (σ₁ : GSubst V₁) (σ₂ : GSubst V₂)
      → drop k (σ₁ ⨟ σ₂) ≡ (drop k σ₁ ⨟ σ₂)
  drop-seq k σ₁ σ₂ = extensionality λ x → refl

  map-sub-inc : ∀{ℓ} {V₁ V₂ V₃ : Set ℓ}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{C : Composable V₁ V₂ V₃}} {{CP : ComposableProps V₁ V₂ V₃}}
      (σ₂ : GSubst V₂)
      → map-sub val₂₃ (⟰ σ₂) ≡  ⟰ (map-sub val₂₃ σ₂)
  map-sub-inc {{C = C}} σ = extensionality G
      where
      G : ∀ x → map-sub (Composable.val₂₃ C) (⟰ σ) x
          ≡  ⟰ (map-sub (Composable.val₂₃ C) σ) x
      G x rewrite val₂₃-shift (σ x) = refl

  compose-sub : ∀{ℓ} {V₁ V₂ V₃ : Set ℓ}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}} {{_ : ComposableProps V₁ V₂ V₃}}
      → (σ₁ : GSubst V₁) (σ₂ : GSubst V₂) (x : Var)
      → “ (σ₁ ⨟ σ₂) x ” ≡ map σ₂ “ σ₁ x ”
  compose-sub σ₁ σ₂ x rewrite quote-map σ₂ (σ₁ x) = refl
  
