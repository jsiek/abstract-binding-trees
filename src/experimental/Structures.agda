open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Var

module experimental.Structures where

record Shiftable {ℓ} (V : Set ℓ) : Set ℓ where
  field ⇑ : V → V
        var→val : Var → V
        var→val-suc-shift : ∀{x} → var→val (suc x) ≡ ⇑ (var→val x)

open Shiftable {{...}} public

instance
  Var-is-Shiftable : Shiftable Var
  Var-is-Shiftable = record { var→val = λ x → x ; ⇑ = suc
                            ; var→val-suc-shift = λ {x} → refl }


record Composable {ℓ} (V₁ V₂ V₃ : Set ℓ){{_ : Shiftable V₁}} : Set ℓ where
   field ⌈_⌉ : (Var → V₂) → V₁ → V₃
         val₂₃ : V₂ → V₃
         ⌈⌉-var→val : ∀ σ x → ⌈ σ ⌉ (var→val x) ≡ val₂₃ (σ x)

open Composable {{...}} public

instance
    Var³-Composable : Composable Var Var Var
    Var³-Composable = record { ⌈_⌉ = λ f x → f x ; val₂₃ = λ x → x
                     ; ⌈⌉-var→val = λ σ x → refl }

infixr 5 _⨟_

_⨟_ : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ} {{_ : Shiftable V₁}} {{_ : Composable V₁ V₂ V₃}}
     → (Var → V₁) → (Var → V₂) → (Var → V₃)
(σ₁ ⨟ σ₂) x = ⌈ σ₂ ⌉ (σ₁ x)

record Relatable {ℓ} (V₁ V₂ : Set ℓ)
    {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}} : Set (lsuc ℓ) where
    field _∼_ : V₁ → V₂ → Set
          var→val∼ : ∀ x → var→val{ℓ}{V₁} x ∼ var→val{ℓ}{V₂} x
          shift∼ : ∀{v₁ v₂}→ v₁ ∼ v₂ → ⇑ v₁ ∼ ⇑ v₂

open Relatable {{...}} public

record Renameable {ℓ} (V : Set ℓ) : Set ℓ where
  field ren : (Var → Var) → V → V

open Renameable {{...}} public

instance
  Var-Renameable : Renameable Var
  Var-Renameable = record { ren = λ f x → f x }

postulate
  extensionality : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁ }{B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

