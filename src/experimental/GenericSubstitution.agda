open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties
open import experimental.Environment
open import experimental.GSubst
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var

module experimental.GenericSubstitution where

open Shiftable {{...}}

map-sub : ∀{ℓ}{V W : Set ℓ} → (V → W) → GSubst V → GSubst W
map-sub f σ x = f (σ x)

map-sub-id : ∀{ℓ}{V : Set ℓ} (σ : GSubst V) → map-sub (λ x → x) σ ≡ σ
map-sub-id σ = refl

drop : ∀{ℓ}{V : Set ℓ} → (k : ℕ) → GSubst V → GSubst V
drop k σ x = σ (k + x)

map-sub-drop : ∀{ℓ} {V W : Set ℓ} σ f k
   → map-sub {ℓ}{V}{W} f (drop k σ) ≡ drop k (map-sub f σ)
map-sub-drop σ f k = refl

drop-0 : ∀ {ℓ}{V : Set ℓ} σ → drop {ℓ}{V} 0 σ ≡ σ
drop-0 σ = refl

drop-drop : ∀ {ℓ}{V} k k' σ → drop {ℓ} {V} (k + k') σ ≡ drop k (drop k' σ)
drop-drop k k' σ = extensionality G
  where
  G : (x : Var) → drop (k + k') σ x ≡ drop k (drop k' σ) x
  G x rewrite +-comm k k' | +-assoc k' k x = refl
  

shifts : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → ℕ → V → V
shifts zero v = v
shifts (suc k) v = ⇑ (shifts k v) 

drop-inc : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}}
   → (k : ℕ) (σ : GSubst V) → drop k (⟰ σ) ≡ ⟰ (drop k σ)
drop-inc k σ = refl

Z-shift : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}}
   → (x : Var) → (var→val{ℓ}{V} 0 • ↑ 1) x ≡ var→val{ℓ}{V} x
Z-shift 0 = refl
Z-shift (suc x) = refl

ext-cong : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} {σ₁ σ₂ : GSubst V}
  → ((x : ℕ) → σ₁ x ≡ σ₂ x)
  → (x : ℕ) → ext σ₁ x ≡ ext σ₂ x
ext-cong {σ₁ = σ₁} {σ₂} f zero = refl
ext-cong {σ₁ = σ₁} {σ₂} f (suc x) rewrite f x = refl

drop-ext : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}}
   → (k : Var) (σ : GSubst V)
   → drop (suc k) (ext σ) ≡ ⟰ (drop k σ)
drop-ext k σ = refl

Shift : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → ℕ → GSubst V → Set ℓ
Shift k σ = ∀ x → σ x ≡ shifts k (var→val x)

inc-Shift : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} {k}{σ : GSubst V}
   → Shift k σ → Shift (suc k) (⟰ σ)
inc-Shift {ℓ} {V} {k} {σ} shk x rewrite shk x = refl

shifts-var→val : ∀{ℓ}{V : Set ℓ} {{S : Shiftable V}}
   → (k x : ℕ) → shifts k (var→val{ℓ}{V} x) ≡ var→val (k + x)
shifts-var→val zero x = refl
shifts-var→val{ℓ}{V}{{S}} (suc k) x rewrite shifts-var→val{ℓ}{V} k x
    | var→val-suc-shift {{S}} {x = k + x} = refl

Shift-var : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}}
   → (σ : GSubst V) (k : ℕ)
   → (x : Var) → Shift{ℓ}{V} k σ → σ x ≡ var→val (k + x)
Shift-var σ zero x sft rewrite sft x = refl
Shift-var {{S}} σ (suc k) x sft rewrite sft x
    | var→val-suc-shift {{S}} {x = k + x}
    | shifts-var→val {{S}} k x = refl

record Relatable {ℓ} (V₁ V₂ : Set ℓ)
    {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}} : Set (lsuc ℓ) where
    field _∼_ : V₁ → V₂ → Set
          var→val∼ : ∀ x → var→val{ℓ}{V₁} x ∼ var→val{ℓ}{V₂} x
          shift∼ : ∀{v₁ v₂}→ v₁ ∼ v₂ → ⇑ v₁ ∼ ⇑ v₂


module _ where

  open Relatable {{...}}

  _≊_ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
                  {{_ : Relatable V₁ V₂}} → GSubst V₁ → GSubst V₂ → Set
  σ₁ ≊ σ₂ = ∀ x → σ₁ x ∼ σ₂ x                

  inc-≊ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
            {{_ : Relatable V₁ V₂}} {σ₁}{σ₂}
     → σ₁ ≊ σ₂ → ⟰ σ₁ ≊ ⟰ σ₂
  inc-≊ {σ₁ = σ₁}{σ₂} σ₁≊σ₂ x = shift∼ (σ₁≊σ₂ x)

  ext-≊ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
           {{_ : Relatable V₁ V₂}}
      {σ₁ σ₂} → σ₁ ≊ σ₂ → ext σ₁ ≊ ext σ₂
  ext-≊ {σ₁ = σ₁} {σ₂} σ₁≊σ₂ zero = var→val∼ 0
  ext-≊ {σ₁ = σ₁} {σ₂} σ₁≊σ₂ (suc x) = shift∼ (σ₁≊σ₂ x)

  lookup∼ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
      {{_ : Relatable V₁ V₂}} {σ₁ σ₂}
     → (x : Var) → σ₁ ≊ σ₂ → σ₁ x ∼ σ₂ x
  lookup∼ x σ₁≊σ₂ = σ₁≊σ₂ x
  
module GSubstPred {ℓ}{V : Set ℓ}{I : Set} (S : Shiftable V)
  (_⊢v_⦂_ : List I → V → I → Set) where
  instance _ : Shiftable V ; _ = S
  
  _⦂_⇒_ : GSubst V → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v σ x ⦂ A
  
record Composable {ℓ} (V₁ V₂ V₃ : Set ℓ){{_ : Shiftable V₁}} : Set ℓ where
   field ⌈_⌉ : GSubst V₂ → V₁ → V₃
         val₂₃ : V₂ → V₃
         ⌈⌉-var→val : ∀ σ x → ⌈ σ ⌉ (var→val x) ≡ val₂₃ (σ x)

open Composable {{...}}

infixr 5 _⨟_

_⨟_ : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ} {{_ : Shiftable V₁}} {{_ : Composable V₁ V₂ V₃}}
     → GSubst V₁ → GSubst V₂ → GSubst V₃
(σ₁ ⨟ σ₂) x = ⌈ σ₂ ⌉ (σ₁ x)
  
up-seq : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ}{{S : Shiftable V₁}}
   {{C : Composable V₁ V₂ V₃}}
   k (σ₂ : GSubst V₂)
   → ↑ k ⨟ σ₂ ≡ map-sub val₂₃ (drop k σ₂)
up-seq {{S}}{{C}} k σ₂ = extensionality G
    where
    G : (x : Var) → (↑ k ⨟ σ₂) x ≡ map-sub (Composable.val₂₃ C) (drop k σ₂) x
    G x rewrite ⌈⌉-var→val σ₂ (k + x) = refl

cons-seq : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ} {{_ : Shiftable V₁}} {{_ : Shiftable V₃}}
   {{C : Composable V₁ V₂ V₃}}
   v₁ (σ₁ : GSubst V₁) (σ₂ : GSubst V₂)
   → (v₁ • σ₁) ⨟ σ₂ ≡ ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)
cons-seq {{C = C}} v₁ σ₁ σ₂ = extensionality G
   where
   G :   (x : Var) → (v₁ • σ₁ ⨟ σ₂) x ≡ (Composable.⌈ C ⌉ σ₂ v₁ • (σ₁ ⨟ σ₂)) x
   G zero = refl
   G (suc x) = refl

module Composition (Op : Set) (sig : Op → List ℕ)   where
  open import AbstractBindingTree Op sig
  open import experimental.Map Op sig
  open Quotable {{...}}

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
      {{_ : Composable V₁ V₂ V₃}}
      {{_ : ComposableProps V₁ V₂ V₃}}
     {x : Var} (σ : GSubst V₂)
     → (map-sub val₂₃ σ) x ≡ val₂₃ (σ x)
  map-sub-⟅·⟆ {x = x} σ = refl

  drop-seq : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}}
      {{_ : ComposableProps V₁ V₂ V₃}}
      k σ₁ σ₂
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
      {{_ : Composable V₁ V₂ V₃}}
      {{_ : ComposableProps V₁ V₂ V₃}}
      → (σ₁ : GSubst V₁) (σ₂ : GSubst V₂) (x : Var)
      → “ (σ₁ ⨟ σ₂) x ” ≡ map σ₂ “ σ₁ x ”
  compose-sub σ₁ σ₂ x rewrite quote-map σ₂ (σ₁ x) = refl
  
