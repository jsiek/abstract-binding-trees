{-# OPTIONS --without-K  #-}
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-assoc)
open import Structures
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Var

module GSubst where

GSubst : ∀{ℓ} (V : Set ℓ) → Set ℓ
GSubst V = Var → V

↑ : (k : ℕ) → ∀{ℓ}{V : Set ℓ}{{_ : Shiftable V}} → GSubst {ℓ} V
↑ k x = var→val (k + x)

infixr 6 _•_
_•_ : ∀{ℓ}{V : Set ℓ}{{_ : Shiftable V}} → V → GSubst V → GSubst V
(v • σ) 0 = v
(v • σ) (suc x) = σ x

⟰ : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → GSubst V → GSubst V
⟰ σ x = ⇑ (σ x)

id : ∀ {ℓ}{V : Set ℓ}{{_ : Shiftable V}} → GSubst V
id = ↑ 0

ext : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → GSubst V → GSubst V
ext σ = (var→val 0) • ⟰ σ

{- obsolete, use • instead -}
_,_ : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → GSubst V → V → GSubst V
(σ , v) = v • ⟰ σ

drop : ∀{ℓ}{V : Set ℓ} → (k : ℕ) → GSubst V → GSubst V
drop k σ x = σ (k + x)

map-sub : ∀{ℓ}{V W : Set ℓ} → (V → W) → GSubst V → GSubst W
map-sub f σ x = f (σ x)

map-sub-id : ∀{ℓ}{V : Set ℓ} (σ : GSubst V) → map-sub (λ x → x) σ ≡ σ
map-sub-id σ = refl

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

