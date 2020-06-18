open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Var
open import Agda.Primitive using (Level; lzero; lsuc)

module GenericSubstitution where

infixr 6 _•_

data GSubst {ℓ : Level} : (V : Set ℓ) → Set ℓ where
  ↑ : (k : ℕ) → ∀{V : Set ℓ} → GSubst {ℓ} V
  _•_ : ∀{V} → V → GSubst V → GSubst V

id : ∀ {ℓ}{V : Set ℓ} → GSubst V
id = ↑ 0

map-sub : ∀{V W : Set} → (V → W) → GSubst V → GSubst W
map-sub f (↑ k) = ↑ k
map-sub f (v • σ) = f v • map-sub f σ

map-sub-id : ∀{V} (σ : GSubst V) → map-sub (λ x → x) σ ≡ σ
map-sub-id (↑ k) = refl
map-sub-id (v • σ) = cong₂ _•_ refl (map-sub-id σ)

drop : ∀{ℓ}{V : Set ℓ} → (k : ℕ) → GSubst V → GSubst V
drop k (↑ k') = ↑ (k + k')
drop zero (v • σ) = v • σ
drop (suc k) (v • σ) = drop k σ

map-sub-drop : ∀ {V W} σ f k
   → map-sub {V}{W} f (drop k σ) ≡ drop k (map-sub f σ)
map-sub-drop (↑ k₁) f k = refl
map-sub-drop (v • σ) f zero = refl
map-sub-drop (v • σ) f (suc k) = map-sub-drop σ f k

drop-0 : ∀ {ℓ}{V : Set ℓ} σ → drop {ℓ}{V} 0 σ ≡ σ
drop-0 (↑ k) = refl
drop-0 (v • σ) = refl
  
drop-drop : ∀ {ℓ}{V} k k' σ → drop {ℓ} {V} (k + k') σ ≡ drop k (drop k' σ)
drop-drop k k' (↑ k₁) rewrite +-assoc k k' k₁ = refl
drop-drop zero k' (v • σ) rewrite drop-0 (drop k' (v • σ)) = refl
drop-drop (suc k) zero (v • σ) rewrite +-comm k 0 = refl
drop-drop (suc k) (suc k') (v • σ)
    with drop-drop (suc k) k' σ
... | IH rewrite +-comm k (suc k') | +-comm k k' = IH

record Shiftable (V : Set) : Set where
  field var→val : Var → V
        shift : V → V
        var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x)

module GenericSubst {V : Set} (S : Shiftable V) where
  open Shiftable S

  ⧼_⧽ : GSubst V → Var → V
  ⧼ ↑ k ⧽ x = var→val (k + x)
  ⧼ y • σ ⧽ 0 = y
  ⧼ y • σ ⧽ (suc x) = ⧼ σ ⧽ x

  g-inc : GSubst V → GSubst V
  g-inc (↑ k) = ↑ (suc k)
  g-inc (v • ρ) = shift v • g-inc ρ

  g-extend : V → GSubst V → GSubst V
  g-extend v σ = v • g-inc σ
  
  abstract
    g-ext : GSubst V → GSubst V
    g-ext σ = g-extend (var→val 0) σ

    g-ext-def : ∀ σ → g-ext σ ≡ g-extend (var→val 0) σ
    g-ext-def σ = refl

  shifts : ℕ → V → V
  shifts zero v = v
  shifts (suc k) v = shift (shifts k v) 

  g-drop-add : ∀ k σ x → ⧼ drop k σ ⧽ x ≡ ⧼ σ ⧽ (k + x)
  g-drop-add k (↑ k') x rewrite +-comm k k' | +-assoc k' k x = refl
  g-drop-add zero (v • σ) x = refl
  g-drop-add (suc k) (v • σ) x = g-drop-add k σ x

  g-drop-inc : ∀ k σ → drop k (g-inc σ) ≡ g-inc (drop k σ)
  g-drop-inc k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
  g-drop-inc zero (v • σ) = refl
  g-drop-inc (suc k) (v • σ) = g-drop-inc k σ

  g-Z-shift : ∀ x → ⧼ var→val 0 • ↑ 1 ⧽ x ≡ var→val x
  g-Z-shift 0 = refl
  g-Z-shift (suc x) = refl

  g-inc-shift : ∀ ρ x → ⧼ g-inc ρ ⧽ x ≡ shift (⧼ ρ ⧽ x)
  g-inc-shift (↑ k) x rewrite +-comm k x = var→val-suc-shift
  g-inc-shift (y • ρ) zero = refl
  g-inc-shift (y • ρ) (suc x) = g-inc-shift ρ x

  abstract 
   g-ext-cong : ∀ {σ₁ σ₂} → ((x : ℕ) → ⧼ σ₁ ⧽ x ≡ ⧼ σ₂ ⧽ x)
     → (x : ℕ) → ⧼ g-ext σ₁ ⧽ x ≡ ⧼ g-ext σ₂ ⧽ x
   g-ext-cong {σ₁} {σ₂} f zero = refl
   g-ext-cong {σ₁} {σ₂} f (suc x)
       rewrite g-inc-shift σ₁ x | g-inc-shift σ₂ x | f x = refl

   g-drop-ext : ∀ k ρ → drop (suc k) (g-ext ρ) ≡ g-inc (drop k ρ)
   g-drop-ext k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
   g-drop-ext zero (x • ρ) = refl
   g-drop-ext (suc k) (x • ρ) = g-drop-inc k ρ

  data Shift : ℕ → GSubst V → Set where
    shift-up : ∀{k} → Shift k (↑ k)
    shift-• : ∀{k σ v} → Shift (suc k) σ → v ≡ shifts k (var→val 0)
       → Shift k (v • σ)

  g-inc-Shift : ∀ {k σ} → Shift k σ → Shift (suc k) (g-inc σ)
  g-inc-Shift shift-up = shift-up
  g-inc-Shift (shift-• kσ refl) = shift-• (g-inc-Shift kσ) refl

  shifts0 : ∀ k → shifts k (var→val 0) ≡ var→val k
  shifts0 zero = refl
  shifts0 (suc k) rewrite shifts0 k | var→val-suc-shift {k} = refl

  g-Shift-var : ∀ {σ}{k} (x : Var) → Shift k σ → ⧼ σ ⧽ x ≡ var→val (k + x)
  g-Shift-var {.(↑ k)}{k} x shift-up = refl
  g-Shift-var {v • _}{k} zero (shift-• σk refl)
      rewrite +-comm k 0 = shifts0 k
  g-Shift-var {v • σ}{k} (suc x) (shift-• σk refl) rewrite +-suc k x =
      g-Shift-var {σ}{suc k} x σk

  data ShftAbv : ℕ → ℕ → ℕ → GSubst V → Set where
    sha-0 : ∀{k k′ σ}
       → Shift k σ
       → ShftAbv k 0 k′ σ
    sha-suc : ∀{k c k′ σ v}
       → ShftAbv (suc k) c (suc k′) σ
       → v ≡ shifts k′ (var→val 0)
       → ShftAbv k (suc c) k′ (v • σ)

  g-inc-ShftAbv : ∀{k c k′ σ}
     → ShftAbv k c k′ σ
     → ShftAbv (suc k) c (suc k′) (g-inc σ)
  g-inc-ShftAbv {k} {.0} {k′} {σ} (sha-0 σk) = sha-0 (g-inc-Shift σk)
  g-inc-ShftAbv {k} {.(suc _)} {k′} {.(_ • _)} (sha-suc σkc refl) =
     sha-suc (g-inc-ShftAbv σkc) refl

  abstract
   g-ext-ShftAbv : ∀ {k c σ}
      → ShftAbv k c 0 σ
      → ShftAbv k (suc c) 0 (g-ext σ)
   g-ext-ShftAbv {k} {.0} {σ} (sha-0 σk) = sha-suc (sha-0 (g-inc-Shift σk)) refl
   g-ext-ShftAbv {k} {.(suc _)} {.(_ • _)} (sha-suc σk refl) =
       sha-suc (sha-suc (g-inc-ShftAbv σk) refl) refl

  g-ShftAbv→Shift : ∀ {k c σ} → ShftAbv k c k σ → Shift k σ
  g-ShftAbv→Shift {k} {.0} (sha-0 σk) = σk
  g-ShftAbv→Shift {k} {suc c} {v • σ} (sha-suc σkc refl) =
      shift-• (g-ShftAbv→Shift{suc k}{c}{σ} σkc) refl

module Relate {V₁ : Set}{V₂ : Set}
    (S₁ : Shiftable V₁) (S₂ : Shiftable V₂)
    (_∼_ : V₁ → V₂ → Set)
    (var→val∼ : ∀ x → Shiftable.var→val S₁ x ∼ Shiftable.var→val S₂ x)
    (shift∼ : ∀{v₁ v₂}→ v₁ ∼ v₂ → Shiftable.shift S₁ v₁ ∼ Shiftable.shift S₂ v₂)
    where
    module G₁ = GenericSubst S₁
    module G₂ = GenericSubst S₂

    data _≊_ : GSubst V₁ → GSubst V₂ → Set where
       r-up : ∀{k} → (↑ k) ≊ (↑ k)
       r-cons : ∀{v₁ σ₁ v₂ σ₂}
          → v₁ ∼ v₂  →   σ₁ ≊ σ₂
          → (v₁ • σ₁) ≊ (v₂ • σ₂)

    g-inc-≊ : ∀ {σ₁ σ₂} → σ₁ ≊ σ₂ → G₁.g-inc σ₁ ≊ G₂.g-inc σ₂
    g-inc-≊ {.(↑ _)} {.(↑ _)} r-up = r-up
    g-inc-≊ {.(_ • _)} {.(_ • _)} (r-cons v₁~v₂ σ₁≊σ₂) =
        r-cons (shift∼ v₁~v₂ ) (g-inc-≊ σ₁≊σ₂)

    g-ext-≊ : ∀ {σ₁ σ₂} → σ₁ ≊ σ₂ → G₁.g-ext σ₁ ≊ G₂.g-ext σ₂
    g-ext-≊ {σ₁}{σ₂} σ₁≊σ₂ rewrite G₁.g-ext-def σ₁
        | G₂.g-ext-def σ₂ = r-cons (var→val∼ 0) (g-inc-≊ σ₁≊σ₂)

    g-lookup : ∀ {σ₁ σ₂} x → σ₁ ≊ σ₂ → G₁.⧼_⧽ σ₁ x ∼ G₂.⧼_⧽ σ₂ x
    g-lookup x (r-up{k}) = var→val∼ (k + x)
    g-lookup zero (r-cons v₁∼v₂ σ₁≊σ₂) = v₁∼v₂
    g-lookup (suc x) (r-cons v₁∼v₂ σ₁≊σ₂) = g-lookup x σ₁≊σ₂

module ComposeGSubst {V₁ V₂ V₃ : Set} 
   (⌈_⌉ : GSubst V₂ → V₁ → V₃)
   (val₂₃ : V₂ → V₃) where
  {- The following generalizes _⨟ᵣ_ and _⨟_, as well as compositions
     of renaming and subtitution. -}
  infixr 5 _⨟_

  abstract
    _⨟_ : GSubst V₁ → GSubst V₂ → GSubst V₃
    ↑ k ⨟ σ₂ = map-sub val₂₃ (drop k σ₂)
    (v₁ • σ₁) ⨟ σ₂ = ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)

  abstract
    up-seq : ∀ k σ₂ → ↑ k ⨟ σ₂ ≡ map-sub val₂₃ (drop k σ₂)
    up-seq k σ₂ = refl

    cons-seq : ∀ v₁ σ₁ σ₂ → (v₁ • σ₁) ⨟ σ₂ ≡ ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)
    cons-seq  v₁ σ₁ σ₂ = refl

module GSubstPred {V I : Set} (S : Shiftable V)
  (_⊢v_⦂_ : List I → V → I → Set) where
  open GenericSubst S
  
  _⦂_⇒_ : GSubst V → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v ⧼ σ ⧽ x ⦂ A
  
