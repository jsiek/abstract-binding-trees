open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties
open import Environment
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import Agda.Primitive using (Level; lzero; lsuc)

module GenericSubstitution where

open Shiftable {{...}}
open Env {{...}}

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

lookup : ∀{V : Set} {{_ : Shiftable V}} → GSubst V → Var → V
lookup (↑ k) x = var→val (k + x)
lookup (y • σ) 0 = y
lookup (y • σ) (suc x) = lookup σ x

inc : ∀ {V : Set} {{_ : Shiftable V}} → GSubst V → GSubst V
inc (↑ k) = ↑ (suc k)
inc (v • ρ) = ⇑ v • inc ρ

inc-shift : ∀{V : Set} {{S : Shiftable V}} (ρ : GSubst V) (x : Var)
   → lookup (inc ρ) x ≡ ⇑ (lookup ρ x)
inc-shift (↑ k) x rewrite +-comm k x = var→val-suc-shift
inc-shift (y • ρ) zero = refl
inc-shift (y • ρ) (suc x) = inc-shift ρ x

instance
  GSubst-is-Env : ∀{V} {{S : Shiftable V}} → Env (GSubst V) V
  GSubst-is-Env {V}{{S}} = record { ⟅_⟆ = lookup
      ; _,_ = λ ρ v → v • inc ρ ; ⟰ = inc ; lookup-0 = λ ρ v → refl
      ; lookup-suc = λ ρ v x → inc-shift ρ x
      ; lookup-shift = λ ρ x → inc-shift ρ x }

drop-add : ∀{V} {{_ : Shiftable V}} k (σ : GSubst V) (x : Var)
   → ⟅ drop k σ ⟆ x ≡ ⟅ σ ⟆ (k + x)
drop-add k (↑ k') x rewrite +-comm k k' | +-assoc k' k x = refl
drop-add zero (v • σ) x = refl
drop-add (suc k) (v • σ) x = drop-add k σ x

shifts : ∀{V} {{_ : Shiftable V}} → ℕ → V → V
shifts zero v = v
shifts (suc k) v = ⇑ (shifts k v) 

drop-inc : ∀{V} {{_ : Shiftable V}}
   → (k : ℕ) (σ : GSubst V) → drop k (inc σ) ≡ inc (drop k σ)
drop-inc k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
drop-inc zero (v • σ) = refl
drop-inc (suc k) (v • σ) = drop-inc k σ

Z-shift : ∀{V} {{_ : Shiftable V}}
   → (x : Var) → ⟅ var→val{V} 0 • ↑ 1 ⟆ x ≡ var→val{V} x
Z-shift 0 = refl
Z-shift (suc x) = refl

ext-cong : ∀{V} {{_ : Shiftable V}} {σ₁ σ₂ : GSubst V}
  → ((x : ℕ) → ⟅ σ₁ ⟆ x ≡ ⟅ σ₂ ⟆ x)
  → (x : ℕ) → ⟅ ext σ₁ ⟆ x ≡ ⟅ ext σ₂ ⟆ x
ext-cong f zero = refl
ext-cong {σ₁ = σ₁} {σ₂} f (suc x)
    rewrite inc-shift σ₁ x | inc-shift σ₂ x | f x = refl

drop-ext : ∀{V} {{_ : Shiftable V}}
   → (k : Var) (ρ : GSubst V)
   → drop (suc k) (ext ρ) ≡ inc (drop k ρ)
drop-ext k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
drop-ext zero (x • ρ) = refl
drop-ext (suc k) (x • ρ) = drop-inc k ρ

data Shift {V} {{_ : Shiftable V}} : ℕ → GSubst V → Set where
  shift-up : ∀{k} → Shift k (↑ k)
  shift-• : ∀{k σ v} → Shift (suc k) σ → v ≡ shifts k (var→val 0)
     → Shift k (v • σ)

inc-Shift : ∀{V} {{_ : Shiftable V}} {k}{σ : GSubst V}
   → Shift k σ → Shift (suc k) (inc σ)
inc-Shift shift-up = shift-up
inc-Shift (shift-• kσ refl) = shift-• (inc-Shift kσ) refl

shifts0 : ∀{V} {{S : Shiftable V}}
   → (k : ℕ) → shifts k (var→val{V} 0) ≡ var→val{V} k
shifts0 zero = refl
shifts0 {V} (suc k) rewrite shifts0{V} k = sym var→val-suc-shift

Shift-var : ∀{V} {{_ : Shiftable V}}
   → (σ : GSubst V) (k : ℕ)
   → (x : Var) → Shift{V} k σ → ⟅ σ ⟆ x ≡ var→val (k + x)
Shift-var .(↑ k) k x shift-up = refl
Shift-var (v • _) k zero (shift-• σk refl)
    rewrite +-comm k 0 = shifts0 k
Shift-var (v • σ) k (suc x) (shift-• σk refl) rewrite +-suc k x =
    Shift-var σ (suc k) x σk

data ShftAbv {V} {{_ : Shiftable V}} : ℕ → ℕ → ℕ → GSubst V → Set where
  sha-0 : ∀{k k′ σ}
     → Shift k σ
     → ShftAbv k 0 k′ σ
  sha-suc : ∀{k c k′ σ v}
     → ShftAbv (suc k) c (suc k′) σ
     → v ≡ shifts k′ (var→val 0)
     → ShftAbv k (suc c) k′ (v • σ)

inc-ShftAbv : ∀{V} {{_ : Shiftable V}} {k c k′ σ}
  → ShftAbv k c k′ σ
  → ShftAbv (suc k) c (suc k′) (inc σ)
inc-ShftAbv {k = k} {.0} {k′} {σ} (sha-0 σk) = sha-0 (inc-Shift σk)
inc-ShftAbv {k = k} {.(suc _)} {k′} {.(_ • _)} (sha-suc σkc refl) =
  sha-suc (inc-ShftAbv σkc) refl

ext-ShftAbv : ∀{V} {{_ : Shiftable V}} {k c σ}
   → ShftAbv k c 0 σ
   → ShftAbv k (suc c) 0 (ext σ)
ext-ShftAbv {k = k} {.0} {σ} (sha-0 σk) =
    sha-suc (sha-0 (inc-Shift σk)) refl
ext-ShftAbv {k = k} {.(suc _)} {.(_ • _)} (sha-suc σk refl) =
    sha-suc (sha-suc (inc-ShftAbv σk) refl) refl

ShftAbv→Shift : ∀{V} {{_ : Shiftable V}} {k c σ}
   → ShftAbv{V} k c k σ → Shift{V} k σ
ShftAbv→Shift {k = k} {.0} (sha-0 σk) = σk
ShftAbv→Shift {k = k} {suc c} {v • σ} (sha-suc σkc refl) =
    shift-• (ShftAbv→Shift{k = suc k}{c}{σ} σkc) refl

record Relatable (V₁ V₂ : Set)
    {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}} : Set₁ where
    field _∼_ : V₁ → V₂ → Set
          var→val∼ : ∀ x → var→val{V₁} x ∼ var→val{V₂} x
          shift∼ : ∀{v₁ v₂}→ v₁ ∼ v₂ → ⇑ v₁ ∼ ⇑ v₂

module _ where

  open Relatable {{...}}

  data _≊_ {V₁ V₂}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
                  {{_ : Relatable V₁ V₂}} : GSubst V₁ → GSubst V₂ → Set where
     r-up : ∀{k} → (↑ k) ≊ (↑ k)
     r-cons : ∀{v₁ σ₁ v₂ σ₂}
        → v₁ ∼ v₂  →   σ₁ ≊ σ₂
        → (v₁ • σ₁) ≊ (v₂ • σ₂)

  inc-≊ : ∀{V₁ V₂}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
            {{_ : Relatable V₁ V₂}} {σ₁ σ₂}
     → σ₁ ≊ σ₂ → inc σ₁ ≊ inc σ₂
  inc-≊ {σ₁ = (↑ _)} {.(↑ _)} r-up = r-up
  inc-≊ {σ₁ = .(_ • _)} {.(_ • _)} (r-cons v₁~v₂ σ₁≊σ₂) =
      r-cons (shift∼ v₁~v₂ ) (inc-≊ σ₁≊σ₂)

  ext-≊ : ∀{V₁ V₂}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}{{_ : Relatable V₁ V₂}}
      {σ₁ σ₂} → σ₁ ≊ σ₂ → ext σ₁ ≊ ext σ₂
  ext-≊ {σ₁}{σ₂} σ₁≊σ₂ = r-cons (var→val∼ 0) (inc-≊ σ₁≊σ₂)

  lookup∼ : ∀{V₁ V₂}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
      {{_ : Relatable V₁ V₂}} {σ₁ σ₂}
     → (x : Var) → σ₁ ≊ σ₂ → (⟅ σ₁ ⟆ x) ∼ (⟅ σ₂ ⟆ x)
  lookup∼ x (r-up{k}) = var→val∼ (k + x)
  lookup∼ zero (r-cons v₁∼v₂ σ₁≊σ₂) = v₁∼v₂
  lookup∼ (suc x) (r-cons v₁∼v₂ σ₁≊σ₂) = lookup∼ x σ₁≊σ₂


module GSubstPred {V I : Set} (S : Shiftable V)
  (_⊢v_⦂_ : List I → V → I → Set) where
  instance _ : Shiftable V ; _ = S
  
  _⦂_⇒_ : GSubst V → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v ⟅ σ ⟆ x ⦂ A
  

record Composable  (V₁ V₂ V₃ : Set) : Set where
   field ⌈_⌉ : GSubst V₂ → V₁ → V₃
         val₂₃ : V₂ → V₃ 

open Composable {{...}}

infixr 5 _⨟_

abstract
  _⨟_ : ∀{V₁ V₂ V₃ : Set} {{_ : Composable V₁ V₂ V₃}}
     → GSubst V₁ → GSubst V₂ → GSubst V₃
  ↑ k ⨟ σ₂ = map-sub val₂₃ (drop k σ₂)
  (v₁ • σ₁) ⨟ σ₂ = ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)

abstract
  up-seq : ∀{V₁ V₂ V₃ : Set} {{_ : Composable V₁ V₂ V₃}}
     k (σ₂ : GSubst V₂)
     → ↑ k ⨟ σ₂ ≡ map-sub val₂₃ (drop k σ₂)
  up-seq k σ₂ = refl

  cons-seq : ∀{V₁ V₂ V₃ : Set} {{_ : Composable V₁ V₂ V₃}}
     v₁ (σ₁ : GSubst V₁) (σ₂ : GSubst V₂)
     → (v₁ • σ₁) ⨟ σ₂ ≡ ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)
  cons-seq  v₁ σ₁ σ₂ = refl


module Composition (Op : Set) (sig : Op → List ℕ)   where
  open import AbstractBindingTree Op sig
  open import Map2 Op sig
  open Quotable {{...}}

  record ComposableProps (V₁ V₂ V₃ : Set)
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}}
       : Set
    where
    field var→val₂₃ : ∀ (x : Var)
             → var→val{V₃} x ≡ val₂₃ (var→val{V₂} x)
          quote-val₂₃ : ∀ (v₂ : V₂) → “ val₂₃ v₂ ” ≡ “ v₂ ”
          val₂₃-shift : ∀ (v₂ : V₂)
             → val₂₃ (⇑{V₂} v₂) ≡ ⇑{V₃} (val₂₃ v₂)
          quote-var→val₁ : ∀ x → “ var→val{V₁} x ” ≡ ` x
          quote-map : ∀ (σ₂ : GSubst V₂) (v₁ : V₁)
             → “ ⌈ σ₂ ⌉ v₁ ” ≡ map σ₂ “ v₁ ”

  open ComposableProps {{...}}

  map-sub-⟅·⟆ : ∀{V₁ V₂ V₃}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{E₂ : Env (GSubst V₂) V₂}} {{E₃ : Env (GSubst V₃) V₃}}
      {{_ : Composable V₁ V₂ V₃}}
      {{_ : ComposableProps V₁ V₂ V₃}}
     {x : Var} (σ : GSubst V₂)
     → ⟅ map-sub val₂₃ σ ⟆ x ≡ val₂₃ (⟅ σ ⟆ x)
  map-sub-⟅·⟆ {x = x} (↑ k) = var→val₂₃ (k + x)
  map-sub-⟅·⟆ {x = zero} (v₂ • σ) = refl
  map-sub-⟅·⟆ {{E₂ = E₂}}{{E₃ = E₃}} {x = suc x} (v₂ • σ) =
      map-sub-⟅·⟆ {{E₂ = E₂}}{{E₃ = E₃}} {x = x} σ

  drop-seq : ∀ {V₁ V₂ V₃}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}}
      {{_ : ComposableProps V₁ V₂ V₃}}
      k σ₁ σ₂
      → drop k (σ₁ ⨟ σ₂) ≡ (drop k σ₁ ⨟ σ₂)
  drop-seq k (↑ k₁) σ₂ = begin
    drop k (↑ k₁ ⨟ σ₂)                    ≡⟨ cong (drop k) (up-seq _ _) ⟩
    drop k (map-sub val₂₃ (drop k₁ σ₂))
                                   ≡⟨  sym (map-sub-drop (drop k₁ σ₂) val₂₃ k) ⟩
    map-sub val₂₃ (drop k (drop k₁ σ₂))
                            ≡⟨  cong (map-sub val₂₃) (sym (drop-drop k k₁ σ₂)) ⟩
    map-sub val₂₃ (drop (k + k₁) σ₂)      ≡⟨ sym (up-seq _ σ₂) ⟩
    ↑ (k + k₁) ⨟ σ₂                       ∎
  drop-seq zero (x • σ₁) σ₂ rewrite cons-seq x σ₁ σ₂ = refl
  drop-seq (suc k) (x • σ₁) σ₂ rewrite cons-seq x σ₁ σ₂
      | drop-seq k σ₁ σ₂ = refl

  map-sub-inc : ∀ {V₁ V₂ V₃}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}} {{_ : ComposableProps V₁ V₂ V₃}}
      (σ₂ : GSubst V₂)
      → map-sub val₂₃ (inc σ₂) ≡  inc (map-sub val₂₃ σ₂)
  map-sub-inc (↑ k) = refl
  map-sub-inc (v₂ • σ₂) = cong₂ _•_ (val₂₃-shift v₂) (map-sub-inc σ₂)

  compose-sub : ∀ {V₁ V₂ V₃}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}}
      {{_ : ComposableProps V₁ V₂ V₃}}
      → (σ₁ : GSubst V₁) (σ₂ : GSubst V₂) (x : Var)
      → “ ⟅ σ₁ ⨟ σ₂ ⟆ x ” ≡ (map σ₂ “ ⟅ σ₁ ⟆ x ”)
      
  compose-sub (↑ k) σ₂ x = begin
    “ ⟅ ↑ k ⨟ σ₂ ⟆ x ”                ≡⟨ cong (λ □ → “ ⟅ □ ⟆ x ”)  (up-seq _ _) ⟩
    “ ⟅ map-sub val₂₃ (drop k σ₂) ⟆ x ”
                         ≡⟨ cong (λ □ → “ ⟅ □ ⟆ x ”) (map-sub-drop σ₂ val₂₃ k) ⟩
    “ ⟅ drop k (map-sub val₂₃ σ₂) ⟆ x ”
                              ≡⟨ cong “_” (drop-add k (map-sub val₂₃ σ₂) x) ⟩
    “ ⟅ map-sub val₂₃ σ₂ ⟆ (k + x) ”            ≡⟨ cong “_” (map-sub-⟅·⟆ σ₂) ⟩
    “ val₂₃ (⟅ σ₂ ⟆ (k + x)) ”                 ≡⟨ quote-val₂₃ (⟅ σ₂ ⟆ (k + x)) ⟩
    “ ⟅ σ₂ ⟆ (k + x) ”                                                       ≡⟨⟩
    map σ₂ (` (k + x))
                         ≡⟨ cong (map σ₂) (sym (quote-var→val₁ (k + x)) ) ⟩
    map σ₂ “ ⟅ ↑ k ⟆ x ”
    ∎
  compose-sub (v₁ • σ₁) σ₂ zero rewrite sym (quote-map σ₂ v₁)
      | cons-seq v₁ σ₁ σ₂ = refl
  compose-sub (v₁ • σ₁) σ₂ (suc x) rewrite cons-seq v₁ σ₁ σ₂
      | compose-sub σ₁ σ₂ x = refl
