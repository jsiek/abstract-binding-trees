open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties
open import experimental.Environment
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var

module experimental.GenericSubstitution where

postulate
  extensionality : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁ }{B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

open Shiftable {{...}}

infixr 6 _•_

{-
data GSubst {ℓ : Level} : (V : Set ℓ) → Set ℓ where
  ↑ : (k : ℕ) → ∀{V : Set ℓ} → GSubst {ℓ} V
  _•_ : ∀{V} → V → GSubst V → GSubst V
-}

GSubst : {ℓ : Level} (V : Set ℓ) → Set ℓ
GSubst V = Var → V

↑ : (k : ℕ) → ∀{ℓ}{V : Set ℓ}{{_ : Shiftable V}} → GSubst {ℓ} V
↑ k x = var→val (k + x)

_•_ : ∀{ℓ}{V : Set ℓ}{{_ : Shiftable V}} → V → GSubst V → GSubst V
(v • σ) 0 = v
(v • σ) (suc x) = σ x

id : ∀ {ℓ}{V : Set ℓ}{{_ : Shiftable V}} → GSubst V
id = ↑ 0

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
  
⟰ : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → GSubst V → GSubst V
⟰ σ x = ⇑ (σ x)

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

{- obsolete, use • instead -}
_,_ : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → GSubst V → V → GSubst V
(σ , v) = v • ⟰ σ

ext : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} → GSubst V → GSubst V
ext σ = (var→val 0) • ⟰ σ

ext-cong : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} {σ₁ σ₂ : GSubst V}
  → ((x : ℕ) → σ₁ x ≡ σ₂ x)
  → (x : ℕ) → ext σ₁ x ≡ ext σ₂ x
ext-cong {σ₁ = σ₁} {σ₂} f zero = refl
ext-cong {σ₁ = σ₁} {σ₂} f (suc x) rewrite f x = refl

drop-ext : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}}
   → (k : Var) (σ : GSubst V)
   → drop (suc k) (ext σ) ≡ ⟰ (drop k σ)
drop-ext k σ = refl


{-

data Shift {ℓ}{V : Set ℓ} {{_ : Shiftable V}} : ℕ → GSubst V → Set ℓ where
  shift-up : ∀{k} → Shift k (↑ k)
  shift-• : ∀{k σ v} → Shift (suc k) σ → v ≡ shifts k (var→val 0)
     → Shift k (v • σ)

inc-Shift : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} {k}{σ : GSubst V}
   → Shift k σ → Shift (suc k) (⟰ σ)
inc-Shift shift-up = shift-up
inc-Shift (shift-• kσ refl) = shift-• (inc-Shift kσ) refl

shifts0 : ∀{ℓ}{V : Set ℓ} {{S : Shiftable V}}
   → (k : ℕ) → shifts k (var→val{ℓ}{V} 0) ≡ var→val k
shifts0 zero = refl
shifts0{ℓ}{V} (suc k) rewrite shifts0{ℓ}{V} k = sym (var→val-suc-shift)

Shift-var : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}}
   → (σ : GSubst V) (k : ℕ)
   → (x : Var) → Shift{ℓ}{V} k σ → ⟅ σ ⟆ x ≡ var→val (k + x)
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

inc-ShftAbv : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} {k c k′ σ}
  → ShftAbv k c k′ σ
  → ShftAbv (suc k) c (suc k′) (⟰ σ)
inc-ShftAbv {k = k} {.0} {k′} {σ} (sha-0 σk) = sha-0 (inc-Shift σk)
inc-ShftAbv{ℓ}{V}{k = k} {.(suc _)} {k′} {.(_ • _)} (sha-suc σkc refl) =
  sha-suc (inc-ShftAbv{ℓ}{V} σkc) refl

ext-ShftAbv : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} {k c σ}
   → ShftAbv k c 0 σ
   → ShftAbv k (suc c) 0 (ext σ)
ext-ShftAbv {k = k} {.0} {σ} (sha-0 σk) =
    sha-suc (sha-0 (inc-Shift σk)) refl
ext-ShftAbv {ℓ}{V} {k = k} {.(suc _)} {.(_ • _)} (sha-suc σk refl) =
    sha-suc (sha-suc (inc-ShftAbv{ℓ}{V} σk) refl) refl

ShftAbv→Shift : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} {k c σ}
   → ShftAbv k c k σ → Shift k σ
ShftAbv→Shift {k = k} {.0} (sha-0 σk) = σk
ShftAbv→Shift{ℓ}{V} {k = k} {suc c} {v • σ} (sha-suc σkc refl) =
    shift-• (ShftAbv→Shift{ℓ}{V}{k = suc k}{c}{σ} σkc) refl

record Relatable {ℓ} (V₁ V₂ : Set ℓ)
    {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}} : Set (lsuc ℓ) where
    field _∼_ : V₁ → V₂ → Set
          var→val∼ : ∀ x → var→val{ℓ}{V₁} x ∼ var→val{ℓ}{V₂} x
          shift∼ : ∀{v₁ v₂}→ v₁ ∼ v₂ → ⇑ v₁ ∼ ⇑ v₂

module _ where

  open Relatable {{...}}

  data _≊_ {ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
                  {{_ : Relatable V₁ V₂}} : GSubst V₁ → GSubst V₂ → Set ℓ where
     r-up : ∀{k} → (↑ k) ≊ (↑ k)
     r-cons : ∀{v₁ σ₁ v₂ σ₂}
        → v₁ ∼ v₂  →   σ₁ ≊ σ₂
        → (v₁ • σ₁) ≊ (v₂ • σ₂)

  inc-≊ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
            {{_ : Relatable V₁ V₂}} {σ₁ σ₂}
     → σ₁ ≊ σ₂ → ⟰ σ₁ ≊ ⟰ σ₂
  inc-≊ {σ₁ = (↑ _)} {.(↑ _)} r-up = r-up
  inc-≊ {σ₁ = .(_ • _)} {.(_ • _)} (r-cons v₁~v₂ σ₁≊σ₂) =
      r-cons (shift∼ v₁~v₂ ) (inc-≊ σ₁≊σ₂)

  ext-≊ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
           {{_ : Relatable V₁ V₂}}
      {σ₁ σ₂} → σ₁ ≊ σ₂ → ext σ₁ ≊ ext σ₂
  ext-≊ {σ₁}{σ₂} σ₁≊σ₂ = r-cons (var→val∼ 0) (inc-≊ σ₁≊σ₂)

  lookup∼ : ∀{ℓ}{V₁ V₂ : Set ℓ}{{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
      {{_ : Relatable V₁ V₂}} {σ₁ σ₂}
     → (x : Var) → σ₁ ≊ σ₂ → (⟅ σ₁ ⟆ x) ∼ (⟅ σ₂ ⟆ x)
  lookup∼ x (r-up{k}) = var→val∼ (k + x)
  lookup∼ zero (r-cons v₁∼v₂ σ₁≊σ₂) = v₁∼v₂
  lookup∼ (suc x) (r-cons v₁∼v₂ σ₁≊σ₂) = lookup∼ x σ₁≊σ₂


module GSubstPred {ℓ}{V : Set ℓ}{I : Set} (S : Shiftable V)
  (_⊢v_⦂_ : List I → V → I → Set) where
  instance _ : Shiftable V ; _ = S
  
  _⦂_⇒_ : GSubst V → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v ⟅ σ ⟆ x ⦂ A
  

record Composable {ℓ} (V₁ V₂ V₃ : Set ℓ) : Set ℓ where
   field ⌈_⌉ : GSubst V₂ → V₁ → V₃
         val₂₃ : V₂ → V₃ 

open Composable {{...}}

infixr 5 _⨟_

abstract
  _⨟_ : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ} {{_ : Composable V₁ V₂ V₃}}
     → GSubst V₁ → GSubst V₂ → GSubst V₃
  ↑ k ⨟ σ₂ = map-sub val₂₃ (drop k σ₂)
  (v₁ • σ₁) ⨟ σ₂ = ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)

abstract
  up-seq : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ} {{_ : Composable V₁ V₂ V₃}}
     k (σ₂ : GSubst V₂)
     → ↑ k ⨟ σ₂ ≡ map-sub val₂₃ (drop k σ₂)
  up-seq k σ₂ = refl

  cons-seq : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ} {{_ : Composable V₁ V₂ V₃}}
     v₁ (σ₁ : GSubst V₁) (σ₂ : GSubst V₂)
     → (v₁ • σ₁) ⨟ σ₂ ≡ ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)
  cons-seq  v₁ σ₁ σ₂ = refl


module Composition (Op : Set) (sig : Op → List ℕ)   where
  open import AbstractBindingTree Op sig
  open import Map Op sig
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
      {{E₂ : Env (GSubst V₂) V₂}} {{E₃ : Env (GSubst V₃) V₃}}
      {{_ : Composable V₁ V₂ V₃}}
      {{_ : ComposableProps V₁ V₂ V₃}}
     {x : Var} (σ : GSubst V₂)
     → ⟅ map-sub val₂₃ σ ⟆ x ≡ val₂₃ (⟅ σ ⟆ x)
  map-sub-⟅·⟆ {x = x} (↑ k) = var→val₂₃ (k + x)
  map-sub-⟅·⟆ {x = zero} (v₂ • σ) = refl
  map-sub-⟅·⟆ {{E₂ = E₂}}{{E₃ = E₃}} {x = suc x} (v₂ • σ) =
      map-sub-⟅·⟆ {{E₂ = E₂}}{{E₃ = E₃}} {x = x} σ

  drop-seq : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ}
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

  map-sub-inc : ∀{ℓ} {V₁ V₂ V₃ : Set ℓ}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}} {{_ : ComposableProps V₁ V₂ V₃}}
      (σ₂ : GSubst V₂)
      → map-sub val₂₃ (⟰ σ₂) ≡  ⟰ (map-sub val₂₃ σ₂)
  map-sub-inc (↑ k) = refl
  map-sub-inc (v₂ • σ₂) = cong₂ _•_ (val₂₃-shift v₂) (map-sub-inc σ₂)

  compose-sub : ∀{ℓ} {V₁ V₂ V₃ : Set ℓ}
      {{S₁ : Shiftable V₁}} {{S₂ : Shiftable V₂}} {{S₃ : Shiftable V₃}}
      {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
      {{_ : Composable V₁ V₂ V₃}}
      {{_ : ComposableProps V₁ V₂ V₃}}
      → (σ₁ : GSubst V₁) (σ₂ : GSubst V₂) (x : Var)
      → “ ⟅ σ₁ ⨟ σ₂ ⟆ x ” ≡ (map σ₂ “ ⟅ σ₁ ⟆ x ”)
      
  compose-sub (↑ k) σ₂ x = begin
    “ ⟅ ↑ k ⨟ σ₂ ⟆ x ”               ≡⟨ cong (λ □ → “ ⟅ □ ⟆ x ”)  (up-seq _ _) ⟩
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
-}
