open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Environment
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning


module Map (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig

open Quotable {{...}}
open Env  {{...}}

map : ∀{E V} {{_ : Shiftable V}} {{_ : Env E V}} {{_ : Quotable V}}
   → E → ABT → ABT

map-arg : ∀{E V} {{_ : Shiftable V}} {{_ : Env E V}} {{_ : Quotable V}}
   → E → {b : ℕ} →  Arg b → Arg b
map-args : ∀{E V} {{_ : Shiftable V}} {{_ : Env E V}} {{_ : Quotable V}}
   → E → {bs : List ℕ} →  Args bs → Args bs
map σ (` x) = “ ⟅ σ ⟆ x ”
map {E}{V} σ (op ⦅ args ⦆) = op ⦅ map-args σ args ⦆
map-arg σ {zero} (ast M) = ast (map σ M)
map-arg σ {suc b} (bind M) = bind (map-arg (ext σ) M)
map-args σ {[]} nil = nil
map-args σ {b ∷ bs} (cons x args) = cons (map-arg σ x) (map-args σ args)

_∘_≈_ : ∀ {V₁}{E₁}{V₂}{E₂}{V₃}{E₃}
        {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}}
        {{M₁ : Env E₁ V₁}} {{M₂ : Env E₂ V₂}} {{M₃ : Env E₃ V₃}}
        {{Q₁ : Quotable V₁}}{{Q₂ : Quotable V₂}}{{Q₃ : Quotable V₃}}
        (σ₂ : E₂)(σ₁ : E₁)(σ₃ : E₃) → Set
_∘_≈_ {V₁}{E₁}{V₂}{E₂}{V₃}{E₃}{{M₁}}{{M₂}}{{M₃}} σ₂ σ₁ σ₃ =
  ∀ x → map σ₂ “ ⟅ σ₁ ⟆ x ” ≡ “ ⟅ σ₃ ⟆ x ”

map-map-fusion : ∀{V₁ E₁ V₂ E₂ V₃ E₃}
  {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}}
  {{_ : Env E₁ V₁}} {{_ : Env E₂ V₂}} {{_ : Env E₃ V₃}}
  {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
  {σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
   → (M : ABT)
   → σ₂ ∘ σ₁ ≈ σ₃
   → (∀{σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
      → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃)
   → map σ₂ (map σ₁ M) ≡ map σ₃ M
map-map-fusion (` x) σ₂∘σ₁≈σ₃ mf-ext = σ₂∘σ₁≈σ₃ x
map-map-fusion  (op ⦅ args ⦆) σ₂∘σ₁≈σ₃ mf-ext =
  cong (_⦅_⦆ op) (mmf-args args σ₂∘σ₁≈σ₃)
  where
  mmf-arg : ∀{σ₁ σ₂ σ₃ b} (arg : Arg b) → σ₂ ∘ σ₁ ≈ σ₃
     → map-arg σ₂ (map-arg σ₁ arg) ≡ map-arg σ₃ arg
  mmf-args : ∀{σ₁ σ₂ σ₃ bs} (args : Args bs) → σ₂ ∘ σ₁ ≈ σ₃
     → map-args σ₂ (map-args σ₁ args) ≡ map-args σ₃ args
  mmf-arg {b = zero} (ast M) σ₂∘σ₁≈σ₃ =
      cong ast (map-map-fusion M σ₂∘σ₁≈σ₃ mf-ext)
  mmf-arg {b = suc b} (bind arg) σ₂∘σ₁≈σ₃ =
      cong bind (mmf-arg arg (mf-ext σ₂∘σ₁≈σ₃))
  mmf-args {bs = []} nil σ₂∘σ₁≈σ₃ = refl
  mmf-args {bs = b ∷ bs} (cons arg args) σ₂∘σ₁≈σ₃ =
      cong₂ cons (mmf-arg arg σ₂∘σ₁≈σ₃) (mmf-args args σ₂∘σ₁≈σ₃)

_≈_ : ∀ {V₁}{E₁}{V₂}{E₂}
        {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}}
        {{_ : Env E₁ V₁}} {{_ : Env E₂ V₂}}
        {{_ : Quotable V₁}} {{_ : Quotable V₂}}
        (σ₂ : E₂)(σ₁ : E₁) → Set
_≈_ {V₁}{E₁}{V₂}{E₂}{{M₁}}{{M₂}} σ₁ σ₂ = ∀ x → “ ⟅ σ₁ ⟆ x ” ≡ “ ⟅ σ₂ ⟆ x ”

map-cong : ∀{V₁ E₁ V₂ E₂}
   {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}}  
   {{_ : Env E₁ V₁}} {{_ : Env E₂ V₂}} {{_ : Quotable V₁}} {{_ : Quotable V₂}}
   {σ₁ : E₁}{σ₂ : E₂}
   → (M : ABT)
   → σ₁ ≈ σ₂
   → (∀{σ₁ : E₁}{σ₂ : E₂} → σ₁ ≈ σ₂ → ext σ₁ ≈ ext σ₂)
   → map σ₁ M ≡ map σ₂ M
map-cong (` x) σ₁≈σ₂ mc-ext = σ₁≈σ₂ x
map-cong (op ⦅ args ⦆) σ₁≈σ₂ mc-ext = cong (_⦅_⦆ op) (mc-args args σ₁≈σ₂)
  where
  mc-arg : ∀{σ₁ σ₂ b} (arg : Arg b) → σ₁ ≈ σ₂
     → map-arg σ₁ arg ≡ map-arg σ₂ arg
  mc-args : ∀{σ₁ σ₂ bs} (args : Args bs) → σ₁ ≈ σ₂
     → map-args σ₁ args ≡ map-args σ₂ args
  mc-arg {b = zero} (ast M) σ₁≈σ₂ =
      cong ast (map-cong M σ₁≈σ₂ mc-ext)
  mc-arg {b = suc b} (bind arg) σ₁≈σ₂ =
      cong bind (mc-arg arg (mc-ext σ₁≈σ₂))
  mc-args {bs = []} nil σ₁≈σ₂ = refl
  mc-args {bs = b ∷ bs} (cons arg args) σ₁≈σ₂ =
      cong₂ cons (mc-arg arg σ₁≈σ₂) (mc-args args σ₁≈σ₂)
