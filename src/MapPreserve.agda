{-# OPTIONS --without-K #-}
{---------------------------

  Preservation of a predicate

      Let "I" be the kind for type-like things.

      A : I
      Γ Δ : List I

  preserve-map : ∀{M σ Γ Δ A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢ map-abt σ M ⦂ A

 ---------------------------}

import ABTPredicate
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax)
    renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (_∘_)
import Substitution
open import Structures
open import GSubst
open import GenericSubstitution
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Sig
open import Var

module MapPreserve (Op : Set) (sig : Op → List Sig)
  (I : Set)
  (𝑉 : List I → Var → I → I → Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set)
  where

open import AbstractBindingTree Op sig
open import Map Op sig

record MapPreservable (V : Set) {{_ : Quotable V}} {{_ : Shiftable V}} : Set₁
  where
  field _⊢v_⦂_ : List I → V → I → Set
        ⊢v-var→val0 : ∀{A Δ} → (A ∷ Δ) ⊢v var→val 0 ⦂ A
        shift-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v ⇑ v ⦂ A
        𝑉-⊢v : ∀{x v A B Γ Δ} → 𝑉 Γ x A B → Δ ⊢v v ⦂ A → Δ ⊢v v ⦂ B
  open ABTPredicate Op sig 𝑉 𝑃 public
  field quote-⊢v : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A

open MapPreservable {{...}}

_⦂_⇒_ : ∀{V : Set}
   {{_ : Quotable V}} {{_ : Shiftable V}} {{_ : MapPreservable V}}
   → GSubst V → List I → List I → Set
_⦂_⇒_ {V} σ Γ Δ = ∀{x : Var} {A : I} → Γ ∋ x ⦂ A  →  Δ ⊢v σ x ⦂ A

preserve-map : ∀ {V : Set}{Γ Δ : List I}{σ : GSubst V}{A : I}
   {{_ : Quotable V}} {{_ : Shiftable V}} {{_ : MapPreservable V}}
   (M : ABT)
   → Γ ⊢ M ⦂ A
   → σ ⦂ Γ ⇒ Δ
   → Δ ⊢ map σ M ⦂ A
preserve-map {V}{Γ}{Δ}{σ}{A}(` x) (var-p {A = B} ∋x 𝑉x) σ⦂ =
    quote-⊢v (𝑉-⊢v 𝑉x (σ⦂ ∋x))
preserve-map {V} (op ⦅ args ⦆) (op-p ⊢args Pop) σ⦂ =
    op-p (pres-args ⊢args σ⦂) Pop
    where
    map-pres-ext : ∀ {σ : GSubst V}{Γ Δ : List I}{A : I}
       → σ ⦂ Γ ⇒ Δ  →  ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
    map-pres-ext {σ = σ} σ⦂ {zero} refl = ⊢v-var→val0 
    map-pres-ext {σ = σ} σ⦂ {suc x} ∋x = shift-⊢v (σ⦂ ∋x)
   
    pres-arg : ∀{b Γ Δ}{arg : Arg b}{A σ Bs}
       → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A → σ ⦂ Γ ⇒ Δ
       → b ∣ Δ ∣ Bs ⊢ₐ map-arg σ {b} arg ⦂ A
    pres-args : ∀{bs Γ Δ}{args : Args bs}{As σ Bss}
       → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As → σ ⦂ Γ ⇒ Δ
       → bs ∣ Δ ∣ Bss ⊢₊ map-args σ {bs} args ⦂ As
    pres-arg {b} {arg = ast M} (ast-p ⊢M) σ⦂ =
        ast-p (preserve-map M ⊢M σ⦂)
    pres-arg {ν b}{Γ}{Δ}{bind arg}{σ = σ} (bind-p {B = B}{A = A} ⊢arg) σ⦂ =
        bind-p (pres-arg ⊢arg (λ{x}{A} → map-pres-ext{σ}{Γ}{Δ} σ⦂ {x}{A}))
    pres-arg {b} {arg = clear arg} (clear-p ⊢arg) σ⦂ = clear-p ⊢arg
    pres-args {[]} {args = nil} nil-p σ⦂ = nil-p
    pres-args {b ∷ bs} {args = cons arg args} (cons-p ⊢arg ⊢args) σ⦂ =
        cons-p (pres-arg ⊢arg σ⦂) (pres-args ⊢args σ⦂)

