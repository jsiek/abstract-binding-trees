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
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Environment
open import Function using (_∘_)
import Substitution
open import GenericSubstitution
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var

module MapPreserve (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Map Op sig
open Shiftable {{...}}
open Quotable {{...}}
open Env {{...}}

record MapPreservable (V I E : Set){{_ : Quotable V}} {{_ : Env E V}} : Set₁ where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        ⊢v0 : ∀{B Δ} → (B ∷ Δ) ⊢v var→val 0 ⦂ B
        shift-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v ⇑ v ⦂ A
  open ABTPredicate Op sig 𝑉 𝑃 public
  field quote-⊢v : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A

open MapPreservable {{...}}

_⦂_⇒_ : ∀{V I E : Set}
   {{_ : Quotable V}} {{_ : Env E V}} {{_ : MapPreservable V I E}}
   → E → List I → List I → Set
_⦂_⇒_ {V}{I}{E} σ Γ Δ = ∀{x : Var} {A : I} → Γ ∋ x ⦂ A  →  Δ ⊢v ⟅ σ ⟆ x ⦂ A

preserve-map : ∀ {E V I : Set}{Γ Δ : List I}{σ : E}{A : I}
   {{_ : Quotable V}} {{_ : Env E V}} {{_ : MapPreservable V I E}}
   (M : ABT)
   → Γ ⊢ M ⦂ A
   → σ ⦂ Γ ⇒ Δ
   → Δ ⊢ map σ M ⦂ A
preserve-map (` x) (var-p ∋x 𝑉x) σ⦂ = quote-⊢v (σ⦂ ∋x)
preserve-map {E}{V}{I} (op ⦅ args ⦆) (op-p ⊢args Pop) σ⦂ =
    op-p (pres-args ⊢args σ⦂) Pop
    where
    map-pres-ext : ∀ {σ : E}{Γ Δ : List I}{A : I}
       → σ ⦂ Γ ⇒ Δ  →  ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
    map-pres-ext {σ = σ} σ⦂ {zero} refl rewrite lookup-0 σ (var→val 0) = ⊢v0
    map-pres-ext {σ = σ} σ⦂ {suc x} ∋x rewrite lookup-suc σ (var→val 0) x =
      shift-⊢v (σ⦂ ∋x)
   
    pres-arg : ∀{b Γ Δ}{arg : Arg b}{A σ Bs}
       → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A → σ ⦂ Γ ⇒ Δ
       → b ∣ Δ ∣ Bs ⊢ₐ map-arg σ {b} arg ⦂ A
    pres-args : ∀{bs Γ Δ}{args : Args bs}{As σ Bss}
       → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As → σ ⦂ Γ ⇒ Δ
       → bs ∣ Δ ∣ Bss ⊢₊ map-args σ {bs} args ⦂ As
    pres-arg {zero} {arg = ast M} (ast-p ⊢M) σ⦂ =
        ast-p (preserve-map M ⊢M σ⦂)
    pres-arg {suc b} {arg = bind arg} (bind-p {B = B}{A = A} ⊢arg) σ⦂ =
        bind-p (pres-arg ⊢arg (map-pres-ext σ⦂))
    pres-args {[]} {args = nil} nil-p σ⦂ = nil-p
    pres-args {b ∷ bs} {args = cons arg args} (cons-p ⊢arg ⊢args) σ⦂ =
        cons-p (pres-arg ⊢arg σ⦂) (pres-args ⊢args σ⦂)
