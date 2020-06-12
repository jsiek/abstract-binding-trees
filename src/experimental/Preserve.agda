{---------------------------

  Preservation of a predicate

      Let "I" be the kind for type-like things.

      A : I
      Γ Δ : List I

  preserve-fold : ∀{M σ Γ Δ A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold σ M ⦂ A

 ---------------------------}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)

module experimental.Preserve (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import GenericSubstitution
open import Data.Empty using (⊥)
open import Fold Op sig
open import ScopedTuple
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
open import Var

_∋_⦂_ : ∀{I : Set} → List I → Var → I → Set
_∋_⦂_ {I} [] x A = ⊥
_∋_⦂_ {I} (B ∷ Γ) zero A = A ≡ B
_∋_⦂_ {I} (B ∷ Γ) (suc x) A = Γ ∋ x ⦂ A

{----- Predicate on ABT's (e.g. Type System) -----}

module ABTPred {I : Set} (𝑃 : Op → List I → I → Set) where

  data _⊢_⦂_ : List I → ABT → I → Set
  data _∣_⊢a_⦂_ : (b : ℕ) → List I → Arg b → I → Set 
  data _∣_⊢as_⦂_ : (bs : List ℕ) → List I → Args bs → List I → Set
  
  data _⊢_⦂_ where
    var-p : ∀{Γ x A}
       → Γ ∋ x ⦂ A   {- use a predicate here too? -}
       → Γ ⊢ ` x ⦂ A
    op-op : ∀{Γ op}{args : Args (sig op)}{B As}
       → (sig op) ∣ Γ ⊢as args ⦂ As
       → 𝑃 op As B
       → Γ ⊢ op ⦅ args ⦆ ⦂ B

  data _∣_⊢a_⦂_ where
    ast-a : ∀{Γ}{M}{A}
       → Γ ⊢ M ⦂ A
       → 0 ∣ Γ ⊢a ast M ⦂ A
       
    bind-a : ∀{b}{B Γ arg A}
       → b ∣ (B ∷ Γ) ⊢a arg ⦂ A
       → (suc b) ∣ Γ ⊢a bind arg ⦂ A

  data _∣_⊢as_⦂_ where
    nil-a : ∀{Γ} → [] ∣ Γ ⊢as nil ⦂ []
    cons-a : ∀{b bs}{arg args}{Γ}{A}{As}
       → b ∣ Γ ⊢a arg ⦂ A
       → bs ∣ Γ ⊢as args ⦂ As
       → (b ∷ bs) ∣ Γ ⊢as cons arg args ⦂ (A ∷ As)

{- Predicate on result C's. -}

module FoldPred {I : Set}{V C : Set} (𝑃 : Op → List I → I → Set) 
  (𝐴 : List I → V → I → Set)
  (_⊢v_⦂_ : List I → V → I → Set)
  (_⊢c_⦂_ : List I → C → I → Set)
  (Env : Substable V)
  where
  open GenericSubst Env

  data _∣_⊢r_⦂_ : (b : ℕ) → List I → Bind V C b → I → Set where
    ast-r : ∀{Δ}{c}{A}
       → Δ ⊢c c ⦂ A
       → 0 ∣ Δ ⊢r c ⦂ A
       
    bind-r : ∀{b}{A B Δ}{f}
          → (∀{v} → (B ∷ Δ) ⊢v v ⦂ B
                      → 𝐴 (B ∷ Δ) v B
                      → b ∣ (B ∷ Δ) ⊢r (f v) ⦂ A)
          → (suc b) ∣ Δ ⊢r f ⦂ A
  
  data _∣_⊢rs_⦂_ : ∀(bs : List ℕ) → List I 
                → Tuple bs (Bind V C) → List I → Set where
    nil-r : ∀{Δ} → [] ∣ Δ ⊢rs tt ⦂ []
    cons-r : ∀{b bs}{r rs}{Δ}{A}{As}
        → b ∣ Δ ⊢r r ⦂ A
        → bs ∣ Δ ⊢rs rs ⦂ As
        → (b ∷ bs) ∣ Δ ⊢rs ⟨ r , rs ⟩ ⦂ (A ∷ As)

  data _⦂_⇒_ : GSubst V → List I → List I → Set where
    empty-env : ∀{k} → ↑ k ⦂ [] ⇒ []
    ext-env : ∀{v σ Γ Δ A}
       → (A ∷ Δ) ⊢v v ⦂ A
       → 𝐴 (A ∷ Δ) v A
       → (_⦂_⇒_ σ Γ Δ)
       → _⦂_⇒_ (g-extend v σ) (A ∷ Γ) (A ∷ Δ)

module PreserveFold {V C I : Set} (F : Fold V C)
 (𝑃 : Op → List I → I → Set)
 (𝐴 : List I → V → I → Set)
 (_⊢v_⦂_ : List I → V → I → Set)
 (_⊢c_⦂_ : List I → C → I → Set)
 where
 open Fold F ; open Substable S ; open GenericSubst S
 open ABTPred 𝑃 ; open FoldPred 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_ S

 module ExtV (ext-⊢v : ∀{σ : GSubst V}{A B : I}{ Δ x v}
                    → Δ ⊢v ⧼ σ ⧽ x ⦂ A
                    → (B ∷ Δ) ⊢v ⧼ g-extend v σ ⧽ (suc x) ⦂ A) where

  lookup-pres : ∀{σ}{Γ Δ}{x}{A} → σ ⦂ Γ ⇒ Δ → Γ ∋ x ⦂ A
           → Δ ⊢v ⧼ σ ⧽ x ⦂ A
  lookup-pres {x = zero} (ext-env ⊢v0 A0 σ⦂) refl = ⊢v0
  lookup-pres {x = suc x}{A} (ext-env {v}{σ}{Γ}{Δ}{B} ⊢v0 𝐴0 σ⦂) ∋x =
    let IH = lookup-pres {σ}{Γ}{Δ}{x}{A} σ⦂ ∋x in
    ext-⊢v {σ}{v = v} IH

  extend-pres' : ∀{v}{σ}{Γ Δ A}
     → (A ∷ Δ) ⊢v v ⦂ A
     → 𝐴 (A ∷ Δ) v A
     → σ ⦂ Γ ⇒ Δ
     → (g-extend v σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  extend-pres' {v} {_} {.[]} {.[]} {A} ⊢v⦂ 𝐴v empty-env = ext-env ⊢v⦂ 𝐴v empty-env
  extend-pres' {v} {_} {.(_ ∷ _)} {.(_ ∷ _)} {A} ⊢v⦂ 𝐴v (ext-env ⊢v₁⦂ 𝐴v₁ σ⦂) =
      ext-env ⊢v⦂ 𝐴v (extend-pres' ⊢v₁⦂ 𝐴v₁ σ⦂)

  module Reqs 
    (extend-pres : ∀{v}{σ}{Γ Δ A} → (A ∷ Δ) ⊢v v ⦂ A
            → 𝐴 (A ∷ Δ) v A → σ ⦂ Γ ⇒ Δ
            → (g-extend v σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ))
    (ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c (ret v) ⦂ A)
    (op-pres : ∀ {op}{Rs}{Δ}{A}{As}
            → sig op ∣ Δ ⊢rs Rs ⦂ As
            → 𝑃 op As A → Δ ⊢c (fold-op op Rs) ⦂ A)
    where
    preserve-fold : ∀{M : ABT}{σ : GSubst V}{Γ Δ : List I}{A : I}
       → Γ ⊢ M ⦂ A
       → σ ⦂ Γ ⇒ Δ
       → Δ ⊢c fold  σ M ⦂ A
    pres-arg : ∀{b}{Γ Δ}{arg : Arg b}{A}{σ}
       → b ∣ Γ ⊢a arg ⦂ A
       → _⦂_⇒_  σ Γ Δ
       → b ∣ Δ ⊢r fold-arg  σ {b} arg ⦂ A
    pres-args : ∀{bs}{Γ Δ}{args : Args bs}{As}{σ}
       → bs ∣ Γ ⊢as args ⦂ As
       → _⦂_⇒_  σ Γ Δ
       → bs ∣ Δ ⊢rs fold-args σ args ⦂ As
    preserve-fold {` x} {σ} {Γ} {Δ} {A} (var-p ∋x) σΓΔ =
        ret-pres (lookup-pres {σ} σΓΔ ∋x)
    preserve-fold {op ⦅ args ⦆} {σ} {Γ} {Δ} {A} (op-op ⊢args 𝑃op) σΓΔ =
        op-pres  (pres-args  ⊢args σΓΔ) 𝑃op
    pres-arg {zero} {Γ} {Δ} {ast M} {A} {σ} (ast-a ⊢arg) σΓΔ =
        ast-r (preserve-fold ⊢arg σΓΔ)
    pres-arg {suc b} {Γ} {Δ} {bind arg} {A} {σ} (bind-a {b}{B} ⊢arg) σΓΔ =
        bind-r G
        where
        G : ∀{v} → (B ∷ Δ) ⊢v v ⦂ B
           → 𝐴 (B ∷ Δ) v B
           → b ∣ B ∷ Δ ⊢r fold-arg σ (bind arg) v ⦂ A
        G {v} ⊢v⦂B 𝐴Mv = pres-arg ⊢arg (extend-pres ⊢v⦂B 𝐴Mv σΓΔ)
    pres-args {[]} {Γ} {Δ} {nil} {[]} ⊢args σΓΔ = nil-r 
    pres-args {b ∷ bs} {Γ} {Δ} {cons arg args} {A ∷ As}
        (cons-a ⊢arg ⊢args) σΓΔ =
        cons-r  (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)

