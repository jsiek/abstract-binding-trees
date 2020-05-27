{---------------------------

  Preservation of a predicate

      Let "I" be the kind for type-like things.

      A : I
      Γ Δ : List I

  preserve : ∀{M}{σ}{Γ Δ}{A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold σ M ⦂ A

 ---------------------------}

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

module Preserve (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Data.Empty using (⊥)
open import Fold
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
  renaming (subst to eq-subst)
open import Var

_∋_⦂_ : ∀{I : Set} → List I → Var → I → Set
_∋_⦂_ {I} [] x A = ⊥
_∋_⦂_ {I} (B ∷ Γ) zero A = A ≡ B
_∋_⦂_ {I} (B ∷ Γ) (suc x) A = Γ ∋ x ⦂ A

module ABTPred {I : Set} (𝒫 : Op → List I → I → Set) where
  
  data _⊢_⦂_ : List I → ABT → I → Set
  data _∣_⊢a_⦂_ : (b : ℕ) → List I → Arg b → I → Set 
  data _∣_⊢as_⦂_ : (bs : List ℕ) → List I → Args bs → List I → Set   
  
  data _⊢_⦂_ where
    var-p : ∀{Γ x A}
       → Γ ∋ x ⦂ A
       → Γ ⊢ ` x ⦂ A
    op-op : ∀{Γ op args}{B As}
       → (sig op) ∣ Γ ⊢as args ⦂ As
       → 𝒫 op As B
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
       → (b ∷ bs) ∣ Γ ⊢as (cons arg args) ⦂ (A ∷ As)


module PresArgResult {V C : Set}{I : Set}
  (𝒫 : Op → List I → I → Set)
  (𝒜 : List I → ABT → V → I → Set)
  (_⊢v_↝_⦂_ : List I → ABT → V → I → Set)
  (_⊢c_↝_⦂_ : List I → ABT → C → I → Set)
  where

  open ABTPred 𝒫
  open ArgResult V C
  
  data _∣_⊢r_⦂_ : (b : ℕ) → List I → ArgRes b → I → Set where
    ast-r : ∀{Δ}{M}{c}{A}
       → Δ ⊢c M ↝ c ⦂ A
       → 0 ∣ Δ ⊢r c ⦂ A
       
    bind-r : ∀{b}{A B Δ}{f}
          → (∀ {v}{M} → (B ∷ Δ) ⊢v M ↝ v ⦂ B
                      → 𝒜 (B ∷ Δ) M v B
                      → b ∣ (B ∷ Δ) ⊢r (f v) ⦂ A)
          → (suc b) ∣ Δ ⊢r f ⦂ A
  
  data _∣_⊢rs_⦂_ : (bs : List ℕ) → List I → ArgsRes bs → List I → Set where
    nil-r : ∀{Δ} → [] ∣ Δ ⊢rs rnil ⦂ []
    cons-r : ∀{b bs}{r rs}{Δ}{A}{As}
        → b ∣ Δ ⊢r r ⦂ A
        → bs ∣ Δ ⊢rs rs ⦂ As
        → (b ∷ bs) ∣ Δ ⊢rs rcons r rs ⦂ (A ∷ As)


record Preservable {V C Env}(I : Set) (F : Foldable V C Op sig Env) : Set₁ where
  field 𝒫 : Op → List I → I → Set
  field 𝒜 : List I → ABT → V → I → Set
  field _⦂_⇒_ : Env → List I → List I → Set
  field _⊢v_↝_⦂_ : List I → ABT → V → I → Set
  field _⊢c_↝_⦂_ : List I → ABT → C → I → Set
  open PresArgResult 𝒫 𝒜 _⊢v_↝_⦂_ _⊢c_↝_⦂_
  open Foldable F
  open ArgResult V C
  field lookup-pres : ∀{σ}{Γ Δ}{x}{A} → σ ⦂ Γ ⇒ Δ → Γ ∋ x ⦂ A → Δ ⊢v ` x ↝ (EnvSig.lookup env σ x) ⦂ A
  field extend-pres : ∀ {v}{σ}{Γ Δ A}{M} → (A ∷ Δ) ⊢v M ↝ v ⦂ A → 𝒜 (A ∷ Δ) M v A → σ ⦂ Γ ⇒ Δ → (EnvSig.extend env σ v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  field ret-pres : ∀{v}{Δ}{A}{M} → Δ ⊢v M ↝ v ⦂ A → Δ ⊢c M ↝ (ret v) ⦂ A
  field var-pres : ∀{x}{Δ}{A} → Δ ∋ x ⦂ A → Δ ⊢v ` x ↝ fold-free-var x ⦂ A
  field op-pres : ∀ {op}{Rs}{Δ}{A}{As}{M} → sig op ∣ Δ ⊢rs Rs ⦂ As → 𝒫 op As A → Δ ⊢c M ↝ (fold-op op Rs) ⦂ A


module Preservation{V C Env}{I}
  (F : Foldable V C Op sig Env)
  (P : Preservable I F)
  where
  open Folder F using (fold; fold-arg; fold-args)
  open Foldable F using (env; fold-op)
  open Preservable P

  open ABTPred 𝒫
  open PresArgResult 𝒫 𝒜 _⊢v_↝_⦂_ _⊢c_↝_⦂_ public

  preserve : ∀{M}{σ}{Γ Δ}{A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold σ M ⦂ A
  pres-arg : ∀{b}{Γ Δ}{arg : Arg b}{A}{σ}
     → b ∣ Γ ⊢a arg ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → b ∣ Δ ⊢r fold-arg σ arg ⦂ A
  pres-args : ∀{bs}{Γ Δ}{args : Args bs}{As}{σ}
     → bs ∣ Γ ⊢as args ⦂ As
     → σ ⦂ Γ ⇒ Δ
     → bs ∣ Δ ⊢rs fold-args σ args ⦂ As
  preserve {` x} {σ} {Γ} {Δ} {A} (var-p ∋x) σΓΔ =
      ret-pres (lookup-pres σΓΔ ∋x)
  preserve {op ⦅ args ⦆} {σ} {Γ} {Δ} {A} (op-op ⊢args 𝒫op) σΓΔ =
      op-pres (pres-args ⊢args σΓΔ) 𝒫op
  pres-arg {zero} {Γ} {Δ} {ast M} {A} {σ} (ast-a ⊢M) σΓΔ = ast-r (preserve ⊢M σΓΔ)
  pres-arg {suc b} {Γ} {Δ} {bind arg} {A} {σ} (bind-a {b}{B} ⊢arg) σΓΔ =
      bind-r G
      where
      G : ∀ {v}{M}
         → (B ∷ Δ) ⊢v M ↝ v ⦂ B
         → 𝒜 (B ∷ Δ) M v B
         → b ∣ B ∷ Δ ⊢r fold-arg σ (bind arg) v ⦂ A
      G {v} ⊢v⦂B 𝒜Mv = pres-arg {b} {arg = arg} ⊢arg (extend-pres ⊢v⦂B 𝒜Mv σΓΔ)
  pres-args {[]} {Γ} {Δ} {nil} {[]} ⊢args σΓΔ = nil-r
  pres-args {b ∷ bs} {Γ} {Δ} {cons arg args} {A ∷ As} (cons-a ⊢arg ⊢args) σΓΔ =
      cons-r (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)
