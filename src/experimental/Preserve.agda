{---------------------------

  NEEDS TO BE UPDATED

  Preservation of a predicate

      Let "I" be the kind for type-like things.

      A : I
      Γ Δ : List I

  preserve : ∀{M}{σ}{Γ Δ}{A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold σ M ⦂ A

 ---------------------------}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)

module experimental.Preserve (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig
open import GenericSubstitution
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import experimental.Fold
open import experimental.ScopedTuple
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
  data _∣_⊢a_⦂_ : (b : ℕ) → List I → ABT → I → Set 
  data _∣_⊢as_⦂_ : (bs : List ℕ) → List I → Tuple bs (λ _ → ABT) → List I → Set   
  
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
       → 0 ∣ Γ ⊢a M ⦂ A
       
    bind-a : ∀{b}{B Γ M A}
       → b ∣ (B ∷ Γ) ⊢a M ⦂ A
       → (suc b) ∣ Γ ⊢a M ⦂ A

  {- don't need? -}
  data _∣_⊢as_⦂_ where
    nil-a : ∀{Γ} → [] ∣ Γ ⊢as tt ⦂ []
    
    cons-a : ∀{b bs}{arg args}{Γ}{A}{As}
       → b ∣ Γ ⊢a arg ⦂ A
       → bs ∣ Γ ⊢as args ⦂ As
       → (b ∷ bs) ∣ Γ ⊢as ⟨ arg ,  args ⟩ ⦂ (A ∷ As)


module PresArgResult {V C : Set}{I : Set}
  (𝒫 : Op → List I → I → Set)
  (𝒜 : List I → ABT → V → I → Set)
  (_⊢v_↝_⦂_ : List I → ABT → V → I → Set)
  (_⊢c_↝_⦂_ : List I → ABT → C → I → Set)
  where

  open ABTPred 𝒫
  
  data _∣_⊢r_↝_⦂_ : (b : ℕ) → List I → ABT → Bind V C b → I → Set where
    ast-r : ∀{Δ}{M}{c}{A}
       → Δ ⊢c M ↝ c ⦂ A
       → 0 ∣ Δ ⊢r M ↝ c ⦂ A
       
    bind-r : ∀{b}{A B Δ}{f}{M}
          → (∀ {v}{M} → (B ∷ Δ) ⊢v M ↝ v ⦂ B
                      → 𝒜 (B ∷ Δ) M v B
                      → b ∣ (B ∷ Δ) ⊢r M ↝ (f v) ⦂ A)
          → (suc b) ∣ Δ ⊢r M ↝ f ⦂ A
  
  data _∣_⊢rs_↝_⦂_ : (bs : List ℕ) → List I → Tuple bs (λ _ → ABT)
                → Tuple bs (λ _ → C) → List I → Set where
    nil-r : ∀{Δ} → [] ∣ Δ ⊢rs tt ↝ tt ⦂ []
    cons-r : ∀{b bs}{r rs}{Δ}{A}{As}{arg}{args}
        → b ∣ Δ ⊢r arg ↝ r ⦂ A
        → bs ∣ Δ ⊢rs args ↝ rs ⦂ As
        → (b ∷ bs) ∣ Δ ⊢rs ⟨ arg , args ⟩ ↝ ⟨ r , rs ⟩ ⦂ (A ∷ As)


record Preservable {V C}(I : Set) (F : Fold V C) : Set₁ where
  field 𝑃 : Op → List I → I → Set
  field 𝐴 : List I → ABT → V → I → Set
  field _⦂_⇒_ : GSubst V → List I → List I → Set
  field _⊢v_↝_⦂_ : List I → ABT → V → I → Set
  field _⊢c_↝_⦂_ : List I → ABT → C → I → Set
  open PresArgResult 𝑃 𝐴 _⊢v_↝_⦂_ _⊢c_↝_⦂_
  open Fold F
  open Substable S

  field lookup-pres : ∀{σ}{Γ Δ}{x}{A} → σ ⦂ Γ ⇒ Δ → Γ ∋ x ⦂ A
           → Δ ⊢v ` x ↝ ⧼ σ ⧽ x ⦂ A
  field extend-pres : ∀ {v}{σ}{Γ Δ A}{M} → (A ∷ Δ) ⊢v M ↝ v ⦂ A
           → 𝐴 (A ∷ Δ) M v A → σ ⦂ Γ ⇒ Δ → (v • σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  field ret-pres : ∀{v}{Δ}{A}{M} → Δ ⊢v M ↝ v ⦂ A → Δ ⊢c M ↝ (ret v) ⦂ A
  field var-pres : ∀{x}{Δ}{A} → Δ ∋ x ⦂ A → Δ ⊢v ` x ↝ var→val x ⦂ A
  field op-pres : ∀ {op}{Rs}{Δ}{A}{As}{args} → sig op ∣ Δ ⊢rs args ↝ Rs ⦂ As
           → 𝑃 op As A → Δ ⊢c op ⦅ args ⦆ ↝ (fold-op op Rs) ⦂ A


module Preservation{V C Env}{I} (F : Fold V C) (P : Preservable I F)
  where
  open Fold F using (fold; fold-arg; fold-op)
  open Preservable P

  open ABTPred 𝑃
  open PresArgResult 𝑃 𝐴 _⊢v_↝_⦂_ _⊢c_↝_⦂_ public

  preserve : ∀{M}{σ}{Γ Δ}{A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold σ M ⦂ A
  pres-arg : ∀{b}{Γ Δ}{arg : ABT}{A}{σ}
     → b ∣ Γ ⊢a arg ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → b ∣ Δ ⊢r arg ↝ fold-arg σ arg ⦂ A
  pres-args : ∀{bs}{Γ Δ}{args : Tuple bs (λ _ → ABT)}{As}{σ}
     → bs ∣ Γ ⊢as args ⦂ As
     → σ ⦂ Γ ⇒ Δ
     → bs ∣ Δ ⊢rs args ↝ map (fold-arg σ) args ⦂ As
  preserve {` x} {σ} {Γ} {Δ} {A} (var-p ∋x) σΓΔ =
      ret-pres (lookup-pres σΓΔ ∋x)
  preserve {op ⦅ args ⦆} {σ} {Γ} {Δ} {A} (op-op ⊢args 𝑃op) σΓΔ =
      op-pres (pres-args ⊢args σΓΔ) 𝑃op
  pres-arg {zero} {Γ} {Δ} {M} {A} {σ} (ast-a ⊢M) σΓΔ =
      ast-r (preserve ⊢M σΓΔ)
  pres-arg {suc b} {Γ} {Δ} {arg} {A} {σ} (bind-a {b}{B} ⊢arg) σΓΔ =
      bind-r G
      where
      G : ∀ {v}{M}
         → (B ∷ Δ) ⊢v M ↝ v ⦂ B
         → 𝐴 (B ∷ Δ) M v B
         → b ∣ B ∷ Δ ⊢r arg ↝ fold-arg σ arg v ⦂ A
      G {v} ⊢v⦂B 𝐴Mv = pres-arg {b} {arg = arg} ⊢arg (extend-pres ⊢v⦂B 𝐴Mv σΓΔ)
  pres-args {[]} {Γ} {Δ} {tt} {[]} ⊢args σΓΔ = nil-r
  pres-args {b ∷ bs} {Γ} {Δ} {⟨ arg , args ⟩} {A ∷ As} (cons-a ⊢arg ⊢args) σΓΔ =
      cons-r (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)
