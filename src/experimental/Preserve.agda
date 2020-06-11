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
open import experimental.Fold Op sig
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
       → Γ ∋ x ⦂ A   {- use a predicate here too? -}
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
    ast-r : ∀{s}{Δ}{M : Term s}{c}{A}
       → Δ ⊢c M ↝ c ⦂ A
       → 0 ∣ Δ ⊢r M ↝ c ⦂ A
       
    bind-r : ∀{s}{b}{A B Δ}{f}{arg : Term s}
          → (∀{v}{M : Term s} → (B ∷ Δ) ⊢v M ↝ v ⦂ B
                      → 𝒜 (B ∷ Δ) M v B
                      → b ∣ (B ∷ Δ) ⊢r M ↝ (f v) ⦂ A)
          → (suc b) ∣ Δ ⊢r arg ↝ f ⦂ A
  
  data _∣_⊢rs_↝_⦂_ : ∀{s}(bs : List ℕ) → List I → Tuple bs (λ _ → Term s)
                → Tuple bs (Bind V C) → List I → Set where
    nil-r : ∀{s}{Δ} → _∣_⊢rs_↝_⦂_ {s} [] Δ tt tt []
    cons-r : ∀{s}{b bs}{r rs}{Δ}{A}{As}
              {arg : Term s}{args : Tuple bs (λ _ → Term s)}
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

  field lookup-pres : ∀{s}{σ}{Γ Δ}{x}{A} → σ ⦂ Γ ⇒ Δ → Γ ∋ x ⦂ A
           → Δ ⊢v `_ {s} x ↝ ⧼ σ ⧽ x ⦂ A
  field extend-pres : ∀ {v}{σ}{Γ Δ A}{M} → (A ∷ Δ) ⊢v M ↝ v ⦂ A
           → 𝐴 (A ∷ Δ) M v A → σ ⦂ Γ ⇒ Δ → (v • g-inc σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  field ret-pres : ∀{v}{Δ}{A}{M} → Δ ⊢v M ↝ v ⦂ A → Δ ⊢c M ↝ (ret v) ⦂ A
  field op-pres : ∀ {s}{op}{Rs}{Δ}{A}{As}{args : Tuple (sig op) (λ _ → Term s)}
           → sig op ∣ Δ ⊢rs args ↝ Rs ⦂ As
           → 𝑃 op As A → Δ ⊢c op ⦅ args ⦆ ↝ (fold-op op Rs) ⦂ A


module Preservation{V C}{I} (F : Fold V C) (P : Preservable I F)
  where
  open Fold F using (fold; fold-arg; fold-op; g-inc)
  open Preservable P

  open ABTPred 𝑃
  open PresArgResult 𝑃 𝐴 _⊢v_↝_⦂_ _⊢c_↝_⦂_ public

  ScopedEnv : (b : ℕ) → Set
  ScopedEnv 0 = GSubst V
  ScopedEnv (suc b) = V → ScopedEnv b

  Ext : (b : ℕ) → GSubst V → ScopedEnv b
  Ext 0 σ = σ
  Ext (suc b) σ v = Ext b (v • g-inc σ)

  preserve : ∀{s}{M : Term s}{σ : GSubst V}{Γ Δ : List I}{A : I}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold {s} σ M ⦂ A
  pres-arg : ∀{s}{b}{Γ Δ}{arg : Term s}{A}{σ}
     → b ∣ Γ ⊢a arg ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → b ∣ Δ ⊢r arg ↝ fold-arg {s} σ arg ⦂ A
  pres-args : ∀{s}{bs}{Γ Δ}{args : Tuple bs (λ _ → Term s)}{As}{σ}
     → bs ∣ Γ ⊢as args ⦂ As
     → σ ⦂ Γ ⇒ Δ
     → bs ∣ Δ ⊢rs args ↝ map (fold-arg σ) args ⦂ As
  preserve {_}{`_ {s} x} {σ} {Γ} {Δ} {A} (var-p ∋x) σΓΔ =
      ret-pres (lookup-pres {s} σΓΔ ∋x)
  preserve {_}{_⦅_⦆ {s} op args} {σ} {Γ} {Δ} {A} (op-op ⊢args 𝑃op) σΓΔ =
      op-pres {s} (pres-args {s} ⊢args σΓΔ) 𝑃op
  pres-arg {s}{zero} {Γ} {Δ} {arg} {A} {σ} (ast-a ⊢arg) σΓΔ =
      ast-r (preserve ⊢arg σΓΔ)
  pres-arg {s}{suc b} {Γ} {Δ} {arg} {A} {σ} (bind-a {b}{B} ⊢arg) σΓΔ =
      bind-r {s}{b}{A}{B}{arg = arg} G
      where
      G : ∀{v}{M : Term s}
         → (B ∷ Δ) ⊢v M ↝ v ⦂ B
         → 𝐴 (B ∷ Δ) M v B
         → b ∣ B ∷ Δ ⊢r M ↝ fold-arg σ arg v ⦂ A
      G {v}{M} ⊢v⦂B 𝐴Mv =
        let e = extend-pres ⊢v⦂B 𝐴Mv σΓΔ in
        let pa = pres-arg {_}{b} {arg = M}{A} {!!} e in
        {!!}
  pres-args {s}{[]} {Γ} {Δ} {tt} {[]} ⊢args σΓΔ = nil-r {s}
  pres-args {s}{b ∷ bs} {Γ} {Δ} {⟨ arg , args ⟩} {A ∷ As}
      (cons-a ⊢arg ⊢args) σΓΔ =
      cons-r {s} (pres-arg {s}{b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)

