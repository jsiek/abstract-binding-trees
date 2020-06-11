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
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Size using (Size)

module experimental.Preserve (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig
open import GenericSubstitution
open import Data.Empty using (⊥)
open import experimental.Fold Op sig
open import experimental.ScopedTuple
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
open import Var

_∋_⦂_ : ∀{I : Set} → List I → Var → I → Set
_∋_⦂_ {I} [] x A = ⊥
_∋_⦂_ {I} (B ∷ Γ) zero A = A ≡ B
_∋_⦂_ {I} (B ∷ Γ) (suc x) A = Γ ∋ x ⦂ A

module ABTPred {I : Set}{V C : Set} (𝑃 : Op → List I → I → Set) 
  (𝐴 : List I → ABT → V → I → Set)
  (_⊢v_↝_⦂_ : List I → ABT → V → I → Set)
  (_⊢c_↝_⦂_ : List I → ABT → C → I → Set)
  (Env : Substable V)
  where

  {- Predicate on ABT's (e.g. Type System) -}

  data _⊢_⦂_ : List I → ABT → I → Set
  data _∣_⊢a_⦂_ : (b : ℕ) → List I → ABT → I → Set 
  data _∣_⊢as_⦂_ : (bs : List ℕ) → List I → Tuple bs (λ _ → ABT) → List I → Set
  
  data _⊢_⦂_ where
    var-p : ∀{Γ x A}
       → Γ ∋ x ⦂ A   {- use a predicate here too? -}
       → Γ ⊢ ` x ⦂ A
    op-op : ∀{Γ op args}{B As}
       → (sig op) ∣ Γ ⊢as args ⦂ As
       → 𝑃 op As B
       → Γ ⊢ op ⦅ args ⦆ ⦂ B

  data _∣_⊢a_⦂_ where
    ast-a : ∀{Γ}{M}{A}
       → Γ ⊢ M ⦂ A
       → 0 ∣ Γ ⊢a M ⦂ A
       
    bind-a : ∀{b}{B Γ M A}
       → b ∣ (B ∷ Γ) ⊢a M ⦂ A
       → (suc b) ∣ Γ ⊢a M ⦂ A

  {- replace with zip? -}
  data _∣_⊢as_⦂_ where
    nil-a : ∀{Γ} → [] ∣ Γ ⊢as tt ⦂ []
    
    cons-a : ∀{b bs}{arg args}{Γ}{A}{As}
       → b ∣ Γ ⊢a arg ⦂ A
       → bs ∣ Γ ⊢as args ⦂ As
       → (b ∷ bs) ∣ Γ ⊢as ⟨ arg ,  args ⟩ ⦂ (A ∷ As)

  {- Predicate on result C's. -}

  data _∣_⊢r_↝_⦂_ : (b : ℕ) → List I → ABT → Bind V C b → I → Set where
    ast-r : ∀{s}{Δ}{M : Term s}{c}{A}
       → Δ ⊢c M ↝ c ⦂ A
       → 0 ∣ Δ ⊢r M ↝ c ⦂ A
       
    bind-r : ∀{s}{b}{A B Δ}{f}{arg : Term s}
          → (∀{v}{M : Term s} → (B ∷ Δ) ⊢v M ↝ v ⦂ B
                      → 𝐴 (B ∷ Δ) M v B
                      → b ∣ (B ∷ Δ) ⊢r arg ↝ (f v) ⦂ A)
          → (suc b) ∣ Δ ⊢r arg ↝ f ⦂ A
  
  data _∣_⊢rs_↝_⦂_ : ∀{s}(bs : List ℕ) → List I → Tuple bs (λ _ → Term s)
                → Tuple bs (Bind V C) → List I → Set where
    nil-r : ∀{s}{Δ} → _∣_⊢rs_↝_⦂_ {s} [] Δ tt tt []
    cons-r : ∀{s}{b bs}{r rs}{Δ}{A}{As}
              {arg : Term s}{args : Tuple bs (λ _ → Term s)}
        → b ∣ Δ ⊢r arg ↝ r ⦂ A
        → bs ∣ Δ ⊢rs args ↝ rs ⦂ As
        → (b ∷ bs) ∣ Δ ⊢rs ⟨ arg , args ⟩ ↝ ⟨ r , rs ⟩ ⦂ (A ∷ As)

  {- Predicate on environemnts -}
  open GenericSubst Env

  data _⦂_⇒_ : {s : Size} → GSubst V → List I → List I → Set where
    empty-env : ∀{k} → ↑ k ⦂ [] ⇒ []
    ext-env : ∀{s}{v σ Γ Δ A}
       → (A ∷ Δ) ⊢v `_ {s} 0 ↝ v ⦂ A
       → 𝐴 (A ∷ Δ) (`_ {s} 0) v A
       → (_⦂_⇒_ {s} σ Γ Δ)
       → _⦂_⇒_ {s} (g-extend v σ) (A ∷ Γ) (A ∷ Δ)
  
  lookup-pres' : ∀{s}{σ}{Γ Δ}{x}{A} → (_⦂_⇒_ {s} σ Γ Δ) → Γ ∋ x ⦂ A
           → Δ ⊢v `_ {s} x ↝ ⧼ σ ⧽ x ⦂ A
  lookup-pres' {s}{x = zero} (ext-env ⊢v0 A0 σ⦂) refl = ⊢v0
  lookup-pres' {s}{x = suc x}{A} (ext-env {.s}{v}{σ}{Γ}{Δ}{B} ⊢v0 𝐴0 σ⦂) ∋x =
    let IH = lookup-pres' {s}{σ}{Γ}{Δ}{x}{A} σ⦂ ∋x in
    {!!}
{-
 Γ ∋ x ⦂ A
 σ ⦂ Γ ⇒ Δ
 Δ ⊢v ` x ↝ ⧼ σ ⧽ x ⦂ A
—————————————————————————————————————
(B ∷ Δ) ⊢v ` suc x ↝ ⧼ g-inc σ ⧽ x ⦂ A
-}

record Preservable {V C}(I : Set) (F : Fold V C) : Set₁ where
  field 𝑃 : Op → List I → I → Set
  field 𝐴 : List I → ABT → V → I → Set
  field _⊢v_↝_⦂_ : List I → ABT → V → I → Set
  field _⊢c_↝_⦂_ : List I → ABT → C → I → Set
  open Fold F ; open Substable S 
  open ABTPred 𝑃 𝐴 _⊢v_↝_⦂_ _⊢c_↝_⦂_ S

  field lookup-pres : ∀{s}{σ}{Γ Δ}{x}{A} → σ ⦂ Γ ⇒ Δ → Γ ∋ x ⦂ A
           → Δ ⊢v `_ {s} x ↝ ⧼ σ ⧽ x ⦂ A
  field extend-pres : ∀ {v}{σ}{Γ Δ A}{M} → (A ∷ Δ) ⊢v M ↝ v ⦂ A
           → 𝐴 (A ∷ Δ) M v A → σ ⦂ Γ ⇒ Δ → (g-extend v σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  field ret-pres : ∀{v}{Δ}{A}{M} → Δ ⊢v M ↝ v ⦂ A → Δ ⊢c M ↝ (ret v) ⦂ A
  field op-pres : ∀ {s}{op}{Rs}{Δ}{A}{As}{args : Tuple (sig op) (λ _ → Term s)}
           → sig op ∣ Δ ⊢rs args ↝ Rs ⦂ As
           → 𝑃 op As A → Δ ⊢c op ⦅ args ⦆ ↝ (fold-op op Rs) ⦂ A

  preserve : ∀{s}{M : Term s}{σ : GSubst V}{Γ Δ : List I}{A : I}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold {s} σ M ⦂ A
  pres-arg : ∀{s}{b}{Γ Δ}{arg : Term s}{A}{σ}
     → b ∣ Γ ⊢a arg ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → b ∣ Δ ⊢r arg ↝ fold-arg {s} σ {b} arg ⦂ A
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
      bind-r G
      where
      G : ∀{v}{M : Term s} → (B ∷ Δ) ⊢v M ↝ v ⦂ B → 𝐴 (B ∷ Δ) M v B
         → b ∣ B ∷ Δ ⊢r arg ↝ fold-arg σ arg v ⦂ A
      G {v}{M} ⊢v⦂B 𝐴Mv = pres-arg ⊢arg (extend-pres ⊢v⦂B 𝐴Mv σΓΔ)
  pres-args {s}{[]} {Γ} {Δ} {tt} {[]} ⊢args σΓΔ = nil-r {s}
  pres-args {s}{b ∷ bs} {Γ} {Δ} {⟨ arg , args ⟩} {A ∷ As}
      (cons-a ⊢arg ⊢args) σΓΔ =
      cons-r {s} (pres-arg {s}{b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)

