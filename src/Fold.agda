open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Environment
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var
open import ScopedTuple
    using (Tuple; map; _✖_; zip; zip-refl; map-pres-zip; map-compose-zip;
           map-compose; zip-map→rel; Lift-Eq-Tuple; Lift-Rel-Tuple; zip→rel)
open import GenericSubstitution
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Level using (Lift; lift)

module Fold (Op : Set) (sig : Op → List ℕ) where

open Shiftable {{...}}
open Env {{...}}
open import AbstractBindingTree Op sig

Bind : {ℓ : Level} → Set ℓ → Set ℓ → ℕ → Set ℓ
Bind V C zero = C
Bind V C (suc b) = V → Bind V C b

{-
module Reify {ℓ : Level} (V : Set) (C : Set ℓ) (var→val : Var → V) where
  reify : {b : ℕ} → Bind V C b → C
  reify {zero} M = M
  reify {suc b} f = reify {b} (f (var→val 0))
-}

{-------------------------------------------------------------------------------
 Folding over an abstract binding tree
 ------------------------------------------------------------------------------}

record Foldable {ℓ : Level}(V : Set ℓ)(C : Set ℓ) : Set (lsuc ℓ) where
  field ret : V → C
        fold-op : (op : Op) → Tuple (sig op) (Bind V C) → C

open Foldable {{...}}

fold : ∀{ℓ}{E V C : Set ℓ}
   {{_ : Shiftable V}} {{_ : Env E V}} {{_ : Foldable V C}}
   → E → ABT → C
fold-arg : ∀{ℓ}{E V C : Set ℓ}
   {{_ : Shiftable V}} {{_ : Env E V}} {{_ : Foldable V C}}
   → E → {b : ℕ} → Arg b → Bind V C b
fold-args : ∀{ℓ}{E V C : Set ℓ}
   {{_ : Shiftable V}} {{_ : Env E V}} {{_ : Foldable V C}}
   → E → {bs : List ℕ} → Args bs → Tuple bs (Bind V C)

fold σ (` x) = ret (⟅ σ ⟆ x)
fold σ (op ⦅ args ⦆) = fold-op op (fold-args σ {sig op} args)
fold-arg σ {zero} (ast M) = fold σ M
fold-arg σ {suc b} (bind arg) v = fold-arg (σ , v) arg
fold-args σ {[]} nil = tt
fold-args σ {b ∷ bs} (cons arg args) = ⟨ fold-arg σ arg , fold-args σ args ⟩

{-------------------------------------------------------------------------------
 Simulation between two folds
 ------------------------------------------------------------------------------}

record RelFold {ℓ₁ ℓ₂} (V₁ : Set ℓ₁)(V₂ : Set ℓ₂) (C₁ : Set ℓ₁)(C₂ : Set ℓ₂)
  : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field _∼_ : V₁ → V₂ → Set (ℓ₁ ⊔ ℓ₂)
        _≈_ : C₁ → C₂ → Set (ℓ₁ ⊔ ℓ₂)
open RelFold {{...}}

_⩳_  : ∀ {ℓ₁ ℓ₂ : Level}{V₁ : Set ℓ₁}{V₂ : Set ℓ₂}{C₁ : Set ℓ₁}{C₂ : Set ℓ₂}
     {{_ : RelFold V₁ V₂ C₁ C₂}}
   → (Bind V₁ C₁) ✖ (Bind V₂ C₂)
_⩳_ {b = zero} c₁ c₂ = c₁ ≈ c₂
_⩳_ {b = suc b} r₁ r₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → r₁ v₁ ⩳ r₂ v₂

record Similar {ℓ₁ ℓ₂} (V₁ : Set ℓ₁)(V₂ : Set ℓ₂) (C₁ : Set ℓ₁)(C₂ : Set ℓ₂)
  {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
  {{_ : Foldable V₁ C₁}} {{_ : Foldable V₂ C₂}}
  {{_ : RelFold V₁ V₂ C₁ C₂}} : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field ret≈ : ∀{v₁ : V₁}{v₂ : V₂} → v₁ ∼ v₂ → ret v₁ ≈ ret v₂
        var→val∼ : ∀ x → var→val x ∼ var→val x
        shift∼ : ∀{v₁ : V₁}{v₂ : V₂} → v₁ ∼ v₂ → ⇑ v₁ ∼ ⇑ v₂
  field op⩳ : ∀{op}{rs₁ : Tuple (sig op) (Bind V₁ C₁)}
                   {rs₂ : Tuple (sig op) (Bind V₂ C₂)}
            → zip _⩳_ rs₁ rs₂ → fold-op op rs₁ ⩳ fold-op op rs₂
  
open Similar {{...}}

_≅_ : ∀ {ℓ₁ ℓ₂}{V₁ : Set ℓ₁}{E₁ : Set ℓ₁}{V₂ : Set ℓ₂}{E₂ : Set ℓ₂}
   {C₁ : Set ℓ₁}{C₂ : Set ℓ₂}
   {{_ : Shiftable V₁}}{{_ : Shiftable V₂}}
   {{_ : Env E₁ V₁}} {{_ : Env E₂ V₂}}
   {{_ : Foldable V₁ C₁}} {{_ : Foldable V₂ C₂}}
   {{_ : RelFold V₁ V₂ C₁ C₂}}
   {{_ : Similar V₁ V₂ C₁ C₂}}
   (σ₁ : E₁) (σ₂ : E₂)  → Set (ℓ₁ ⊔ ℓ₂)
_≅_ σ₁ σ₂ = ∀ x → ⟅ σ₁ ⟆ x ∼ ⟅ σ₂ ⟆ x

sim : ∀{ℓ₁ ℓ₂}{V₁ E₁ : Set ℓ₁}{V₂ E₂ : Set ℓ₂}{C₁ : Set ℓ₁}{C₂ : Set ℓ₂}
   {σ₁ : E₁}{σ₂ : E₂}
   {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
   {{_ : Env E₁ V₁}} {{_ : Env E₂ V₂}}
   {{_ : Foldable V₁ C₁}} {{_ : Foldable V₂ C₂}}
   {{_ : RelFold V₁ V₂ C₁ C₂}}
   {{_ : Similar V₁ V₂ C₁ C₂}}
   → (M : ABT)
   → σ₁ ≅ σ₂
   → (fold σ₁ M) ≈ (fold σ₂ M)
sim (` x) σ₁≅σ₂ = ret≈ (σ₁≅σ₂ x)
sim {V₁ = V₁}{E₁}{V₂}{E₂}{C₁}{C₂}{σ₁}{σ₂} (op ⦅ args ⦆) σ₁≅σ₂ =
    op⩳ (sim-args args σ₁≅σ₂)
    where
    sim-ext : ∀{σ₁ : E₁}{σ₂ : E₂}{v₁ : V₁}{v₂ : V₂}
       → σ₁ ≅ σ₂ → v₁ ∼ v₂ → (σ₁ , v₁) ≅ (σ₂ , v₂)
    sim-ext {σ₁} {σ₂} {v₁} {v₂} σ₁≅σ₂ v₁∼v₂ zero rewrite lookup-0 σ₁ v₁
        | lookup-0 σ₂ v₂ = v₁∼v₂
    sim-ext {σ₁} {σ₂} {v₁} {v₂} σ₁≅σ₂ v₁∼v₂ (suc x)
        rewrite lookup-suc σ₁ v₁ x | lookup-suc σ₂ v₂ x = shift∼ (σ₁≅σ₂ x)

    sim-arg : ∀{σ₁ : E₁}{σ₂ : E₂}{b} (arg : Arg b)
       → σ₁ ≅ σ₂ → (fold-arg σ₁ {b} arg) ⩳ (fold-arg σ₂ {b} arg)
    sim-args : ∀{σ₁ : E₁}{σ₂ : E₂}{bs} (args : Args bs)
       → σ₁ ≅ σ₂ → zip _⩳_ (fold-args σ₁ {bs} args)
                           (fold-args σ₂ {bs} args)

    sim-arg {b = zero} (ast M) σ₁≊σ₂ = sim M σ₁≊σ₂
    sim-arg {b = suc b} (bind arg) σ₁≊σ₂ v₁∼v₂ =
        sim-arg {b = b} arg (sim-ext σ₁≊σ₂ v₁∼v₂)
    sim-args {bs = []} args σ₁≊σ₂ = tt
    sim-args {bs = b ∷ bs} (cons arg args) σ₁≊σ₂ =
        ⟨ sim-arg arg σ₁≊σ₂ , sim-args args σ₁≊σ₂ ⟩
