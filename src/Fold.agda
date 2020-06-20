open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
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
open import Agda.Primitive using (Level; lzero; lsuc)

module Fold (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig

Bind : {ℓᶜ : Level} → Set → Set ℓᶜ → ℕ → Set ℓᶜ
Bind V C zero = C
Bind V C (suc b) = V → Bind V C b

module Reify {ℓ : Level} (V : Set) (C : Set ℓ) (var→val : Var → V) where
  reify : {b : ℕ} → Bind V C b → C
  reify {zero} M = M
  reify {suc b} f = reify {b} (f (var→val 0))

  reify-arg : {b : ℕ} → Bind V ABT b → Arg b
  reify-arg {zero} M = ast M
  reify-arg {suc b} f = bind (reify-arg {b} (f (var→val 0)))

  reify-args : {bs : List ℕ} → Tuple bs (Bind V ABT) → Args bs
  reify-args {[]} tt = nil
  reify-args {b ∷ bs} ⟨ r , rs ⟩ = cons (reify-arg r) (reify-args rs)

{-------------------------------------------------------------------------------
 Folding over an abstract binding tree
 ------------------------------------------------------------------------------}

record Foldable {ℓᶜ : Level}(V : Set)(C : Set ℓᶜ) : Set (lsuc ℓᶜ) where
  field ret : V → C
        fold-op : (op : Op) → Tuple (sig op) (Bind V C) → C


{- FoldEnv is abstract with respect to the environment -}
record FoldEnv  {ℓᶜ : Level}(E V : Set)(C : Set ℓᶜ) : Set (lsuc ℓᶜ) where
  field is-Foldable : Foldable V C
  open Foldable is-Foldable public
  field is-Env : Env E V
  open Env is-Env public

  fold : E → ABT → C
  fold-arg : E → {b : ℕ} → Arg b → Bind V C b
  fold-args : E → {bs : List ℕ} → Args bs → Tuple bs (Bind V C)

  fold σ (` x) = ret (lookup σ x)
  fold σ (op ⦅ args ⦆) = fold-op op (fold-args σ {sig op} args)
  fold-arg σ {zero} (ast M) = fold σ M
  fold-arg σ {suc b} (bind arg) v = fold-arg (σ , v) arg
  fold-args σ {[]} nil = tt
  fold-args σ {b ∷ bs} (cons arg args) = ⟨ fold-arg σ arg , fold-args σ args ⟩


{- Fold instantiates FoldEnv using substitutions for the environment -}
record Fold {ℓᶜ : Level}(V : Set)(C : Set ℓᶜ) : Set (lsuc ℓᶜ) where
  field is-Foldable : Foldable V C
  open Foldable is-Foldable public
  field V-is-Shiftable : Shiftable V

  GSubst-is-FoldEnv : FoldEnv (GSubst V) V C
  GSubst-is-FoldEnv = record { is-Foldable = is-Foldable
                             ; is-Env = GSubst-is-Env {{V-is-Shiftable}} }
  open FoldEnv GSubst-is-FoldEnv using (fold; fold-arg; fold-args) public
  open Env (GSubst-is-Env {{V-is-Shiftable}}) hiding (V-is-Shiftable) public

{-------------------------------------------------------------------------------
 Simulation between two folds
 ------------------------------------------------------------------------------}

module RelBind {ℓ : Level}{V₁}{C₁ : Set ℓ}{V₂}{C₂ : Set ℓ}
  (_∼_ : V₁ → V₂ → Set) (_≈_ : C₁ → C₂ → Set ℓ) where
  _⩳_  : (Bind V₁ C₁) ✖ (Bind V₂ C₂)
  _⩳_ {zero} c₁ c₂ = c₁ ≈ c₂
  _⩳_ {suc b} r₁ r₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → r₁ v₁ ⩳ r₂ v₂

record Similar {V₁ C₁ V₂ C₂} (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂) : Set₁ where
  open Fold {{...}}
  instance _ : Fold V₁ C₁ ; _ = F₁ ; _ : Fold V₂ C₂ ; _ = F₂
  open Shiftable {{...}}
  instance _ : Shiftable V₁ ; _ = V-is-Shiftable
           _ : Shiftable V₂ ; _ = V-is-Shiftable

  field _∼_ : V₁ → V₂ → Set
        _≈_ : C₁ → C₂ → Set
        ret≈ : ∀{v₁ : V₁}{v₂ : V₂} → v₁ ∼ v₂ → ret v₁ ≈ ret v₂
        vars∼ : ∀{x} → var→val x ∼ var→val x
        var→val∼ : ∀ x → var→val x ∼ var→val x
        shift∼ : ∀{v₁ : V₁}{v₂ : V₂} → v₁ ∼ v₂ → shift v₁ ∼ shift v₂
  open RelBind _∼_ _≈_ using (_⩳_) 
  open Relate {V₁}{V₂} V-is-Shiftable V-is-Shiftable _∼_ var→val∼ shift∼ 
  field op≈ : ∀{op}{rs₁ : Tuple (sig op) (Bind V₁ C₁)}{rs₂}
            → zip _⩳_ rs₁ rs₂ → fold-op op rs₁ ≈ fold-op op rs₂
  
  sim : ∀{σ₁ σ₂}
     → (M : ABT)
     → σ₁ ≊ σ₂
     → (Fold.fold F₁ σ₁ M) ≈ (Fold.fold F₂ σ₂ M)
     
  sim-arg : ∀{σ₁}{σ₂}{b} (arg : Arg b)
     → σ₁ ≊ σ₂ → (Fold.fold-arg F₁ σ₁ {b} arg) ⩳ (Fold.fold-arg F₂ σ₂ {b} arg)
  sim-args : ∀{σ₁}{σ₂}{bs} (args : Args bs)
     → σ₁ ≊ σ₂ → zip _⩳_ (Fold.fold-args F₁ σ₁ {bs} args)
                         (Fold.fold-args F₂ σ₂ {bs} args)

  sim (` x) σ₁~σ₂ = ret≈ (g-lookup x σ₁~σ₂)
  sim {σ₁}{σ₂} (op ⦅ args ⦆) σ₁~σ₂ =
    op≈ (sim-args {bs = sig op} args σ₁~σ₂)
  sim-arg {b = zero} (ast M) σ₁≊σ₂ = sim M σ₁≊σ₂
  sim-arg {b = suc b} (bind arg) σ₁≊σ₂ v₁∼v₂ =
      sim-arg {b = b} arg (r-cons v₁∼v₂ (g-inc-≊ σ₁≊σ₂))
  sim-args {bs = []} args σ₁≊σ₂ = tt
  sim-args {bs = b ∷ bs} (cons arg args) σ₁≊σ₂ =
      ⟨ sim-arg arg σ₁≊σ₂ , sim-args args σ₁≊σ₂ ⟩

