open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Env using (EnvI)
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
    renaming (_⊔_ to _⊔'_)

module Fold (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig

Bind : {ℓᶜ : Level} → Set → Set ℓᶜ → ℕ → Set ℓᶜ
Bind V C zero = C
Bind V C (suc b) = V → Bind V C b

module Reify {ℓ : Level} (V : Set) (C : Set ℓ) (var→val : Var → V) where
  reify : {b : ℕ} → Bind V C b → C
  reify {zero} M = M
  reify {suc b} f = reify {b} (f (var→val 0))

{-------------------------------------------------------------------------------
 Folding over an abstract binding tree
 ------------------------------------------------------------------------------}

{- FoldEnv is abstract with respect to the environment -}
record FoldEnv  {ℓᶜ : Level}(Env V : Set)(C : Set ℓᶜ) : Set (lsuc ℓᶜ) where
  field ret : V → C
        fold-op : (op : Op) → Tuple (sig op) (Bind V C) → C
        env : Env.EnvI V Env
  open EnvI env public
        
  fold : Env → ABT → C
  fold-arg : Env → {b : ℕ} → Arg b → Bind V C b
  fold-args : Env → {bs : List ℕ} → Args bs → Tuple bs (Bind V C)

  fold σ (` x) = ret (lookup σ x)
  fold σ (op ⦅ args ⦆) = fold-op op (fold-args σ {sig op} args)
  fold-arg σ {zero} (ast M) = fold σ M
  fold-arg σ {suc b} (bind arg) v = fold-arg (σ , v) arg
  fold-args σ {[]} nil = tt
  fold-args σ {b ∷ bs} (cons arg args) = ⟨ fold-arg σ arg , fold-args σ args ⟩

{- Fold instantiates FoldEnv using substitutions for the environment -}
record Fold {ℓᶜ : Level}(V : Set)(C : Set ℓᶜ) : Set (lsuc ℓᶜ) where
  field S : Shiftable V
        ret : V → C
        fold-op : (op : Op) → Tuple (sig op) (Bind V C) → C
  open Env.GSubstIsEnv V S public
  FE : FoldEnv (GSubst V) V C
  FE = record { ret = ret ; fold-op = fold-op ; env = GSubstIsEnv }
  open FoldEnv FE using (fold; fold-arg; fold-args) public

{-------------------------------------------------------------------------------
 Simulation between two folds
 ------------------------------------------------------------------------------}

module RelBind {V₁ C₁}{V₂ C₂} (_∼_ : V₁ → V₂ → Set) (_≈_ : C₁ → C₂ → Set) where
  _⩳_  : (Bind V₁ C₁) ✖ (Bind V₂ C₂)
  _⩳_ {zero} c₁ c₂ = c₁ ≈ c₂
  _⩳_ {suc b} r₁ r₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → r₁ v₁ ⩳ r₂ v₂

record Similar {V₁ C₁ V₂ C₂} (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂) : Set₁ where
  module 𝐹₁ = Fold F₁ ; module 𝐹₂ = Fold F₂
  module S₁ = Shiftable 𝐹₁.S ; module S₂ = Shiftable 𝐹₂.S
  field _∼_ : V₁ → V₂ → Set
        _≈_ : C₁ → C₂ → Set
        ret≈ : ∀{v₁ v₂} → v₁ ∼ v₂ → 𝐹₁.ret v₁ ≈ 𝐹₂.ret v₂
        vars∼ : ∀{x} → S₁.var→val x ∼ S₂.var→val x
        var→val∼ : ∀ x → S₁.var→val x ∼ S₂.var→val x
        shift∼ : ∀{v₁ v₂} → v₁ ∼ v₂ → S₁.shift v₁ ∼ S₂.shift v₂
  open RelBind _∼_ _≈_ using (_⩳_) public
  open Relate 𝐹₁.S 𝐹₂.S _∼_ var→val∼ shift∼ public
  field op≈ : ∀{op rs₁ rs₂} → zip _⩳_ rs₁ rs₂
            → 𝐹₁.fold-op op rs₁ ≈ 𝐹₂.fold-op op rs₂
  
  sim : ∀{σ₁ σ₂}
     → (M : ABT) → σ₁ ≊ σ₂ → (Fold.fold F₁ σ₁ M) ≈ (Fold.fold F₂ σ₂ M)
  sim-arg : ∀{σ₁}{σ₂}{b} (arg : Arg b)
     → σ₁ ≊ σ₂ → (Fold.fold-arg F₁ σ₁ {b} arg) ⩳ (Fold.fold-arg F₂ σ₂ {b} arg)
  sim-args : ∀{σ₁}{σ₂}{bs} (args : Args bs)
     → σ₁ ≊ σ₂ → zip _⩳_ (Fold.fold-args F₁ σ₁ {bs} args)
                         (Fold.fold-args F₂ σ₂ {bs} args)

  sim (` x) σ₁~σ₂ = ret≈ (g-lookup x σ₁~σ₂)
  sim {σ₁}{σ₂} (op ⦅ args ⦆) σ₁~σ₂ = op≈ (sim-args {bs = sig op} args σ₁~σ₂)
  sim-arg {b = zero} (ast M) σ₁≊σ₂ = sim M σ₁≊σ₂
  sim-arg {b = suc b} (bind arg) σ₁≊σ₂ v₁∼v₂ =
      sim-arg {b = b} arg (r-cons v₁∼v₂ (g-inc-≊ σ₁≊σ₂))
  sim-args {bs = []} args σ₁≊σ₂ = tt
  sim-args {bs = b ∷ bs} (cons arg args) σ₁≊σ₂ =
      ⟨ sim-arg arg σ₁≊σ₂ , sim-args args σ₁≊σ₂ ⟩

