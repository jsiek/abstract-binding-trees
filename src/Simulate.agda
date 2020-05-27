{---------------------------------------

   Simulation between two folds

   sim : ∀{M}{σ₁ σ₂}
      → σ₁ ≊ σ₂
      → (fold₁ σ₁ M) ≈ (fold₂ σ₂ M)

 ---------------------------------------}

module Simulate where

import AbstractBindingTree
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Fold

module SimArgResult {Op : Set}{sig : Op → List ℕ}{V₁ C₁ : Set} {V₂ C₂ : Set}
  (_∼_ : V₁ → V₂ → Set) (_≈_ : C₁ → C₂ → Set) where
  
  open ArgResult V₁ C₁ renaming (ArgRes to ArgRes₁; ArgsRes to ArgsRes₁;
      rnil to rnil₁; rcons to rcons₁) public
  open ArgResult V₂ C₂ renaming (ArgRes to ArgRes₂; ArgsRes to ArgsRes₂;
      rnil to rnil₂; rcons to rcons₂) public
  
  ArgRes∼ : ∀ {b} → ArgRes₁ b → ArgRes₂ b → Set 
  ArgRes∼ {zero} c₁ c₂ = c₁ ≈ c₂
  ArgRes∼ {suc b} f₁ f₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → ArgRes∼ (f₁ v₁) (f₂ v₂)
  
  data ArgsRes∼ : {bs : List ℕ} → ArgsRes₁ bs → ArgsRes₂ bs → Set where
    rnil∼ : ArgsRes∼ rnil₁ rnil₂
    rcons∼ : ∀{b bs}{r₁ rs₁}{r₂ rs₂}
        → ArgRes∼ r₁ r₂
        → ArgsRes∼ rs₁ rs₂
        → ArgsRes∼ {b ∷ bs} (rcons₁ r₁ rs₁) (rcons₂ r₂ rs₂)

record RelatedEnv {V₁ Env₁}{V₂ Env₂}
  (_∼_ : V₁ → V₂ → Set)
  (E₁ : EnvSig Env₁ V₁) (E₂ : EnvSig Env₂ V₂)
  : Set₁ where
  open EnvSig E₁ renaming (lookup to lookup₁; extend to ext₁)
  open EnvSig E₂ renaming (lookup to lookup₂; extend to ext₂)
  field _≊_ : Env₁ → Env₂ → Set
  field lookup∼ : ∀ {σ₁ σ₂} → σ₁ ≊ σ₂ → ∀{x} → lookup₁ σ₁ x ∼ lookup₂ σ₂ x
  field extend≊ : ∀ {v₁ v₂ σ₁ σ₂} → v₁ ∼ v₂ → σ₁ ≊ σ₂ → ext₁ σ₁ v₁ ≊ ext₂ σ₂ v₂
  
record Related {Op sig}{V₁ C₁ Env₁} {V₂ C₂ Env₂}
  (F₁ : Foldable V₁ C₁ Op sig Env₁)
  (F₂ : Foldable V₂ C₂ Op sig Env₂)
  : Set₁ where
  field _∼_ : V₁ → V₂ → Set
  field _≈_ : C₁ → C₂ → Set
  field env∼ : RelatedEnv _∼_ (Foldable.env F₁) (Foldable.env F₂)
  open RelatedEnv env∼ public
  open SimArgResult {Op}{sig} _∼_ _≈_
  open Foldable F₁
      renaming (fold-free-var to ffvar₁; ret to ret₁; fold-op to fop₁)
  open Foldable F₂
      renaming (fold-free-var to ffvar₂; ret to ret₂; fold-op to fop₂)
  field ret≈ : ∀{v₁ v₂} → v₁ ∼ v₂ → ret₁ v₁ ≈ ret₂ v₂
  field vars∼ : ∀{x} → ffvar₁ x ∼ ffvar₂ x
  field op∼ : ∀{op}{Rs₁}{Rs₂} → ArgsRes∼ Rs₁ Rs₂ → fop₁ op Rs₁ ≈ fop₂ op Rs₂

module Simulator {Op sig}{V₁ C₁ Env₁} {V₂ C₂ Env₂}
  (F₁ : Foldable V₁ C₁ Op sig Env₁)
  (F₂ : Foldable V₂ C₂ Op sig Env₂)
  (R : Related F₁ F₂)
  where

  open Folder F₁
     renaming (fold to fold₁; fold-arg to fold-arg₁; fold-args to fold-args₁)
  open Folder F₂
     renaming (fold to fold₂; fold-arg to fold-arg₂; fold-args to fold-args₂)

  open Related R
  open SimArgResult {Op}{sig} _∼_ _≈_

  open AbstractBindingTree Op sig

  sim : ∀{M}{σ₁ σ₂}
     → σ₁ ≊ σ₂
     → (fold₁ σ₁ M) ≈ (fold₂ σ₂ M)
  sim-arg : ∀{σ₁}{σ₂}{b}{arg : Arg b}
     → σ₁ ≊ σ₂
     → ArgRes∼ (fold-arg₁ σ₁ arg) (fold-arg₂ σ₂ arg)
  sim-args : ∀{σ₁}{σ₂}{bs}{args : Args bs}
     → σ₁ ≊ σ₂
     → ArgsRes∼ (fold-args₁ σ₁ args) (fold-args₂ σ₂ args)
  sim {` x} {σ₁} {σ₂} σ₁~σ₂ = ret≈ (lookup∼ σ₁~σ₂)
  sim {op ⦅ args ⦆}{σ₁}{σ₂} σ₁~σ₂ = op∼ (sim-args {args = args} σ₁~σ₂)
  sim-arg {σ₁} {σ₂} {zero} {ast M} σ₁≊σ₂ = sim {M} σ₁≊σ₂ 
  sim-arg {σ₁} {σ₂} {suc b} {bind arg} σ₁≊σ₂ {v₁}{v₂} v₁∼v₂ =
     sim-arg {b = b}{arg = arg} (extend≊ v₁∼v₂ σ₁≊σ₂)
  sim-args {σ₁} {σ₂} {[]} {nil} σ₁≊σ₂ = rnil∼
  sim-args {σ₁} {σ₂} {b ∷ bs} {cons A As} σ₁≊σ₂ =
    let sa = sim-arg {arg = A} σ₁≊σ₂ in
    rcons∼ sa (sim-args {σ₁} {σ₂} {bs} {As} σ₁≊σ₂)

