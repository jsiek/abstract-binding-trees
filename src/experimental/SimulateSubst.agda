module SimulateSubst where

import AbstractBindingTree
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Fold
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
import Rename
open import Simulate
open import GenericSubstitution
open SNF
open import Var

module RelGenericSubst (V₁ V₂ : Set) (_∼_ : V₁ → V₂ → Set) where
  data _≊_ : Substitution V₁ → Substitution V₂ → Set where
     r-up : ∀{k} → (↑ k) ≊ (↑ k)
     r-cons : ∀{v₁ σ₁ v₂ σ₂}
        → v₁ ∼ v₂  →   σ₁ ≊ σ₂
        → (v₁ • σ₁) ≊ (v₂ • σ₂)


module RelateSub (V₁ V₂ : Set)
  (_∼_ : V₁ → V₂ → Set)
  (var→val₁ : Var → V₁)
  (shift₁ : V₁ → V₁)
  (var→val₂ : Var → V₂)
  (shift₂ : V₂ → V₂)
  (var→val∼ : ∀{x} → var→val₁ x ∼ var→val₂ x)
  (shift∼ : ∀ {v₁ v₂} → v₁ ∼ v₂ → shift₁ v₁ ∼ shift₂ v₂)
  where

  open GenericSub V₁ var→val₁ shift₁
     renaming (⧼_⧽ to ⧼_⧽₁; gen-subst-is-env to subst-is-env₁; gen-inc to inc₁)
  open GenericSub V₂ var→val₂ shift₂
     renaming (⧼_⧽ to ⧼_⧽₂; gen-subst-is-env to subst-is-env₂; gen-inc to inc₂)
  open RelGenericSubst V₁ V₂ _∼_

  lookup∼ : {σ₁ : Substitution V₁} {σ₂ : Substitution V₂} →
      σ₁ ≊ σ₂ → {x : ℕ} → ⧼ σ₁ ⧽₁ x ∼ ⧼ σ₂ ⧽₂ x
  lookup∼ (r-up{k}) {x} = var→val∼
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {zero} = v₁∼v₂
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {suc x} = lookup∼ σ₁≊σ₂

  ≊-inc : ∀{σ₁}{σ₂}
    → σ₁ ≊ σ₂
    → (inc₁ σ₁) ≊ (inc₂ σ₂)
  ≊-inc {.(↑ _)} {.(↑ _)} r-up = r-up
  ≊-inc {.(_ • _)} {.(_ • _)} (r-cons v₁∼v₂ σ₁≊σ₂) = r-cons (shift∼ v₁∼v₂) (≊-inc σ₁≊σ₂)

  sub-is-rel-env : RelatedEnv _∼_ subst-is-env₁ subst-is-env₂
  sub-is-rel-env = record { _≊_ = _≊_ ; lookup∼ = lookup∼ ;
                    extend≊ = λ v₁∼v₂ σ₁≊σ₂ → r-cons v₁∼v₂ (≊-inc σ₁≊σ₂) }

module SubstSubst
  (Op : Set) (sig : Op → List ℕ) 
  (V₁ V₂ : Set)
  (_∼_ : V₁ → V₂ → Set)
  (var→val₁ : Var → V₁)
  (shift₁ : V₁ → V₁)
  (val→abt₁ : V₁ → AbstractBindingTree.ABT Op sig)
  (var→val₂ : Var → V₂)
  (shift₂ : V₂ → V₂)
  (val→abt₂ : V₂ → AbstractBindingTree.ABT Op sig)
  (var→val∼ : ∀{x} → var→val₁ x ∼ var→val₂ x)
  (shift∼ : ∀ {v₁ v₂} → v₁ ∼ v₂ → shift₁ v₁ ∼ shift₂ v₂)
  (val→abt∼ : ∀{v₁ v₂} → v₁ ∼ v₂ → val→abt₁ v₁ ≡ val→abt₂ v₂)
  (val→abt∘var→val₁ : ∀ x → val→abt₁ (var→val₁ x) ≡ AbstractBindingTree.`_ x)
  (val→abt∘var→val₂ : ∀ x → val→abt₂ (var→val₂ x) ≡ AbstractBindingTree.`_ x)
  where

  _≈_ = _≡_

  open AbstractBindingTree Op sig
  open RelGenericSubst V₁ V₂ _∼_
  open RelateSub V₁ V₂ _∼_ var→val₁ shift₁ var→val₂ shift₂ var→val∼ shift∼
  open SimArgResult {Op}{sig}{V₁}{ABT}{V₂}{ABT} _∼_ _≈_
  open GenericSubst V₁ var→val₁ shift₁ Op sig val→abt₁ 
      renaming (gen-subst to gen-subst₁;
          gen-subst-is-foldable to gsubst-foldable₁;
          s-arg to s-arg₁; s-args to s-args₁)
  open GenericSubst V₂ var→val₂ shift₂ Op sig val→abt₂ 
      renaming (gen-subst to gen-subst₂;
          gen-subst-is-foldable to gsubst-foldable₂;
          s-arg to s-arg₂; s-args to s-args₂)
  open Foldable gsubst-foldable₁ renaming (fold-op to fop₁)
  open Foldable gsubst-foldable₂ renaming (fold-op to fop₂)

  op∼ : ∀{op : Op}{Rs₁ : ArgsRes₁ (sig op)}{Rs₂ : ArgsRes₂ (sig op)}
         → ArgsRes∼ Rs₁ Rs₂
         → fop₁ op Rs₁ ≈ fop₂ op Rs₂
  op∼ {op}{Rs₁}{Rs₂} rs∼ = G
    where
    I : ∀{b}{R₁ : ArgRes₁ b}{R₂ : ArgRes₂ b} → ArgRes∼ R₁ R₂
       → s-arg₁ R₁ ≡ s-arg₂ R₂
    I {zero} {R₁} {.R₁} refl = refl
    I {suc b} {R₁} {R₂} r~ = cong bind (I (r~ var→val∼))
    
    H : ∀{bs}{Rs₁ : ArgsRes₁ bs}{Rs₂ : ArgsRes₂ bs} → ArgsRes∼ Rs₁ Rs₂
       → s-args₁ Rs₁ ≡ s-args₂ Rs₂
    H {[]} {rnil₁} {rnil₂} rnil∼ = refl
    H {b ∷ bs} {rcons₁ r₁ Rs₁} {rcons₂ r₂ Rs₂} (rcons∼ r∼ rs∼) =
        cong₂ cons (I r∼) (H rs∼)

    G : op ⦅ s-args₁ Rs₁ ⦆ ≡ op ⦅ s-args₂ Rs₂ ⦆
    G = cong (_⦅_⦆ op) (H rs∼)

  SubSubRel : Related gsubst-foldable₁ gsubst-foldable₂
  SubSubRel = record { _∼_ = _∼_ ; _≈_ = _≈_ ; env∼ = sub-is-rel-env ;
         ret≈ = λ {v₁} {v₂} v₁∼v₂ → val→abt∼ v₁∼v₂ ; vars∼ = λ {x} → var→val∼ ;
         op∼ = op∼ }

  module Sim = Simulator gsubst-foldable₁ gsubst-foldable₂ SubSubRel

  subsub-sim : ∀{σ₁}{σ₂} (M : ABT) → σ₁ ≊ σ₂ → gen-subst₁ σ₁ M ≡ gen-subst₂ σ₂ M
  subsub-sim M = Sim.sim {M = M}


module RenameSubst (Op : Set) (sig : Op → List ℕ) where

  open AbstractBindingTree Op sig using (ABT; `_; _⦅_⦆; cons; bind)
  open Rename Op sig hiding (↑; _•_)
  open import Subst Op sig hiding (↑; _•_)
  _∼_ = λ x M → ` x ≡ M
  open SubstSubst Op sig Var ABT _∼_ (λ x → x) suc `_ `_ (rename (↑ 1)) 
        (λ M → M) (λ {x} → refl) (λ { refl → refl } ) (λ { refl → refl })
        (λ x → refl) (λ x → refl)
  open RelGenericSubst Var ABT _∼_
  
  rename→subst : Rename → Subst
  rename→subst (↑ k) = ↑ k 
  rename→subst (x • ρ) = ` x • rename→subst ρ

  rename→subst-≊ : ∀{ρ} → ρ ≊ rename→subst ρ
  rename→subst-≊ {↑ k} = r-up
  rename→subst-≊ {x • ρ} = r-cons refl rename→subst-≊

  rename-subst : ∀ ρ M → rename ρ M ≡ ⟪ rename→subst ρ ⟫ M
  rename-subst ρ M = subsub-sim M (rename→subst-≊ {ρ})

