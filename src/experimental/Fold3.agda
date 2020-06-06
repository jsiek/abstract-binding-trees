open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Size using (Size)
open import Var
open import experimental.ScopedTuple
open import Syntax

module experimental.Fold3 (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig

Bind : Set → Set → ℕ → Set
Bind V C zero = C
Bind V C (suc b) = V → Bind V C b

record Fold (V C : Set) : Set where
  field ret : V → C
  field fold-op : (op : Op) → Tuple (sig op) (Bind V C) → C
  field var→val : Var → V
  field shift : V → V

  open GenericSubst V var→val shift

  fold : {s : Size} → Substitution V → Term s → C
  fold-arg : Substitution V → {b : ℕ}{s : Size} → Term s → Bind V C b

  fold σ (` x) = ret (⧼ σ ⧽ x)
  fold σ (op ⦅ args ⦆) = fold-op op (map (fold-arg σ) args)
  fold-arg σ {zero} M = fold σ M
  fold-arg σ {suc b} M v = fold-arg (v • σ) {b} M

module Reify (V : Set) (zero-val : V) where

  reify : {b : ℕ} → Bind V ABT b → ABT
  reify {zero} M = M
  reify {suc b} f = reify {b} (f zero-val)

Renaming : Fold Var ABT
Renaming = record { ret = `_ ; var→val = λ x → x ; shift = suc 
                  ; fold-op = λ op rs → op ⦅ map RV.reify rs ⦆ }
    where module RV = Reify Var 0
open Fold Renaming renaming (fold to ren)

Subst : Fold ABT ABT
Subst = record { ret = λ x → x ; var→val = λ x → ` x ; shift = ren (↑ 1) 
               ; fold-op = λ op rs → op ⦅ map RT.reify rs ⦆ }
    where module RT = Reify ABT (` 0)

module RelAux {V₁ C₁}{V₂ C₂} (_∼_ : V₁ → V₂ → Set) (_≈_ : C₁ → C₂ → Set) where
  data _≊_ : Substitution V₁ → Substitution V₂ → Set where
     r-up : ∀{k} → (↑ k) ≊ (↑ k)
     r-cons : ∀{v₁ σ₁ v₂ σ₂}
        → v₁ ∼ v₂  →   σ₁ ≊ σ₂
        → (v₁ • σ₁) ≊ (v₂ • σ₂)
        
  _⩳_  : {b : ℕ} → (Bind V₁ C₁ b) → (Bind V₂ C₂ b) → Set
  _⩳_ {zero} c₁ c₂ = c₁ ≈ c₂
  _⩳_ {suc b} r₁ r₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → r₁ v₁ ⩳ r₂ v₂

record Related {V₁ C₁} {V₂ C₂} (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂) : Set₁ where
  module ℱ₁ = Fold F₁ ; module ℱ₂ = Fold F₂
  field _∼_ : V₁ → V₂ → Set
        _≈_ : C₁ → C₂ → Set
        ret≈ : ∀{v₁ v₂} → v₁ ∼ v₂ → ℱ₁.ret v₁ ≈ ℱ₂.ret v₂
        vars∼ : ∀{x} → ℱ₁.var→val x ∼ ℱ₂.var→val x
        var→val∼ : ∀{x} → ℱ₁.var→val x ∼ ℱ₂.var→val x
  open RelAux _∼_ _≈_ using (_⩳_)
  field op≈ : ∀{op rs₁ rs₂} → zip _⩳_ rs₁ rs₂
            → ℱ₁.fold-op op rs₁ ≈ ℱ₂.fold-op op rs₂
  
module Simulate {V₁ C₁ V₂ C₂} (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂)
  (R : Related F₁ F₂) where
  module FF₁ = Fold F₁ ; module FF₂ = Fold F₂
  open Related R ; open RelAux _∼_ _≈_
  module GS₁ = GenericSubst V₁ FF₁.var→val FF₁.shift
  module GS₂ = GenericSubst V₂ FF₂.var→val FF₂.shift
  
  lookup∼ : {σ₁ : Substitution V₁} {σ₂ : Substitution V₂} →
      σ₁ ≊ σ₂ → {x : ℕ} → GS₁.⧼ σ₁ ⧽ x ∼ GS₂.⧼ σ₂ ⧽ x
  lookup∼ (r-up{k}) {x} = var→val∼
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {zero} = v₁∼v₂
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {suc x} = lookup∼ σ₁≊σ₂

  sim : ∀{s : Size}{M : Term s}{σ₁ σ₂}
     → σ₁ ≊ σ₂ → (FF₁.fold σ₁ M) ≈ (FF₂.fold σ₂ M)
  sim-arg : ∀{s : Size}{σ₁}{σ₂}{b}{arg : Term s}
     → σ₁ ≊ σ₂ → (FF₁.fold-arg σ₁ {b} arg) ⩳ (FF₂.fold-arg σ₂ {b} arg)

  sim {s}{` x} {σ₁} {σ₂} σ₁~σ₂ = ret≈ (lookup∼ σ₁~σ₂)
  sim {s}{op ⦅ args ⦆}{σ₁}{σ₂} σ₁~σ₂ =
      op≈ (map-pres-zip _≡_ _⩳_ (FF₁.fold-arg σ₁) (FF₂.fold-arg σ₂)
               (zip-refl args) (λ { {b} refl → sim-arg {b = b} σ₁~σ₂ }))
  sim-arg {s} {σ₁} {σ₂} {zero} {M} σ₁≊σ₂ = sim {s}{M} σ₁≊σ₂
  sim-arg {s} {σ₁} {σ₂} {suc b} {arg} σ₁≊σ₂ v₁∼v₂ =
      sim-arg {b = b} (r-cons v₁∼v₂ σ₁≊σ₂)

module RelReify (V₁ V₂ : Set) (zero-val₁ : V₁) (zero-val₂ : V₂)
  (_∼_ : V₁ → V₂ → Set) (zero∼ : zero-val₁ ∼ zero-val₂) where
  module R1 = Reify V₁ zero-val₁
  module R2 = Reify V₂ zero-val₂
  open RelAux {C₁ = ABT} _∼_ _≡_

  rel-arg : ∀{b}{r₁ : Bind V₁ ABT b}{r₂ : Bind V₂ ABT b}
     → r₁ ⩳ r₂ → R1.reify {b} r₁ ≡ R2.reify {b} r₂
  rel-arg {zero}{r₁}{r₂} r~ = r~
  rel-arg {suc b} r~ = rel-arg {b} (r~ zero∼)

RenSubRel : Related Renaming Subst
RenSubRel = record
              { _∼_ = λ x M → ` x ≡ M
              ; _≈_ = λ M₁ M₂ → M₁ ≡ M₂
              ; ret≈ = λ { refl → refl }
              ; vars∼ = λ {x} → refl
              ; var→val∼ = λ {x} → refl
              ; op≈ = λ {op} rs≅ → cong (_⦅_⦆ op) (map-reify rs≅)
              }
  where
  module R1 = Reify Var 0 ; module R2 = Reify ABT (` 0)
  open RelAux {C₁ = ABT} (λ x M → _≡_ (` x) M) _≡_ using (_⩳_)
  open RelReify Var ABT 0 (` 0) (λ x M → _≡_ (` x) M) refl using (rel-arg)

  map-reify : ∀{bs}{rs₁  : Tuple bs (Bind Var ABT)}{rs₂}
    → zip _⩳_ rs₁ rs₂  →  map R1.reify rs₁ ≡ map R2.reify rs₂
  map-reify rs≅ = zip-map→rel _⩳_ _≡_ _≡_ R1.reify R2.reify (λ{b}→ rel-arg{b})
                              Lift-Eq-Tuple rs≅

open Simulate Renaming Subst RenSubRel renaming (sim to rensub)
