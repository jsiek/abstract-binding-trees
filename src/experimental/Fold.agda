{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Size using (Size)
open import Var
open import experimental.ScopedTuple
    using (Tuple; map; _✖_; zip; zip-refl; map-pres-zip; map-compose-zip;
           map-compose; zip-map→rel; Lift-Eq-Tuple; Lift-Rel-Tuple; zip→rel)
open import GenericSubstitution

module experimental.Fold (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig

Bind : Set → Set → ℕ → Set
Bind V C zero = C
Bind V C (suc b) = V → Bind V C b

module Reify (V C : Set) (var→val : Var → V) where
  reify : {b : ℕ} → Bind V C b → C
  reify {zero} M = M
  reify {suc b} f = reify {b} (f (var→val 0))

{-------------------------------------------------------------------------------
 Folding over an abstract binding tree
 ------------------------------------------------------------------------------}

record Fold (V C : Set) : Set where
  field ret : V → C
        fold-op : (op : Op) → Tuple (sig op) (Bind V C) → C
        var→val : Var → V
        shift : V → V
        var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x)
        
  open GenericSubst V var→val shift var→val-suc-shift public

  fold : ∀{s : Size} → Substitution V → Term s → C
  fold-arg : ∀{s : Size} → Substitution V → {b : ℕ} → Term s → Bind V C b

  fold σ (` x) = ret (⧼ σ ⧽ x)
  fold σ (op ⦅ args ⦆) = fold-op op (map (fold-arg σ) args)
  fold-arg σ {zero} M = fold σ M
  fold-arg σ {suc b} M v = fold-arg (g-extend v σ) M

{-------------------------------------------------------------------------------
 Simulation between two folds
 ------------------------------------------------------------------------------}

module RelAux {V₁ C₁}{V₂ C₂} (_∼_ : V₁ → V₂ → Set) (_≈_ : C₁ → C₂ → Set) where
  data _≊_ : Substitution V₁ → Substitution V₂ → Set where
     r-up : ∀{k} → (↑ k) ≊ (↑ k)
     r-cons : ∀{v₁ σ₁ v₂ σ₂}
        → v₁ ∼ v₂  →   σ₁ ≊ σ₂
        → (v₁ • σ₁) ≊ (v₂ • σ₂)

  _⩳_  : (Bind V₁ C₁) ✖ (Bind V₂ C₂)
  _⩳_ {zero} c₁ c₂ = c₁ ≈ c₂
  _⩳_ {suc b} r₁ r₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → r₁ v₁ ⩳ r₂ v₂

record Related {V₁ C₁} {V₂ C₂} (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂) : Set₁ where
  module ℱ₁ = Fold F₁ ; module ℱ₂ = Fold F₂
  field _∼_ : V₁ → V₂ → Set
        _≈_ : C₁ → C₂ → Set
        ret≈ : ∀{v₁ v₂} → v₁ ∼ v₂ → ℱ₁.ret v₁ ≈ ℱ₂.ret v₂
        vars∼ : ∀{x} → ℱ₁.var→val x ∼ ℱ₂.var→val x
        var→val∼ : ∀{x} → ℱ₁.var→val x ∼ ℱ₂.var→val x
        shift∼ : ∀{v₁ v₂} → v₁ ∼ v₂ → ℱ₁.shift v₁ ∼ ℱ₂.shift v₂
  open RelAux _∼_ _≈_ using (_⩳_)
  field op≈ : ∀{op rs₁ rs₂} → zip _⩳_ rs₁ rs₂
            → ℱ₁.fold-op op rs₁ ≈ ℱ₂.fold-op op rs₂
  
module Simulate {V₁ C₁ V₂ C₂} (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂)
  (R : Related F₁ F₂) where
  module FF₁ = Fold F₁ ; module FF₂ = Fold F₂
  open Related R ; open RelAux _∼_ _≈_ using (_≊_; r-up; r-cons; _⩳_)
  module GS₁ = GenericSubst V₁ FF₁.var→val FF₁.shift FF₁.var→val-suc-shift
  module GS₂ = GenericSubst V₂ FF₂.var→val FF₂.shift FF₂.var→val-suc-shift
  
  lookup∼ : {σ₁ : Substitution V₁} {σ₂ : Substitution V₂} →
      σ₁ ≊ σ₂ → {x : ℕ} → GS₁.⧼ σ₁ ⧽ x ∼ GS₂.⧼ σ₂ ⧽ x
  lookup∼ (r-up{k}) {x} = var→val∼
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {zero} = v₁∼v₂
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {suc x} = lookup∼ σ₁≊σ₂

  extend-≊ : ∀ {σ₁ σ₂}
    → σ₁ ≊ σ₂
    → GS₁.g-inc σ₁ ≊ GS₂.g-inc σ₂
  extend-≊ {.(↑ _)} {.(↑ _)} r-up = r-up
  extend-≊ {.(_ • _)} {.(_ • _)} (r-cons v₁~v₂ σ₁≊σ₂) =
      r-cons (shift∼ v₁~v₂) (extend-≊ σ₁≊σ₂)

  sim : ∀{s : Size}{σ₁ σ₂}
     → (M : Term s) → σ₁ ≊ σ₂ → (FF₁.fold σ₁ M) ≈ (FF₂.fold σ₂ M)
  sim-arg : ∀{s : Size}{σ₁}{σ₂}{b} (M : Term s)
     → σ₁ ≊ σ₂ → (FF₁.fold-arg σ₁ {b} M) ⩳ (FF₂.fold-arg σ₂ {b} M)

  sim {s} (` x) σ₁~σ₂ = ret≈ (lookup∼ σ₁~σ₂)
  sim {s}{σ₁}{σ₂} (op ⦅ args ⦆) σ₁~σ₂ =
      op≈ (map-pres-zip _≡_ _⩳_ (FF₁.fold-arg σ₁) (FF₂.fold-arg σ₂)
              (zip-refl args) (λ{ {b}{arg} refl → sim-arg {b = b} arg σ₁~σ₂}))
  sim-arg {s} {b = zero} M σ₁≊σ₂ = sim {s} M σ₁≊σ₂
  sim-arg {s} {b = suc b} arg σ₁≊σ₂ v₁∼v₂ =
      sim-arg {b = b} arg (r-cons v₁∼v₂ (extend-≊ σ₁≊σ₂))

{-------------------------------------------------------------------------------
 Fusion of two folds (relational version a la AACMM)
 ------------------------------------------------------------------------------}

record Fusable {V₁ C₁ V₂ C₂ V₃ C₃ : Set}
  (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂) (F₃ : Fold V₃ C₃) : Set₁ where
  module 𝐹₁ = Fold F₁ ; module 𝐹₂ = Fold F₂ ; module 𝐹₃ = Fold F₃
  field “_” : C₁ → ABT
        _⨟_≈_ : Substitution V₁ → Substitution V₂ → Substitution V₃ → Set
        _≃_ : V₂ → V₃ → Set
        _⩯_ : C₂ → C₃ → Set
        ret⩯ : ∀{s : Size}{x σ₁ σ₂ σ₃} → σ₁ ⨟ σ₂ ≈ σ₃
             → 𝐹₂.fold σ₂ “ 𝐹₁.ret (𝐹₁.⧼ σ₁ ⧽ x) ” ⩯ 𝐹₃.ret (𝐹₃.⧼ σ₃ ⧽ x)
        ext≈ : ∀{σ₁ σ₂ σ₃ v₂ v₃}
             → σ₁ ⨟ σ₂ ≈ σ₃   →   v₂ ≃ v₃
             → (𝐹₁.var→val 0 • 𝐹₁.g-inc σ₁) ⨟ (v₂ • 𝐹₂.g-inc σ₂) ≈ (v₃ • 𝐹₃.g-inc σ₃)
  module R1 = Reify V₁ C₁ 𝐹₁.var→val
  open RelAux _≃_ _⩯_ 
  field op⩯ : ∀{s : Size}{σ₁ σ₂ σ₃ op}{args : Tuple (sig op) (λ _ → Term s)}
            → zip (λ {b} → _⩳_ {b})
              (map (𝐹₂.fold-arg {Size.∞} σ₂)
                 (map (λ{b} M → “ R1.reify M ”)
                    (map (λ{b} M → 𝐹₁.fold-arg {s} σ₁ {b} M) args)))
              (map (𝐹₃.fold-arg {s} σ₃) args)
            → 𝐹₂.fold σ₂ “ 𝐹₁.fold-op op (map (𝐹₁.fold-arg {s} σ₁) args) ”
              ⩯ 𝐹₃.fold-op op (map (𝐹₃.fold-arg {s} σ₃) args)

module Fuse {V₁ C₁ V₂ C₂ V₃ C₃ : Set}
  (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂) (F₃ : Fold V₃ C₃)
  (Fus : Fusable F₁ F₂ F₃) where
  open Fusable Fus
  open RelAux _≃_ _⩯_

  fusion : ∀{s}{M : Term s}{σ₁ σ₂ σ₃}
     → σ₁ ⨟ σ₂ ≈ σ₃
     → (𝐹₂.fold σ₂ “ 𝐹₁.fold σ₁ M ”) ⩯ (𝐹₃.fold σ₃ M)
  fusion-arg : ∀{s}{σ₁ σ₂ σ₃}
     → σ₁ ⨟ σ₂ ≈ σ₃
     → ∀ {b : ℕ} (M : Term s)
     → _⩳_ {b} (𝐹₂.fold-arg σ₂ {b} “ (R1.reify (𝐹₁.fold-arg σ₁ {b} M)) ”)
               (𝐹₃.fold-arg σ₃ {b} M)

  fusion {.(Size.↑ _)} {` x} {σ₁} {σ₂} {σ₃} σ≈ = ret⩯ σ≈
  fusion {.(Size.↑ s)} {_⦅_⦆ {s} op args} {σ₁} {σ₂} {σ₃} σ≈
      with map-compose-zip {g = λ{b} → 𝐹₂.fold-arg σ₂{b}}
              {f = (λ{b} M → “ R1.reify (𝐹₁.fold-arg {s} σ₁ {b} M) ”)}
              {h = 𝐹₃.fold-arg σ₃}
              {R = _⩳_}{xs = args} (λ {b} M → fusion-arg {s} σ≈ {b} M)
  ... | mcz
      rewrite sym (map-compose {g = λ {b} r → “ R1.reify r ”}
                          {f = λ{b}→ 𝐹₁.fold-arg σ₁{b}}{xs = args}) = 
      op⩯ mcz

  fusion-arg {s} {σ₁} {σ₂} {σ₃} σ≈ {zero} M = fusion {s}{M} σ≈
  fusion-arg {s} {σ₁} {σ₂} {σ₃} σ≈ {suc b} M {v₂}{v₃} v₂~v₃ =
      fusion-arg (ext≈ σ≈ v₂~v₃) {b = b} M

