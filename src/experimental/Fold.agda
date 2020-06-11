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
  field S : Substable V
        ret : V → C
        fold-op : (op : Op) → Tuple (sig op) (Bind V C) → C
        
  open GenericSubst S using (⧼_⧽; g-extend)

  fold : ∀{s : Size} → GSubst V → Term s → C
  fold-arg : ∀{s : Size} → GSubst V → {b : ℕ} → Term s → Bind V C b

  fold σ (` x) = ret (⧼ σ ⧽ x)
  fold σ (op ⦅ args ⦆) = fold-op op (map (fold-arg σ) args)
  fold-arg σ {zero} M = fold σ M
  fold-arg σ {suc b} M v = fold-arg (g-extend v σ) M

{-------------------------------------------------------------------------------
 Simulation between two folds
 ------------------------------------------------------------------------------}

module RelBind {V₁ C₁}{V₂ C₂} (_∼_ : V₁ → V₂ → Set) (_≈_ : C₁ → C₂ → Set) where
  _⩳_  : (Bind V₁ C₁) ✖ (Bind V₂ C₂)
  _⩳_ {zero} c₁ c₂ = c₁ ≈ c₂
  _⩳_ {suc b} r₁ r₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → r₁ v₁ ⩳ r₂ v₂

record Similar {V₁ C₁ V₂ C₂} (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂) : Set₁ where
  module 𝐹₁ = Fold F₁ ; module 𝐹₂ = Fold F₂
  module S₁ = Substable 𝐹₁.S ; module S₂ = Substable 𝐹₂.S
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
  
  sim : ∀{s : Size}{σ₁ σ₂}
     → (M : Term s) → σ₁ ≊ σ₂ → (Fold.fold F₁ σ₁ M) ≈ (Fold.fold F₂ σ₂ M)
  sim-arg : ∀{s : Size}{σ₁}{σ₂}{b} (M : Term s)
     → σ₁ ≊ σ₂ → (Fold.fold-arg F₁ σ₁ {b} M) ⩳ (Fold.fold-arg F₂ σ₂ {b} M)

  sim {s} (` x) σ₁~σ₂ = ret≈ (g-lookup x σ₁~σ₂)
  sim {s}{σ₁}{σ₂} (op ⦅ args ⦆) σ₁~σ₂ =
      op≈ (map-pres-zip _≡_ _⩳_ (Fold.fold-arg F₁ σ₁) (Fold.fold-arg F₂ σ₂)
              (zip-refl args) (λ{ {b}{arg} refl → sim-arg {b = b} arg σ₁~σ₂}))
  sim-arg {s} {b = zero} M σ₁≊σ₂ = sim {s} M σ₁≊σ₂
  sim-arg {s} {b = suc b} arg σ₁≊σ₂ v₁∼v₂ =
      sim-arg {b = b} arg (r-cons v₁∼v₂ (g-inc-≊ σ₁≊σ₂))

{-------------------------------------------------------------------------------
 Fusion of two folds (relational version a la AACMM)

 (I don't recommend using this. The fusion of two folds isn't a
  natural thing. The fusion of two maps makes more sense.)

 ------------------------------------------------------------------------------}

record Fusable {V₁ C₁ V₂ C₂ V₃ C₃ : Set}
  (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂) (F₃ : Fold V₃ C₃) : Set₁ where
  module 𝐹₁ = Fold F₁ ; module 𝐹₂ = Fold F₂ ; module 𝐹₃ = Fold F₃
  module S₁ = Substable 𝐹₁.S ; module S₂ = Substable 𝐹₂.S
  module G₁ = GenericSubst 𝐹₁.S ; module G₂ = GenericSubst 𝐹₂.S
  module G₃ = GenericSubst 𝐹₃.S
  field
     “_” : C₁ → ABT
     _⨟_≈_ : GSubst V₁ → GSubst V₂ → GSubst V₃ → Set
     _≃_ : V₂ → V₃ → Set
     _⩯_ : C₂ → C₃ → Set
     ret⩯ : ∀{s : Size}{x σ₁ σ₂ σ₃} → σ₁ ⨟ σ₂ ≈ σ₃
          → 𝐹₂.fold σ₂ “ 𝐹₁.ret (G₁.⧼ σ₁ ⧽ x) ” ⩯ 𝐹₃.ret (G₃.⧼ σ₃ ⧽ x)
     ext≈ : ∀{σ₁ σ₂ σ₃ v₂ v₃}
        → σ₁ ⨟ σ₂ ≈ σ₃   →   v₂ ≃ v₃
        → (S₁.var→val 0 • G₁.g-inc σ₁) ⨟ (v₂ • G₂.g-inc σ₂) ≈ (v₃ • G₃.g-inc σ₃)
  module R1 = Reify V₁ C₁ S₁.var→val
  open RelBind _≃_ _⩯_ 
  field op⩯ : ∀{s : Size}{σ₁ σ₂ σ₃ op}{args : Tuple (sig op) (λ _ → Term s)}
            → zip (λ {b} → _⩳_ {b})
              (map (𝐹₂.fold-arg {Size.∞} σ₂)
                 (map (λ{b} M → “ R1.reify M ”)
                    (map (λ{b} M → 𝐹₁.fold-arg {s} σ₁ {b} M) args)))
              (map (𝐹₃.fold-arg {s} σ₃) args)
            → 𝐹₂.fold σ₂ “ 𝐹₁.fold-op op (map (𝐹₁.fold-arg {s} σ₁) args) ”
              ⩯ 𝐹₃.fold-op op (map (𝐹₃.fold-arg {s} σ₃) args)

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

