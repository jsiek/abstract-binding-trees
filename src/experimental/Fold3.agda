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
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Size using (Size)
open import Var
open import experimental.ScopedTuple
open import Syntax hiding (⦉_⦊)

module experimental.Fold3 (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig

{-------------------------------------------------------------------------------
 Folding over an abstract binding tree
 ------------------------------------------------------------------------------}

{- Need a btter name for this -}
Bind : Set → Set → ℕ → Set
Bind V C zero = C
Bind V C (suc b) = V → Bind V C b

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
  fold-arg σ {suc b} M v = fold-arg (v • g-inc σ) M

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

  sim : ∀{s : Size}{M : Term s}{σ₁ σ₂}
     → σ₁ ≊ σ₂ → (FF₁.fold σ₁ M) ≈ (FF₂.fold σ₂ M)
  sim-arg : ∀{s : Size}{σ₁}{σ₂}{b}{M : Term s}
     → σ₁ ≊ σ₂ → (FF₁.fold-arg σ₁ {b} M) ⩳ (FF₂.fold-arg σ₂ {b} M)

  sim {s}{` x} {σ₁} {σ₂} σ₁~σ₂ = ret≈ (lookup∼ σ₁~σ₂)
  sim {s}{op ⦅ args ⦆}{σ₁}{σ₂} σ₁~σ₂ =
      op≈ (map-pres-zip _≡_ _⩳_ (FF₁.fold-arg σ₁) (FF₂.fold-arg σ₂)
               (zip-refl args) (λ { {b} refl → sim-arg {b = b} σ₁~σ₂ }))
  sim-arg {s} {σ₁} {σ₂} {zero} {M} σ₁≊σ₂ = sim {s}{M} σ₁≊σ₂
  sim-arg {s} {σ₁} {σ₂} {suc b} {arg} σ₁≊σ₂ v₁∼v₂ =
      sim-arg {b = b} (r-cons v₁∼v₂ (extend-≊ σ₁≊σ₂))

{-------------------------------------------------------------------------------
 Reify a bind into a computation
 ------------------------------------------------------------------------------}

module Reify (V C : Set) (new : V) where
  reify : {b : ℕ} → Bind V C b → C
  reify {zero} M = M
  reify {suc b} f = reify {b} (f new)

{-------------------------------------------------------------------------------
 Fusion of two folds
 ------------------------------------------------------------------------------}

record Fusable {V₁ C₁ V₂ C₂ V₃ C₃ : Set}
  (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂) (F₃ : Fold V₃ C₃) : Set₁ where
  module 𝐹₁ = Fold F₁ ; module 𝐹₂ = Fold F₂ ; module 𝐹₃ = Fold F₃
  field “_” : C₁ → ABT
        _⨟_≈_ : Substitution V₁ → Substitution V₂ → Substitution V₃ → Set
        _≃_ : V₂ → V₃ → Set
        _⩯_ : C₂ → C₃ → Set
        new₁ : V₁
        ret⩯ : ∀{s : Size}{x σ₁ σ₂ σ₃} → σ₁ ⨟ σ₂ ≈ σ₃
             → 𝐹₂.fold σ₂ “ 𝐹₁.ret (𝐹₁.⧼ σ₁ ⧽ x) ” ⩯ 𝐹₃.ret (𝐹₃.⧼ σ₃ ⧽ x)
        ext≈ : ∀{σ₁ σ₂ σ₃ v₂ v₃}
             → σ₁ ⨟ σ₂ ≈ σ₃   →   v₂ ≃ v₃
             → (new₁ • 𝐹₁.g-inc σ₁) ⨟ (v₂ • 𝐹₂.g-inc σ₂) ≈ (v₃ • 𝐹₃.g-inc σ₃)
  module R1 = Reify V₁ C₁ new₁
  open RelAux _≃_ _⩯_ 
  field op⩯ : ∀{s : Size}{σ₁ σ₂ σ₃ op}{args : Tuple (sig op) (λ _ → Term s)}
            → zip (λ {b} → _⩳_ {b})
              (map (λ {b} M → 𝐹₂.fold-arg {Size.∞} σ₂ {b} M)
                 (map (λ {b} M →
                         let x = R1.reify (𝐹₁.fold-arg {s} σ₁ {b} M) in
                         let y = “ x ” in
                         y) args))
              (map (λ {b} M → 𝐹₃.fold-arg {s} σ₃ {b} M) args)
            → 𝐹₂.fold σ₂ “ 𝐹₁.fold-op op (map (λ {b} → 𝐹₁.fold-arg {s} σ₁ {b}) args) ”
              ⩯ 𝐹₃.fold-op op (map (λ {b} → 𝐹₃.fold-arg {s} σ₃ {b}) args)

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
  fusion {.(Size.↑ s)} {_⦅_⦆ {s} op args} {σ₁} {σ₂} {σ₃} σ≈ =
      op⩯ (map-compose (λ {b} M → fusion-arg {s} σ≈ {b} M))
  fusion-arg {s} {σ₁} {σ₂} {σ₃} σ≈ {zero} M = fusion {s}{M} σ≈
  fusion-arg {s} {σ₁} {σ₂} {σ₃} σ≈ {suc b} M {v₂}{v₃} v₂~v₃ =
      fusion-arg (ext≈ σ≈ v₂~v₃) {b = b} M

{-------------------------------------------------------------------------------
 Renaming and substitution
 ------------------------------------------------------------------------------}

Renaming : Fold Var ABT
Renaming = record { ret = `_ ; var→val = λ x → x ; shift = suc 
                  ; fold-op = λ op rs → op ⦅ map RV.reify rs ⦆
                  ; var→val-suc-shift = refl}
    where module RV = Reify Var ABT 0
open Fold Renaming renaming (⧼_⧽ to ⦉_⦊; fold to ren; fold-arg to ren-arg;
    fold-op to ren-op; g-inc to inc; g-inc-shift to inc-suc)

Subst : Fold ABT ABT
Subst = record { ret = λ x → x ; var→val = λ x → ` x ; shift = ren (↑ 1) 
               ; fold-op = λ op rs → op ⦅ map RT.reify rs ⦆
               ; var→val-suc-shift = refl }
    where module RT = Reify ABT ABT (` 0)
open Fold Subst renaming (⧼_⧽ to ⟦_⟧; fold to sub; fold-arg to sub-arg;
    fold-op to sub-op; g-inc to incs; g-inc-shift to incs-rename)


module RelReify {s : Size} (V₁ V₂ : Set) (new₁ : V₁) (new₂ : V₂)
  (_∼_ : V₁ → V₂ → Set) (zero∼ : new₁ ∼ new₂) where
  module R1 = Reify V₁ (Term s) new₁
  module R2 = Reify V₂ (Term s) new₂
  open RelAux {C₁ = (Term s)} _∼_ _≡_

  rel-arg : ∀{b}{r₁ : Bind V₁ (Term s) b}{r₂ : Bind V₂ (Term s) b}
     → r₁ ⩳ r₂ → R1.reify {b} r₁ ≡ R2.reify {b} r₂
  rel-arg {zero}{r₁}{r₂} r~ = r~
  rel-arg {suc b} r~ = rel-arg {b} (r~ zero∼)

module RenSubProps where

  RenSubRel : Related Renaming Subst
  RenSubRel = record
                { _∼_ = λ x M → ` x ≡ M
                ; _≈_ = λ M₁ M₂ → M₁ ≡ M₂
                ; ret≈ = λ { refl → refl }
                ; vars∼ = λ {x} → refl
                ; var→val∼ = λ {x} → refl
                ; op≈ = λ {op} rs≅ → cong (_⦅_⦆ op) (map-reify rs≅)
                ; shift∼ = λ { refl → refl }
                }
    where
    module R1 = Reify Var ABT 0 ; module R2 = Reify ABT ABT (` 0)
    open RelAux {C₁ = ABT} (λ x M → _≡_ (` x) M) _≡_ using (_⩳_)
    open RelReify Var ABT 0 (` 0) (λ x M → _≡_ (` x) M) refl using (rel-arg)

    map-reify : ∀{bs}{rs₁  : Tuple bs (Bind Var ABT)}{rs₂}
      → zip _⩳_ rs₁ rs₂  →  map R1.reify rs₁ ≡ map R2.reify rs₂
    map-reify rs≅ = zip-map→rel _⩳_ _≡_ _≡_ R1.reify R2.reify (λ{b}→ rel-arg{b})
                                Lift-Eq-Tuple rs≅

  open Simulate Renaming Subst RenSubRel using () renaming (sim to rensub)
  open RelAux {C₁ = ABT} (λ x M → _≡_ (` x) M) _≡_ using (_≊_; r-up; r-cons)

  ren→sub : Substitution Var → Substitution ABT
  ren→sub (↑ k) = ↑ k
  ren→sub (x • ρ) = ` x • ren→sub ρ

  ≊-ren→sub : ∀ ρ → ρ ≊ ren→sub ρ
  ≊-ren→sub (↑ k) = r-up
  ≊-ren→sub (x • ρ) = r-cons refl (≊-ren→sub ρ)

  rename-subst : ∀ {M : ABT} {ρ} → ren ρ M ≡ sub (ren→sub ρ) M
  rename-subst {M}{ρ} = rensub {M = M}{ρ}{ren→sub ρ} (≊-ren→sub ρ)

  RenRenFus : Fusable Renaming Renaming Renaming
  RenRenFus = record
                { “_” = λ M → M
                ; _⨟_≈_ = λ ρ₁ ρ₂ ρ₃ → ∀ x → ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x) ≡ ⦉ ρ₃ ⦊ x
                ; _≃_ = _≡_
                ; _⩯_ = _≡_
                ; new₁ = 0
                ; ret⩯ = λ {s}{x}{σ₁ σ₂ σ₃} → ret≈ {x}{σ₁}{σ₂}{σ₃}
                ; ext≈ = ext≈
                ; op⩯ = op⩯
                }
      where
      ret≈ : ∀ {x} {ρ₁ ρ₂ ρ₃}  →  ((x₁ : ℕ) → ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x₁) ≡ ⦉ ρ₃ ⦊ x₁)
         → ren ρ₂ (` ⦉ ρ₁ ⦊ x) ≡ (` ⦉ ρ₃ ⦊ x)
      ret≈ {x} f rewrite f x = refl
      ext≈ : ∀ {σ₁ σ₂ σ₃} {v₂ v₃} → ((x : ℕ) → ⦉ σ₂ ⦊ (⦉ σ₁ ⦊ x) ≡ ⦉ σ₃ ⦊ x)
         → v₂ ≡ v₃  →  (x : ℕ)
         → ⦉ v₂ • inc σ₂ ⦊ (⦉ 0 • inc σ₁ ⦊ x) ≡ ⦉ v₃ • inc σ₃ ⦊ x
      ext≈ {σ₁} {σ₂} {σ₃} {v₂} {.v₂} f refl zero = refl
      ext≈ {σ₁} {σ₂} {σ₃} {v₂} {.v₂} f refl (suc x) =
          begin
              ⦉ v₂ • inc σ₂ ⦊ (⦉ 0 • inc σ₁ ⦊ (suc x))
          ≡⟨⟩
              suc (⦉ σ₂ ⦊ (⦉ σ₁ ⦊ x))
          ≡⟨ cong suc (f x) ⟩
              suc (⦉ σ₃ ⦊ x)
          ≡⟨⟩
              ⦉ v₂ • inc σ₃ ⦊ (suc x)
          ∎
      open RelAux {Var}{ABT} _≡_ _≡_ using (_⩳_)
      open Reify Var ABT 0 using (reify)
      op⩯ : ∀{s : Size} {σ₁ σ₂ σ₃} {op} {args : Tuple (sig op) (λ _ → Term s)}
         → zip (λ {b} → _⩳_ {b})
             (map (ren-arg σ₂)
                (map (λ {b} M → reify {b} (ren-arg σ₁ M)) args))
              (map (ren-arg σ₃) args)
         → ren σ₂ (ren-op op (map (ren-arg σ₁) args))
           ≡ ren-op op (map (ren-arg σ₃) args)
      op⩯ {s}{σ₁}{σ₂}{σ₃}{op}{args} z = {!!}

  SubRenFus : Fusable Subst Renaming Subst
  SubRenFus = record
                { “_” = λ M → M
                ; _⨟_≈_ = λ σ₁ ρ₂ σ₃ → ∀ x → ren ρ₂ (⟦ σ₁ ⟧ x) ≡ ⟦ σ₃ ⟧ x
                ; _≃_ = λ x M → ` x ≡ M
                ; _⩯_ = _≡_
                ; new₁ = ` 0
                ; ret⩯ = λ {s}{x} f → f x
                ; ext≈ = ext≈
                ; op⩯ = {!!}
                }
    where
    module GR = GenericSubst Var (λ x → x) suc (λ {x} → refl)
    module GS = GenericSubst ABT `_ (ren (↑ 1)) (λ {x} → refl)

    ext≈ : ∀ {σ₁} {ρ₂} {σ₃} {v₂ : Var} {v₃ : ABT} →
            ((x : ℕ) → ren ρ₂ (⟦ σ₁ ⟧ x) ≡ ⟦ σ₃ ⟧ x) →
           (` v₂) ≡ v₃ →
           (x : ℕ) → ren (v₂ • inc ρ₂) (⟦ (` 0) • incs σ₁ ⟧ x)
                    ≡ ⟦ v₃ • incs σ₃ ⟧ x
    ext≈ {σ₁} {ρ₂} {σ₃} {v₂} {.(` v₂)} f refl zero = refl
    ext≈ {σ₁} {ρ₂} {σ₃} {v₂} {.(` v₂)} f refl (suc x) =
        begin
            ren (v₂ • inc ρ₂) (⟦ (` 0) • incs σ₁ ⟧ (suc x))
        ≡⟨⟩
            ren (v₂ • inc ρ₂) (⟦ incs σ₁ ⟧ x)
        ≡⟨ cong (λ □ → ren (v₂ • inc ρ₂) □) (incs-rename σ₁ x) ⟩
            ren (v₂ • inc ρ₂) (ren (↑ 1) (⟦ σ₁ ⟧ x))
        ≡⟨ {!!} ⟩
            ren (inc ρ₂) (⟦ σ₁ ⟧ x)
        ≡⟨ {!!} ⟩
            {- ren (ρ₂ ; ↑ 1) (⟦ σ₁ ⟧ x) -}
            ren (↑ 1) (ren ρ₂ (⟦ σ₁ ⟧ x))
        ≡⟨ cong (ren (↑ 1)) (f x) ⟩
            ren (↑ 1) (⟦ σ₃ ⟧ x)
        ≡⟨ sym (incs-rename σ₃ x) ⟩
            ⟦ incs σ₃ ⟧ x
        ≡⟨⟩
            ⟦ (` v₂) • incs σ₃ ⟧ (suc x)
        ∎
