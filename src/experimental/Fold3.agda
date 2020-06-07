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

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
    
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
 Reify a bind into a computation
 ------------------------------------------------------------------------------}

module Reify (V C : Set) (var→val : Var → V) where
  reify : {b : ℕ} → Bind V C b → C
  reify {zero} M = M
  reify {suc b} f = reify {b} (f (var→val 0))

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

{-------------------------------------------------------------------------------
 Renaming and substitution
 ------------------------------------------------------------------------------}

module ReifyRen = Reify Var ABT (λ x → x)

Renaming : Fold Var ABT
Renaming = record { ret = `_ ; var→val = λ x → x ; shift = suc 
                  ; fold-op = λ op rs → op ⦅ map ReifyRen.reify rs ⦆
                  ; var→val-suc-shift = refl}
open Fold Renaming renaming (⧼_⧽ to ⦉_⦊; fold to ren; fold-arg to ren-arg;
    fold-op to ren-op; g-inc to inc; g-ext to ext; g-inc-shift to inc-suc)


module ReifySubst = Reify ABT ABT `_

Subst : Fold ABT ABT
Subst = record { ret = λ x → x ; var→val = λ x → ` x ; shift = ren (↑ 1) 
               ; fold-op = λ op rs → op ⦅ map ReifySubst.reify rs ⦆
               ; var→val-suc-shift = refl }
open Fold Subst renaming (⧼_⧽ to ⟦_⟧; fold to sub; fold-arg to sub-arg;
    fold-op to sub-op; g-inc to incs; g-ext to exts; g-inc-shift to incs-rename)


module RelReify {s : Size} (V₁ V₂ : Set)
  (var→val₁ : Var → V₁) (var→val₂ : Var → V₂)
  (_∼_ : V₁ → V₂ → Set) (var∼ : ∀{x} → var→val₁ x ∼ var→val₂ x) where
  module R1 = Reify V₁ (Term s) var→val₁
  module R2 = Reify V₂ (Term s) var→val₂
  open RelAux {C₁ = (Term s)} _∼_ _≡_

  rel-arg : ∀{b}{r₁ : Bind V₁ (Term s) b}{r₂ : Bind V₂ (Term s) b}
     → r₁ ⩳ r₂ → R1.reify {b} r₁ ≡ R2.reify {b} r₂
  rel-arg {zero}{r₁}{r₂} r~ = r~
  rel-arg {suc b} r~ = rel-arg {b} (r~ var∼)

module RenSubProps where

{-------------------------------------------------------------------------------
 Proof of rename-subst (using Simulate)
 ------------------------------------------------------------------------------}

  module _ where
    private
      var-term-eq = λ x M → ` x ≡ M
      open RelAux {C₁ = ABT} var-term-eq _≡_ using (_≊_; r-up; r-cons; _⩳_)

      RenSubRel : Related Renaming Subst
      RenSubRel = record
        { _∼_ = var-term-eq ; _≈_ = _≡_ ; ret≈ = λ { refl → refl }
        ; vars∼ = λ {x} → refl ; var→val∼ = λ {x} → refl
        ; shift∼ = λ { refl → refl } 
        ; op≈ = λ {op} rs≅ → cong (_⦅_⦆ op)
                  (zip-map→rel _ _ _ _ _ (λ{b}→ rel-arg{b}) Lift-Eq-Tuple rs≅) }
        where
        open RelReify Var ABT (λ x → x) `_ var-term-eq refl using (rel-arg)

    open Simulate Renaming Subst RenSubRel using () renaming (sim to rensub)

    ren→sub : Substitution Var → Substitution ABT
    ren→sub (↑ k) = ↑ k
    ren→sub (x • ρ) = ` x • ren→sub ρ

    ≊-ren→sub : ∀ ρ → ρ ≊ ren→sub ρ
    ≊-ren→sub (↑ k) = r-up
    ≊-ren→sub (x • ρ) = r-cons refl (≊-ren→sub ρ)

    rename-subst : ∀ {M : ABT} {ρ} → ren ρ M ≡ sub (ren→sub ρ) M
    rename-subst {M}{ρ} = rensub {_}{ρ}{ren→sub ρ} M (≊-ren→sub ρ)

{-------------------------------------------------------------------------------
 Proof of compose-rename' (using Fuse)
 ------------------------------------------------------------------------------}

  RenRenFus : Fusable Renaming Renaming Renaming
  RenRenFus = record
                { “_” = λ M → M
                ; _⨟_≈_ = λ ρ₁ ρ₂ ρ₃ → ∀ x → ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x) ≡ ⦉ ρ₃ ⦊ x
                ; _≃_ = _≡_
                ; _⩯_ = _≡_
                ; ret⩯ = λ {s}{x}{σ₁ σ₂ σ₃} → ret≈ {x}{σ₁}{σ₂}{σ₃}
                ; ext≈ = ext≈
                ; op⩯ = λ { {op = op} z →
                        cong (λ □ → op ⦅ map reify □  ⦆) (zip→rel _⩳_ _≡_ L z) }
                }
      where
      ret≈ : ∀ {x} {ρ₁ ρ₂ ρ₃}  →  ((x₁ : ℕ) → ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x₁) ≡ ⦉ ρ₃ ⦊ x₁)
         → ren ρ₂ (` ⦉ ρ₁ ⦊ x) ≡ (` ⦉ ρ₃ ⦊ x)
      ret≈ {x} f rewrite f x = refl
      ext≈ : ∀ {σ₁ σ₂ σ₃} {v₂ v₃}
         → ((x : ℕ) → ⦉ σ₂ ⦊ (⦉ σ₁ ⦊ x) ≡ ⦉ σ₃ ⦊ x)
         → v₂ ≡ v₃  →  (x : ℕ)
         → ⦉ v₂ • inc σ₂ ⦊ (⦉ 0 • inc σ₁ ⦊ x) ≡ ⦉ v₃ • inc σ₃ ⦊ x
      ext≈ f refl zero = refl
      ext≈ f refl (suc x) rewrite f x = refl
      
      open RelAux {Var}{ABT} _≡_ _≡_ using (_⩳_)
      open Reify Var ABT (λ x → x) using (reify)
      ⩳→≡ : ∀{b}{x y : Bind Var ABT b} → x ⩳ y → x ≡ y
      ⩳→≡ {zero} {x} {.x} refl = refl
      ⩳→≡ {suc b} {f} {g} f⩳g = extensionality λ x → ⩳→≡{b}{f x}{g x}(f⩳g refl)
      
      L : Lift-Rel-Tuple (λ {b} → _⩳_ {b}) (λ {bs} → _≡_)
      L = record { base = refl
                 ; step = λ { {x = x}{xs} eq refl →
                            cong (λ □ → ⟨ □ , xs ⟩) (⩳→≡ eq)  } }

  open Fuse Renaming Renaming Renaming RenRenFus
      renaming (fusion to compose-rename')

{-------------------------------------------------------------------------------
 Proof of ...
 ------------------------------------------------------------------------------}
{-
  SubRenFus : Fusable Subst Renaming Subst
  SubRenFus = record
                { “_” = λ M → M
                ; _⨟_≈_ = λ σ₁ ρ₂ σ₃ → ∀ x → ren ρ₂ (⟦ σ₁ ⟧ x) ≡ ⟦ σ₃ ⟧ x
                ; _≃_ = λ x M → ` x ≡ M
                ; _⩯_ = _≡_
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
-}
