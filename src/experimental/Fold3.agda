open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Size using (Size)
open import Var
open import Syntax

module experimental.Fold3 (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig

Bind : Set → Set → ℕ → Set
Bind V C zero = C
Bind V C (suc b) = V → Bind V C b

record Fold (V C : Set) : Set where
  field ret : V → C
  field fold-op : (op : Op) → ⟦ sig op ⟧ (Bind V C) → C
  field var→val : Var → V
  field shift : V → V

  open GenericSubst V var→val shift

  fold : {s : Size} → Substitution V → ABT → C
  fold-arg : Substitution V → {s : Size} (b : ℕ) → Term s → Bind V C b
  fold-args : ∀{s} (bs : List ℕ) → ⟦ bs ⟧ (λ _ → Term s) → Substitution V 
     → ⟦ bs ⟧ (Bind V C)

  fold σ (var x) = ret (⧼ σ ⧽ x)
  fold σ (node op args) = fold-op op (fold-args (sig op) args σ)
  fold-arg σ zero M = fold σ M
  fold-arg σ (suc b) M v = fold-arg (v • σ) b M
  fold-args [] tt σ = tt
  fold-args (b ∷ bs) ⟨ M , args ⟩ σ = ⟨ fold-arg σ b M , fold-args bs args σ ⟩

module Reify (V : Set) (zero-val : V) where

  reify : {b : ℕ} → Bind V ABT b → ABT
  reify {zero} M = M
  reify {suc b} f = reify {b} (f zero-val)

module RV = Reify Var 0

Renaming : Fold Var ABT
Renaming = record { ret = var
                  ; fold-op = λ op rs → node op (map RV.reify (sig op) rs)
                  ; var→val = λ x → x
                  ; shift = suc }

open Fold Renaming renaming (fold to ren)


module RT = Reify ABT (var 0)

Subst : Fold ABT ABT
Subst = record { ret = λ x → x
               ; fold-op = λ op rs → node op (map RT.reify (sig op) rs)
               ; var→val = λ x → var x
               ; shift = ren (↑ 1) }

module RelAux {V₁ C₁}{V₂ C₂} (_∼_ : V₁ → V₂ → Set) (_≈_ : C₁ → C₂ → Set) where
  data _≊_ : Substitution V₁ → Substitution V₂ → Set where
     r-up : ∀{k} → (↑ k) ≊ (↑ k)
     r-cons : ∀{v₁ σ₁ v₂ σ₂}
        → v₁ ∼ v₂  →   σ₁ ≊ σ₂
        → (v₁ • σ₁) ≊ (v₂ • σ₂)
        
  _⩳_  : {b : ℕ} → (Bind V₁ C₁ b) → (Bind V₂ C₂ b) → Set
  _⩳_ {zero} c₁ c₂ = c₁ ≈ c₂
  _⩳_ {suc b} r₁ r₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → r₁ v₁ ⩳ r₂ v₂

record Related {V₁ C₁} {V₂ C₂}
  (F₁ : Fold V₁ C₁)
  (F₂ : Fold V₂ C₂)
  : Set₁ where
  field _∼_ : V₁ → V₂ → Set
  field _≈_ : C₁ → C₂ → Set
  open Fold F₁
      renaming (var→val to var→val₁; ret to ret₁; fold-op to fop₁)
  open Fold F₂
      renaming (var→val to var→val₂; ret to ret₂; fold-op to fop₂)
  field ret≈ : ∀{v₁ v₂} → v₁ ∼ v₂ → ret₁ v₁ ≈ ret₂ v₂
  field vars∼ : ∀{x} → var→val₁ x ∼ var→val₂ x
  field var→val∼ : ∀{x} → var→val₁ x ∼ var→val₂ x
  open RelAux _∼_ _≈_
  field op≈ : ∀{op}{rs₁}{rs₂} → zip _⩳_ (sig op) rs₁ rs₂ → fop₁ op rs₁ ≈ fop₂ op rs₂
  
module Simulate {V₁ C₁ V₂ C₂} (F₁ : Fold V₁ C₁) (F₂ : Fold V₂ C₂)
  (R : Related F₁ F₂) where
  
  module FF₁ = Fold F₁
  module FF₂ = Fold F₂
  open Related R
  open RelAux _∼_ _≈_

  open GenericSubst V₁ FF₁.var→val FF₁.shift
     renaming (⧼_⧽ to ⧼_⧽₁)
  open GenericSubst V₂ FF₂.var→val FF₂.shift
     renaming (⧼_⧽ to ⧼_⧽₂)
     
  lookup∼ : {σ₁ : Substitution V₁} {σ₂ : Substitution V₂} →
      σ₁ ≊ σ₂ → {x : ℕ} → ⧼ σ₁ ⧽₁ x ∼ ⧼ σ₂ ⧽₂ x
  lookup∼ (r-up{k}) {x} = var→val∼
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {zero} = v₁∼v₂
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {suc x} = lookup∼ σ₁≊σ₂

  sim : ∀{M}{σ₁ σ₂}
     → σ₁ ≊ σ₂
     → (FF₁.fold σ₁ M) ≈ (FF₂.fold σ₂ M)
  sim-arg : ∀{σ₁}{σ₂}{b}{arg}
     → σ₁ ≊ σ₂
     → (FF₁.fold-arg σ₁ b arg) ⩳ (FF₂.fold-arg σ₂ b arg)
  sim-args : ∀{σ₁}{σ₂}{bs}{args}
     → σ₁ ≊ σ₂
     → zip _⩳_ bs (FF₁.fold-args bs args σ₁) (FF₂.fold-args bs args σ₂)
     
  sim {var x} {σ₁} {σ₂} σ₁~σ₂ = ret≈ (lookup∼ σ₁~σ₂)
  sim {node op args}{σ₁}{σ₂} σ₁~σ₂ = op≈ (sim-args {args = args} σ₁~σ₂)
  sim-arg {σ₁} {σ₂} {zero} {M} σ₁≊σ₂ = sim {M} σ₁≊σ₂
  sim-arg {σ₁} {σ₂} {suc b} {arg} σ₁≊σ₂ v₁∼v₂ =
      sim-arg {b = b} (r-cons v₁∼v₂ σ₁≊σ₂)
  sim-args {σ₁} {σ₂} {[]} {nil} σ₁≊σ₂ = tt
  sim-args {σ₁} {σ₂} {b ∷ bs} {⟨ A , As ⟩} σ₁≊σ₂ =
      ⟨ (sim-arg {b = b} {arg = A} σ₁≊σ₂) , (sim-args {bs = bs} {As} σ₁≊σ₂) ⟩

module RelReify (V₁ V₂ : Set) (zero-val₁ : V₁) (zero-val₂ : V₂)
  (_∼_ : V₁ → V₂ → Set) (zero∼ : zero-val₁ ∼ zero-val₂) where
  module R1 = Reify V₁ zero-val₁
  module R2 = Reify V₂ zero-val₂
  open RelAux {C₁ = ABT} _∼_ _≡_

  rel-arg : ∀{b}{r₁ : Bind V₁ ABT b}{r₂ : Bind V₂ ABT b}
     → r₁ ⩳ r₂
     → R1.reify {b} r₁ ≡ R2.reify {b} r₂
  rel-arg {zero}{r₁}{r₂} r~ = r~
  rel-arg {suc b} r~ = rel-arg {b} (r~ zero∼)


RenSubRel : Related Renaming Subst
RenSubRel = record
              { _∼_ = λ x M → var x ≡ M
              ; _≈_ = λ M₁ M₂ → M₁ ≡ M₂
              ; ret≈ = λ { refl → refl }
              ; vars∼ = λ {x} → refl
              ; var→val∼ = λ {x} → refl
              ; op≈ = λ {op} rs≅ → cong (node op) (map-reify rs≅)
              }
  where
  module R1 = Reify Var 0
  module R2 = Reify ABT (var 0)
  open RelAux {C₁ = ABT} (λ x M → _≡_ (var x) M) _≡_
  open RelReify Var ABT 0 (var 0) (λ x M → _≡_ (var x) M) refl using (rel-arg)

  map-reify : ∀{bs}{rs₁}{rs₂ : ⟦ bs ⟧ (Bind ABT ABT)}
    → zip _⩳_ bs rs₁ rs₂
    → map R1.reify bs rs₁ ≡ map R2.reify bs rs₂
  map-reify rs≅ =
      let mpz = map-pres-zip _⩳_ _≡_ R1.reify R2.reify rs≅ (λ{b} → rel-arg {b})
      in zip→rel _≡_ _≡_ Lift-Eq-Prod mpz 
    
open Simulate Renaming Subst RenSubRel renaming (sim to rensub)
