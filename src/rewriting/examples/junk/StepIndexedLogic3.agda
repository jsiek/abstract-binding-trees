{-# OPTIONS --without-K --rewriting #-}

{-
 Based on the development of Logical step-indexed logical relation
 by Philip Wadler (June 1, 2022)

 Also based on "An Indexed Model of Recursive Types"
 by Appel and McAllester.
-}
module rewriting.examples.StepIndexedLogic3 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; s≤s-injective; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import rewriting.examples.IfAndOnlyIf

Setᵒ : Set₁
Setᵒ = ℕ → Set

⊥ᵒ : Setᵒ
⊥ᵒ zero     =  ⊤
⊥ᵒ (suc n)  =  ⊥

⊤ᵒ : Setᵒ
⊤ᵒ n  =  ⊤

infixr 7 _×ᵒ_
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
(P ×ᵒ Q) n  = (P n) × (Q n)

infixr 7 _⊎ᵒ_
_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
(P ⊎ᵒ Q) n  = (P n) ⊎ (Q n)

infixr 6 _→ᵒ_
_→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
(P →ᵒ Q) n  = ∀ k → k ≤ n → P k → Q k

downClosed : (ℕ → Set) → Set
downClosed P = ∀ n → P n → ∀ k → k ≤ n → P k

_≡ᵒ_ : Setᵒ → Setᵒ → Set
S ≡ᵒ T = ∀ i → S i ⇔ T i

≡ᵒ-refl : ∀{S T : Setᵒ}
  → S ≡ T
  → S ≡ᵒ T
≡ᵒ-refl refl i = (λ x → x) , (λ x → x)

≡ᵒ-sym : ∀{S T : Setᵒ}
  → S ≡ᵒ T
  → T ≡ᵒ S
≡ᵒ-sym ST i = (proj₂ (ST i)) , (proj₁ (ST i))

≡ᵒ-trans : ∀{S T R : Setᵒ}
  → S ≡ᵒ T
  → T ≡ᵒ R
  → S ≡ᵒ R
≡ᵒ-trans ST TR i = (λ z → proj₁ (TR i) (proj₁ (ST i) z))
                 , (λ z → proj₂ (ST i) (proj₂ (TR i) z))

infixr 2 _≡ᵒ⟨_⟩_
infix  3 _QEDᵒ
  
_≡ᵒ⟨_⟩_ : 
    (P : Setᵒ)
  → ∀{Q} → P ≡ᵒ Q
  → ∀{R} → Q ≡ᵒ R
  → P ≡ᵒ R
P ≡ᵒ⟨ P≡Q ⟩ Q≡R = ≡ᵒ-trans P≡Q Q≡R

_QEDᵒ :
    (P : Setᵒ)
  → P ≡ᵒ P
P QEDᵒ = ≡ᵒ-refl refl

record Setᵍ : Set₁ where
  field
    # : Setᵒ
    down : downClosed #
    tz : # 0
open Setᵍ

infixr 7 _×ᵍ_
_×ᵍ_ : Setᵍ → Setᵍ → Setᵍ
P ×ᵍ Q = record { # = λ k → # P k × # Q k
                ; down = λ k (Pk , Qk) j j≤k →
                          (down P k Pk j j≤k) , (down Q k Qk j j≤k)
                ; tz = (tz P) , (tz Q)
                }

example : ∀{P Q : Setᵍ} → # (P ×ᵍ Q) ≡ᵒ # (Q ×ᵍ P)
example {P}{Q} = 
  # (P ×ᵍ Q)          ≡ᵒ⟨ (λ i → (λ {(Pi , Qi) → Qi , Pi})
                               , (λ {(Qi , Pi) → Pi , Qi})) ⟩
  # (Q ×ᵍ P)
  QEDᵒ 
