{-# OPTIONS --without-K --rewriting #-}

{-

 Based on "Logical Step-Indexed Logical Relations"
 by Dreyer, Ahmed, and Birkedal.

 Based on the Agda development of Logical Step-Indexed Logical Relations
 by Philip Wadler (June 1, 2022)

 The proof of the fixpoint theorem is based on "An Indexed Model of
 Recursive Types" by Appel and McAllester.

-}
module rewriting.examples.StepIndexedLogic2 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import Level using (Lift)

open import rewriting.examples.EquivalenceRelation public

Setₒ : Set₁
Setₒ = ℕ → Set

Predₒ : Set → Set₁
Predₒ A = A → Setₒ

Context : Set₁
Context = List Set

Preds : Context → Set₁
Preds [] = topᵖ 
Preds (A ∷ Γ) = (A → ℕ → Set) × Preds Γ

SISet : Context → Set₁
SISet Γ = Preds Γ → ℕ → Set

downClosed : (ℕ → Set) → Set
downClosed S = ∀ n → S n → ∀ k → k ≤ n → S k

downClosedᵖ : ∀{A} → (A → ℕ → Set) → Set
downClosedᵖ P = ∀ a → downClosed (P a)

downClosedᵖs : ∀{Γ} → Preds Γ → Set
downClosedᵖs {[]} μs = ⊤
downClosedᵖs {A ∷ Γ} (μP , μs) = (downClosedᵖ μP) × (downClosedᵖs μs)

downClosedᵒ : ∀{Γ} → SISet Γ → Set₁
downClosedᵒ {Γ} S = ∀ (μs : Preds Γ) → downClosedᵖs μs → downClosed (S μs) 

trueZeroᵖ : ∀{A} → (A → ℕ → Set) → Set
trueZeroᵖ P = ∀ a → (P a) 0

trueZeroᵖs : ∀{Γ} → Preds Γ → Set
trueZeroᵖs {[]} μs = ⊤
trueZeroᵖs {A ∷ Γ} (μP , μs) = (trueZeroᵖ μP) × (trueZeroᵖs μs)

trueZeroᵒ : ∀{Γ} → SISet Γ → Set₁
trueZeroᵒ {Γ} S = ∀ (μs : Preds Γ) → trueZeroᵖs μs → (S μs) 0

data Time : Set where
  Now : Time
  Later : Time

data Times : Context → Set₁ where
  ∅ : Times []
  cons : ∀{Γ}{A} → Time → Times Γ → Times (A ∷ Γ)

↓ : ℕ → Setₒ → Setₒ
↓ k S zero = ⊤
↓ k S (suc j) = suc j < k × (S (suc j))

↓ᵖ : ℕ → ∀{A : Set} → Predₒ A → Predₒ A
↓ᵖ k P a = ↓ k (P a)

abstract
  infix 2 _≡ₒ_
  _≡ₒ_ : Setₒ → Setₒ → Set
  S ≡ₒ T = ∀ i → S i ⇔ T i

  infix 2 _≡ₚ_
  _≡ₚ_ : ∀{A} → Predₒ A → Predₒ A → Set
  P ≡ₚ Q = ∀ v → P v ≡ₒ Q v

-- goodness : {Γ : Context} → Times Γ → SISet Γ → Set₁
-- goodness ∅ S = Lift _ ⊤
-- goodness (cons Now ts) S = {!!}
-- goodness (cons Later ts) S = {!!}

record Setᵒ (Γ : Context) (ts : Times Γ) : Set₁ where
  field
    # : SISet Γ
    down : downClosedᵒ #
    tz : trueZeroᵒ #
    good : ⊤
    congr : ⊤
open Setᵒ public

⊥ᵒ : ∀{Γ}{ts : Times Γ} → Setᵒ Γ ts
⊥ᵒ = record { # = λ { μs zero → ⊤ ; μs (suc k) → ⊥}
            ; down = λ { μs dμs zero x zero k≤n → tt}
            ; tz = λ μs tzμs → tt
            ; good = tt
            ; congr = tt
            }

{-
  Variable refering to a recursive predicate (from a μᵒ)
-}
data _⊢_ : Context → Set → Set₁ where
  ze : ∀{Γ}{A} → (A ∷ Γ) ⊢ A
  sc : ∀{Γ}{A}{B} → Γ ⊢ B → (A ∷ Γ) ⊢ B

{-
Apply recursive predicate to an argument.
-}
^ : ∀{Γ}{ts : Times Γ}{A} → (x : Γ ⊢ A) → A → Setᵒ Γ ts
^ ze a =
    record { # = λ (μP , μs) k → μP a k
           ; down = λ (μP , μs) (dμP , dμs) → dμP a
           ; tz = λ (μP , μs) (tzμP , tzμs) → tzμP a
           ; good = tt
           ; congr = tt
           }
^{A ∷ Γ}{cons t ts} (sc{Γ}{A}{B} x) a =
  let y = ^{Γ}{ts} x a in
  record { # = λ {(μP , μs) k → # y μs k}
         ; down = λ {(μP , μs) (tzP , tzμs) → down y μs tzμs}
         ; tz = λ (μP , μs) (tzμP , tzμs) → tz y μs tzμs
         ; good = tt
         ; congr = tt
         }

choose : Time → Time → Time
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later

combine : ∀{Γ} (ts₁ ts₂ : Times Γ) → Times Γ
combine {[]} ts₁ ts₂ = ∅
combine {A ∷ Γ} (cons x ts₁) (cons y ts₂) = cons (choose x y) (combine ts₁ ts₂)

infixr 7 _×ᵒ_
_×ᵒ_ : ∀{Γ}{ts₁ ts₂ : Times Γ}
   → Setᵒ Γ ts₁
   → Setᵒ Γ ts₂
     ------------------------
   → Setᵒ Γ (combine ts₁ ts₂)
S ×ᵒ T = record { # = λ μs k → # S μs k × # T μs k
                ; down = λ μs dμs n (Sn , Tn) k k≤n →
                          (down S μs dμs n Sn k k≤n , down T μs dμs n Tn k k≤n)
                ; tz = λ μs tzμs → (tz S μs tzμs) , (tz T μs tzμs)
                ; good = tt
                ; congr = tt
                }
