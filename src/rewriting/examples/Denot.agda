{-# OPTIONS --without-K --rewriting #-}
{-

-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Var

module rewriting.examples.Denot where

data Val : Set where
  lit : ℕ → Val
  _↦_ : List Val → Val → Val
  pair : List Val → List Val → Val

D : Set₁
D = Val → Set

⊥′ : D
⊥′ v = ⊥

{- Application Operator -}
infixl 7 _●_
_●_ : D → D → D
_●_ D₁ D₂ w = (∃[ v ] D₂ v)
               × Σ[ V ∈ List Val ] D₁ (V ↦ w) × (∀ {v} → v ∈ V → D₂ v)

{- Abstraction Operator -}
Λ : (D → D) → D
Λ F (lit k) = ⊥
Λ F (V ↦ w) = F (_∈ V) w
Λ F (pair v w) = ⊥

{- Pair operator -}
⦅_,_⦆ : D → D → D
⦅ D₁ , D₂ ⦆ (lit k) = ⊥
⦅ D₁ , D₂ ⦆ (v ↦ w) = ⊥
⦅ D₁ , D₂ ⦆ (pair V W) = (∀ {v} → v ∈ V → D₁ v) × (∀ {w} → w ∈ W → D₂ w)

{- Fst operator -}
π₁ : D → D
π₁ D v = ∃[ V ] ∃[ W ] D (pair V W) × v ∈ V

{- Snd operator -}
π₂ : D → D
π₂ D w = ∃[ V ] ∃[ W ] D (pair V W)  × w ∈ W

{- For looking up variables -}
nth : ∀{ℓ}{A : Set ℓ} → ℕ → List A → A → A
nth n [] d = d
nth zero (x ∷ xs) d = x
nth (suc n) (x ∷ xs) d = nth n xs d

