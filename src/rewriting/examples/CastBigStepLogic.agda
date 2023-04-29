{-# OPTIONS --rewriting #-}
module rewriting.examples.CastBigStepLogic where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties 
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.CastBigStepResult
open import rewriting.examples.StepIndexedLogic2

infixr 6 _⇓_
_⇓_ : Term → Result → ℕ → Set
(M ⇓ R) 0 = ⊤
(M ⇓ R) (suc k) = Halt R × ∃[ n ] (M ⇓ᵏ R) (n ∸ (suc k))

downClosed⇓ : ∀ M R → downClosed (M ⇓ R)
downClosed⇓ M R zero M⇓ zero z≤n = tt
downClosed⇓ M R (suc k) (H , n , M⇓Rn-k) zero z≤n = tt
downClosed⇓ M R (suc k) (H , n , M⇓Rn-k) (suc j) (s≤s j≤k) =
    H , n , ⇓ᵏhalt-upClosed M⇓Rn-k H (∸-monoʳ-≤ n (s≤s j≤k))

infix 8 _⇓ᵒ_
_⇓ᵒ_ : Term → Result → Setᵒ
M ⇓ᵒ N = record { # = (M ⇓ N)
                ; down = downClosed⇓ M N
                ; tz = tt
                }

_⇑ : Term → ℕ → Set
(M ⇑) k = (M ⇓ᵏ timeout) k

downClosed⇑ : ∀ M → downClosed (M ⇑)
downClosed⇑ M k M⇑ j j≤k = ⇓ᵏtimeout-downClosed M⇑ j≤k

infix 8 _⇑ᵒ
_⇑ᵒ : Term → Setᵒ
M ⇑ᵒ = record { # = (M ⇑)
              ; down = downClosed⇑ M
              ; tz = ⇓ᵏzero
              }


{-
⇓ᵒ-value : ∀ {𝒫} → ∀ V → Value V → 𝒫 ⊢ᵒ V ⇓ᵒ V
⇓ᵒ-value {𝒫} V v = ⊢ᵒ-intro λ n 𝒫n → ⇓-value V v

-}
