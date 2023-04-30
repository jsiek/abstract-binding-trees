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

⇓-value : ∀ V k → Value V → (V ⇓ val V) k
⇓-value V zero v = tt
⇓-value V (suc k) v
    with ⇓ᵏ-value V v
... | l , V⇓Vl = valueH , l + suc k , Goal
    where
    Goal : (V ⇓ᵏ val V) (l + suc k ∸ suc k)
    Goal rewrite +-∸-assoc l {suc k}{suc k} ≤-refl | n∸n≡0 k | +-identityʳ l =
        V⇓Vl

sk∸k=1 : ∀ k → suc k ∸ k ≡ suc zero
sk∸k=1 zero = refl
sk∸k=1 (suc k) = sk∸k=1 k

⇓-blame : ∀{k} → (blame ⇓ blameR) k
⇓-blame {zero} = tt
⇓-blame {suc k} = blameH , ((suc (suc k)) , Goal)
    where
    Goal : (blame ⇓ᵏ blameR) (suc k ∸ k)
    Goal rewrite sk∸k=1 k = blame⇓ᵏ

{- false
⇓-timeout : ∀{M}{k} → (M ⇓ timeout) k
⇓-timeout {M} {zero} = tt
⇓-timeout {M} {suc k} = {!!} , {!!}
-}

downClosed⇓ : ∀ M R → downClosed (M ⇓ R)
downClosed⇓ M R zero M⇓ zero z≤n = tt
downClosed⇓ M R (suc k) (H , n , M⇓Rn-k) zero z≤n = tt
downClosed⇓ M R (suc k) (H , n , M⇓Rn-k) (suc j) (s≤s j≤k) =
    H , n , ⇓ᵏhalt-upClosed M⇓Rn-k H (∸-monoʳ-≤ n (s≤s j≤k))

infix 8 _⇓ᵒ_
_⇓ᵒ_ : Term → Result → Setᵒ
M ⇓ᵒ R = record { # = (M ⇓ R)
                ; down = downClosed⇓ M R
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

infix 6 _⟹_
_⟹_ : Term → Result → ℕ → Set
(M ⟹ val V) k = (M ⇓ val V) k
(M ⟹ blameR) k = (M ⇓ blameR) k
(M ⟹ timeout) k = (M ⇑) k

downClosed⟹ : ∀ M R → downClosed (M ⟹ R)
downClosed⟹ M (val V) = downClosed⇓ M (val V)
downClosed⟹ M blameR = downClosed⇓ M blameR
downClosed⟹ M timeout = downClosed⇑ M

trueZero⟹ : ∀ M R → (M ⟹ R) 0
trueZero⟹ M (val V) = tt
trueZero⟹ M blameR = tt
trueZero⟹ M timeout = ⇓ᵏzero

infix 8 _⟹ᵒ_
_⟹ᵒ_ : Term → Result → Setᵒ
M ⟹ᵒ R = record { # = (M ⟹ R)
                ; down = downClosed⟹ M R
                ; tz = trueZero⟹ M R
                }

⟹E : ∀ M R {k} {P : Set}
   → (M ⟹ R) k
   → ((M ⇓ R) k → P)
   → ((M ⇑) k → P)
   → P
⟹E M (val V) M⟹R cont⇓ cont⇑ = cont⇓ M⟹R
⟹E M blameR M⟹R cont⇓ cont⇑ = cont⇓ M⟹R
⟹E M timeout M⟹R cont⇓ cont⇑ = cont⇑ M⟹R

{-
values-dont-diverge : ∀{V}{k}
   → Value V
   → (V ⇑) (suc k)
   → ⊥
values-dont-diverge{V}{k} (v 〈 _ 〉) (inj⇓ᵏ-raise V⇑ x) =
    values-dont-diverge{k = k} v {!!} 
-}
