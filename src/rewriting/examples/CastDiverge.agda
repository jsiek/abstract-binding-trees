{-# OPTIONS --rewriting #-}
module rewriting.examples.CastDiverge where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Maybe
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.CastBigStep
open import rewriting.examples.StepIndexedLogic2

data ⇑ : Term → ℕ → Set where
  ⇑zero : ∀{M} → ⇑ M zero
  ⇑app : ∀{L M N W k}
     → L ⇓ ƛ N
     → M ⇓ W → Value W
     → ⇑ (N [ W ]) k
     → ⇑ (L · M) (suc k)
  ⇑app-L : ∀{L M k} → ⇑ L k → ⇑ (L · M) (suc k)
  ⇑app-R : ∀{L M N k} → L ⇓ ƛ N → ⇑ M k → ⇑ (L · M) (suc k)
  ⇑inj : ∀{M G k} → ⇑ M k → ⇑ (M ⟨ G !⟩) (suc k)
  ⇑proj : ∀{M H k} → ⇑ M k → ⇑ (M ⟨ H ?⟩) (suc k)

downClosed⇑ : ∀ {M} → downClosed (⇑ M)
downClosed⇑ zero ⇑M .zero z≤n = ⇑zero
downClosed⇑ (suc k) ⇑M .zero z≤n = ⇑zero
downClosed⇑ (suc k) (⇑app L⇓ M⇓ w ⇑NW) (suc j) (s≤s j≤k) =
    ⇑app L⇓ M⇓ w (downClosed⇑ k ⇑NW j j≤k)
downClosed⇑ (suc k) (⇑app-L ⇑M) (suc j) (s≤s j≤k) =
    ⇑app-L (downClosed⇑ k ⇑M j j≤k)
downClosed⇑ (suc k) (⇑app-R x ⇑M) (suc j) (s≤s j≤k) =
    ⇑app-R x (downClosed⇑ k ⇑M j j≤k)
downClosed⇑ (suc k) (⇑inj ⇑M) (suc j) (s≤s j≤k) =
    ⇑inj (downClosed⇑ k ⇑M j j≤k)
downClosed⇑ (suc k) (⇑proj ⇑M) (suc j) (s≤s j≤k) =
    ⇑proj (downClosed⇑ k ⇑M j j≤k)

⇑ᵒ : Term → Setᵒ
⇑ᵒ M = record { # = ⇑ M
              ; down = downClosed⇑ 
              ; tz = ⇑zero
              }
