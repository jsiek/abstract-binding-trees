{-# OPTIONS --without-K --safe #-}
open import Data.Nat using (ℕ; zero; suc)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Sig where

data Sig : Set where
  ■ : Sig
  ν : Sig → Sig
  ∁ : Sig → Sig

sig→ℕ : Sig → ℕ
sig→ℕ ■ = 0
sig→ℕ (ν b) = suc (sig→ℕ b)
sig→ℕ (∁ b) = sig→ℕ b

ℕ→sig : ℕ → Sig
ℕ→sig 0 = ■
ℕ→sig (suc n) = ν (ℕ→sig n)

{- The following is used in Fold2 -}

Result : {ℓ : Level} → Set ℓ → Sig → Set ℓ
Result V ■ = V
Result V (ν b) = V → Result V b
Result V (∁ b) = Result V b

