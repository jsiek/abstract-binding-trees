{-# OPTIONS --without-K --safe #-}
open import Data.Nat using (ℕ; zero; suc)

module Sig where

data Sig : Set where
  ■ : Sig
  ν : Sig → Sig
  ∁ : Sig → Sig

sig→ℕ : Sig → ℕ
sig→ℕ ■ = 0
sig→ℕ (ν b) = suc (sig→ℕ b)
sig→ℕ (∁ b) = sig→ℕ b
