{-# OPTIONS --without-K #-}
open import Data.List using (List)
open import Data.Nat using (ℕ)

module Syntax where

open import Sig public
open import Var public
open import Substitution public

module OpSig (Op : Set) (sig : Op → List Sig)  where

  open import AbstractBindingTree Op sig public
  open Substitution.ABTOps Op sig public
  open import WellScoped Op sig public

