open import Data.Nat using (ℕ; zero; suc)
open import GenericSubstitution
open import Var

module Env (V : Set) where

record EnvI (Env : Set) : Set where
  field lookup : Env → Var → V
        _,_ : Env → V → Env
        ext : Env → Env

module FunIsEnv (S : Shiftable V) where
  open Shiftable S

  fun-ext : (Var → V) → V → (Var → V)
  fun-ext ρ v zero = v
  fun-ext ρ v (suc x) = shift (ρ x)

  FunIsEnv : EnvI (Var → V)
  FunIsEnv = record { lookup = λ ρ x → ρ x
                    ; _,_ = fun-ext ; ext = λ ρ → fun-ext ρ (var→val 0) }

module GSubstIsEnv (S : Shiftable V) where

  open GenericSubst S using (⧼_⧽; g-extend; g-ext)
  
  GSubstIsEnv : EnvI (GSubst V)
  GSubstIsEnv = record { lookup = ⧼_⧽; _,_ = λ ρ v → g-extend v ρ; ext = g-ext }

