open import Data.Nat using (ℕ; zero; suc)
open import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Var

module Env {V : Set} (S : Shiftable V) where

open Shiftable S

record EnvI (Env : Set) : Set where
  field lookup : Env → Var → V
        _,_ : Env → V → Env
        ext-env : Env → Env
        shift-env : Env → Env
        lookup-0 : ∀ ρ v → lookup (ρ , v) 0 ≡ v
        lookup-suc : ∀ ρ v x → lookup (ρ , v) (suc x) ≡ shift (lookup ρ x)
        lookup-shift : ∀ ρ x → lookup (shift-env ρ) x ≡ shift (lookup ρ x)

fun-ext : (Var → V) → V → (Var → V)
fun-ext ρ v zero = v
fun-ext ρ v (suc x) = shift (ρ x)

FunIsEnv : EnvI (Var → V)
FunIsEnv = record { lookup = λ ρ x → ρ x
                  ; _,_ = fun-ext ; ext-env = λ ρ → fun-ext ρ (var→val 0)
                  ; shift-env = λ ρ x → shift (ρ x)
                  ; lookup-0 = λ ρ v → refl
                  ; lookup-suc = λ ρ v x → refl
                  ; lookup-shift = λ ρ x → refl }


open GenericSubst S using (⧼_⧽; g-extend; g-ext; g-inc; g-inc-shift)

GSubstIsEnv : EnvI (GSubst V)
GSubstIsEnv = record { lookup = ⧼_⧽; _,_ = λ ρ v → g-extend v ρ
                     ; ext-env = g-ext
                     ; shift-env = g-inc
                     ; lookup-0 = λ ρ v → refl
                     ; lookup-suc = λ ρ v x → g-inc-shift ρ x
                     ; lookup-shift = λ ρ x → g-inc-shift ρ x }

