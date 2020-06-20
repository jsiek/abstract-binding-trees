open import Data.Nat using (ℕ; zero; suc)
open import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Var

module Environment where

record Env (E : Set) (V : Set) : Set where
  field V-is-Shiftable : Shiftable V
  open Shiftable V-is-Shiftable
  field lookup : E → Var → V
        _,_ : E → V → E
        ext-env : E → E
        shift-env : E → E
        lookup-0 : ∀ ρ v → lookup (ρ , v) 0 ≡ v
        lookup-suc : ∀ ρ v x → lookup (ρ , v) (suc x) ≡ shift (lookup ρ x)
        lookup-shift : ∀ ρ x → lookup (shift-env ρ) x ≡ shift (lookup ρ x)

module _ where
  open Shiftable {{...}}
  
  fun-ext : ∀{V}{{_ : Shiftable V}} → (Var → V) → V → (Var → V)
  fun-ext ρ v zero = v
  fun-ext ρ v (suc x) = shift (ρ x)

  instance
    Fun-is-Env : ∀{V}{{_ : Shiftable V}} → Env (Var → V) V
    Fun-is-Env {V}{{V-is-Shiftable}} = record { V-is-Shiftable = V-is-Shiftable
                      ; lookup = λ ρ x → ρ x
                      ; _,_ = fun-ext ; ext-env = λ ρ → fun-ext ρ (var→val 0)
                      ; shift-env = λ ρ x → shift (ρ x)
                      ; lookup-0 = λ ρ v → refl
                      ; lookup-suc = λ ρ v x → refl
                      ; lookup-shift = λ ρ x → refl }

instance
  GSubst-is-Env : ∀{V}{{_ : Shiftable V}} → Env (GSubst V) V
  GSubst-is-Env {V}{{V-is-Shiftable}} = record { V-is-Shiftable = V-is-Shiftable
                       ; lookup = ⧼_⧽; _,_ = λ ρ v → g-extend v ρ
                       ; ext-env = g-ext
                       ; shift-env = g-inc
                       ; lookup-0 = λ ρ v → refl
                       ; lookup-suc = λ ρ v x → g-inc-shift ρ x
                       ; lookup-shift = λ ρ x → g-inc-shift ρ x }
    where open GenericSubst V-is-Shiftable
