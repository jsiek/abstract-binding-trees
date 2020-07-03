open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (Dec; yes; no)
open import Var

module experimental.Environment where

record Shiftable {ℓ} (V : Set ℓ) : Set ℓ where
  field ⇑ : V → V
        var→val : Var → V
        var→val-suc-shift : ∀{x} → var→val (suc x) ≡ ⇑ (var→val x)

instance
  Var-is-Shiftable : Shiftable Var
  Var-is-Shiftable = record { var→val = λ x → x ; ⇑ = suc
                            ; var→val-suc-shift = λ {x} → refl }

open Shiftable {{...}}

{-
l→f : List Var → Var → Var
l→f [] y = y
l→f (x ∷ xs) zero = x
l→f (x ∷ xs) (suc y) = l→f xs y

record Env {ℓ} (E : Set ℓ) (V : Set ℓ) : Set ℓ where
  field {{V-is-Shiftable}} : Shiftable V
  field ⟅_⟆  : E → Var → V   {- lookup variable in environment -}
        _,_ : E → V → E      {- update environment, mapping 0 to value -}
        ⟰ : E → E            {- shift up by one everything in environment -}
        π : List Var → E → E {- permute the environment -}
        lookup-0 : ∀ ρ v → ⟅ ρ , v ⟆ 0 ≡ v
        lookup-suc : ∀ ρ v x → ⟅ ρ , v ⟆ (suc x) ≡ ⇑ (⟅ ρ ⟆ x)
        lookup-shift : ∀ ρ x → ⟅ ⟰ ρ ⟆ x ≡ ⇑ (⟅ ρ ⟆ x)
        lookup-perm : ∀ ρ xs x → ⟅ π xs ρ ⟆ x ≡ ⟅ ρ ⟆ ((l→f xs) x)
  ext : E → E
  ext ρ = ρ , (var→val 0)

fun-extend : ∀{ℓ}{V : Set ℓ}{{_ : Shiftable V}} → (Var → V) → V → (Var → V)
fun-extend ρ v zero = v
fun-extend ρ v (suc x) = ⇑ (ρ x)

instance
  Fun-is-Env : ∀{ℓ}{V : Set ℓ}{{_ : Shiftable V}} → Env (Var → V) V
  Fun-is-Env = record { ⟅_⟆ = λ ρ x → ρ x ; _,_ = fun-extend
      ; ⟰ = λ ρ x → ⇑ (ρ x) ; π = λ xs ρ → ρ ∘ (l→f xs)
      ; lookup-0 = λ ρ v → refl
      ; lookup-suc = λ ρ v x → refl ; lookup-shift = λ ρ x → refl
      ; lookup-perm = λ ρ xs x → refl }
-}


