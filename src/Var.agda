open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s; _+_)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sig

module Var where

Var : Set
Var = ℕ

_∋_⦂_ : ∀{I : Set} → List I → Var → I → Set
_∋_⦂_ {I} [] x A = ⊥
_∋_⦂_ {I} (B ∷ Γ) zero A = A ≡ B
_∋_⦂_ {I} (B ∷ Γ) (suc x) A = Γ ∋ x ⦂ A

∋x→< : ∀{I : Set}{Γ : List I}{x A} → Γ ∋ x ⦂ A → x < (length Γ)
∋x→< {I}{B ∷ Γ} {zero} {A} ∋x = s≤s z≤n
∋x→< {I}{B ∷ Γ} {suc x} {A} ∋x = s≤s (∋x→< {I}{Γ} ∋x)

<→∋x : ∀{I : Set}{Γ : List ⊤}{x A} → x < (length Γ) → Γ ∋ x ⦂ A
<→∋x {I}{B ∷ Γ} {zero} {A} x<Γ = refl
<→∋x {I}{B ∷ Γ} {suc x} {A} (s≤s x<Γ) = <→∋x {I}{Γ}{x}{A} x<Γ

∋++ : ∀{I}{Γ Δ : List I}{x A} →  Γ ∋ x ⦂ A  → (Δ ++ Γ) ∋ (length Δ + x) ⦂ A  
∋++ {I}{Γ} {[]} {x} {A} ∋ΔΓ = ∋ΔΓ
∋++ {I}{Γ} {B ∷ Δ} {x} {A} ∋ΔΓ = ∋++ {I}{Γ}{Δ}{x}{A} ∋ΔΓ

{--- types for bound variables ---}

BType : Set → Sig → Set
BType I ■ = ⊤
BType I (ν b) = I × BType I b
BType I (∁ b) = BType I b

BTypes : Set → List Sig → Set
BTypes I [] = ⊤
BTypes I (b ∷ bs) = BType I b × BTypes I bs

