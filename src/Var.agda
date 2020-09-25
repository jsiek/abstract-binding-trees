{-# OPTIONS --without-K --safe #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s; _+_)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Product using (_×_)
open import Level using (levelOfType)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sig

module Var where

Var : Set
Var = ℕ

data Lift (ℓᵛ : Level) {ℓᶜ : Level} (C : Set ℓᶜ) : Set (ℓᵛ ⊔ ℓᶜ) where
  lift : C → Lift ℓᵛ C

lower : ∀{ℓᵛ ℓᶜ}{C : Set ℓᶜ} → Lift ℓᵛ C → C
lower (lift c) = c

lift-lower-id : ∀{ℓᵛ ℓᶜ}{C : Set ℓᶜ} (lc : Lift ℓᵛ C)
  → lift (lower lc) ≡ lc
lift-lower-id (lift c) = refl

private
  variable
    ℓ : Level
    I : Set ℓ
    Γ Δ : List I
    x : Var
    A : I

_∋_⦂_ : List I → Var → I → Set (levelOfType I)
_∋_⦂_ {I = I} [] x A = Lift (levelOfType I) ⊥
_∋_⦂_ (B ∷ Γ) zero A = A ≡ B
_∋_⦂_ (B ∷ Γ) (suc x) A = Γ ∋ x ⦂ A

∋x→< : Γ ∋ x ⦂ A → x < (length Γ)
∋x→< {Γ = []} {x} (lift ())
∋x→< {Γ = B ∷ Γ} {x = zero} ∋x = s≤s z≤n
∋x→< {Γ = B ∷ Γ} {x = suc x} ∋x = s≤s (∋x→< {Γ = Γ} ∋x)

<→∋x : ∀{Γ : List {a = lzero} ⊤}{x A} → x < (length Γ) → Γ ∋ x ⦂ A
<→∋x {Γ = B ∷ Γ} {x = zero} x<Γ = refl
<→∋x {Γ = B ∷ Γ} {x = suc x} (s≤s x<Γ) = <→∋x {Γ = Γ} x<Γ 

∋++ : Γ ∋ x ⦂ A  → (Δ ++ Γ) ∋ (length Δ + x) ⦂ A  
∋++ {Δ = []} ∋ΔΓ = ∋ΔΓ
∋++ {Δ = B ∷ Δ} ∋ΔΓ = ∋++ {Δ = Δ} ∋ΔΓ

{--- types for bound variables ---}

BType : ∀{ℓ} → Set ℓ → Sig → Set ℓ
BType I ■ = ⊤
BType I (ν b) = I × BType I b
BType I (∁ b) = BType I b

BTypes : ∀{ℓ} → Set ℓ → List Sig → Set ℓ
BTypes I [] = ⊤
BTypes I (b ∷ bs) = BType I b × BTypes I bs

