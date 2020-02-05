open import Data.Maybe 
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; ≤-pred; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)


module Variables where

data Var : ℕ → Set where

  Z : ∀ {Γ}
     ---------
   → Var (suc Γ)

  S_ : ∀ {Γ}
    → Var Γ
      ---------
    → Var (suc Γ)

{-
Rename : ℕ → ℕ → Set
Rename Γ Δ = Var Γ → Var Δ

ext : ∀ {Γ Δ} → Rename Γ Δ
    ----------------------
  → Rename (suc Γ) (suc Δ)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
-}

_var≟_ : ∀ {Γ} → (x y : Var Γ) → Dec (x ≡ y)
Z var≟ Z  =  yes refl
Z var≟ (S _)  =  no λ()
(S _) var≟ Z  =  no λ()
(S x) var≟ (S y) with  x var≟ y
...                 |  yes refl =  yes refl
...                 |  no neq   =  no λ{refl → neq refl}

var≟-refl : ∀ {Γ} (x : Var Γ) → (x var≟ x) ≡ yes refl
var≟-refl Z = refl
var≟-refl (S x) rewrite var≟-refl x = refl

var→ℕ : ∀{Γ} → Var Γ → Σ[ n ∈ ℕ ] n < Γ
var→ℕ {Γ} Z = ⟨ 0 , s≤s z≤n ⟩
var→ℕ (S x)
    with var→ℕ x
... | ⟨ n , lt ⟩ =
      ⟨ suc n , s≤s lt ⟩

ℕ→var : ∀{Γ} → (n : ℕ) → (lt : n < Γ) → Var Γ
ℕ→var {zero} zero ()
ℕ→var {suc Γ} zero lt =
    Z
ℕ→var {zero} (suc n) ()
ℕ→var {suc Γ} (suc n) lt =
    S (ℕ→var {Γ} n (≤-pred lt))


{- Some other miscellaneous stuff -}

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

