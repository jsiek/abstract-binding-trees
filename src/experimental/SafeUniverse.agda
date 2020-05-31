open import Data.List using (List; _∷_)
open import Data.Product using (_×_)

module experimental.SafeUniverse where

{-
  Things that have type I in environment List I.
-}
_-Scoped : Set → Set₁
I -Scoped = I → List I → Set

private
  variable
    P Q : Set

  infixr 3 _→̇_
  _→̇_ : (S T : P → Set) → (P → Set)
  (S →̇ T) a = S a → T a

  _×̇_ : (S T : P → Set) → (P → Set)
  (S ×̇ T) a = S a × T a

  _⊢_ : (P → Q) → (Q → Set) → (P → Set)
  (f ⊢ T) a = T (f a)

  κ : Set → (P → Set)
  κ S a = S

  [_] : (P → Set) → Set
  [ T ] = ∀{a} → T a

private
  variable
    I J : Set
    i : I
    j : J

data Var : I -Scoped where
  z : [ (i ∷_) ⊢ Var i ]
  s : [ Var i →̇ (j ∷_) ⊢ Var i ]

infixr 3 _⇒_

data Type : Set where
  α     : Type
  _⇒_  : Type → Type → Type

private
  variable
    σ τ : Type
    Γ Δ : List Type

data Lam : Type -Scoped where
  V  : [ Var σ →̇ Lam σ ]
  A  : [ Lam (σ ⇒ τ) →̇ Lam σ →̇ Lam τ ]
  L  : [ (σ ∷_) ⊢ Lam τ →̇ Lam (σ ⇒ τ) ]
