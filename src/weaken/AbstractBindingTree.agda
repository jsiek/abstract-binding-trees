{-
 Based on Philip Wadler's paper Explicit Weakening.
-}

{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _≟_)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning

module weaken.AbstractBindingTree {ℓ} (Op : Set ℓ) (sig : Op → List ℕ) where

infixl 5 _▷_
infixl 5 _⨟_
infix 8 _↑

data Args : List ℕ → Set ℓ

data ABT : Set ℓ where
  • : ABT
  _↑ : ABT → ABT
  _⦅_⦆ : (op : Op) → Args (sig op) → ABT

data Arg : ℕ → Set ℓ where
  ast : ABT → Arg 0
  bind : ∀{b} → Arg b → Arg (suc b)

data Args where
  nil : Args []
  cons : ∀{b bs} → Arg b → Args bs → Args (b ∷ bs)

data Subst : Set ℓ where
  id : Subst
  _↑ : Subst → Subst
  _▷_ : Subst → ABT → Subst

_[_] : ABT → Subst → ABT
_[_]ₐ : ∀{b} → Arg b → Subst → Arg b
_[_]* : ∀{bs} → Args bs → Subst → Args bs
M [ id ] = M
M [ σ ↑ ] = M [ σ ] ↑ 
• [ σ ▷ N ] = N
(M ↑) [ σ ▷ N ] = M [ σ ]
(op ⦅ args ⦆) [ σ ▷ N ] = op ⦅ args [ σ ▷ N ]* ⦆

ast M [ σ ]ₐ = ast (M [ σ ])
bind arg [ σ ]ₐ = bind (arg [ σ ↑ ▷ • ]ₐ)

nil [ σ ]* = nil
(cons arg args) [ σ ]* = cons (arg [ σ ]ₐ) (args [ σ ]*)

_⨟_ : Subst → Subst → Subst
σ ⨟ id = σ
σ ⨟ τ ↑ = (σ ⨟ τ) ↑
id ⨟ (τ ▷ N) = τ ▷ N
σ ↑ ⨟ (τ ▷ N) = σ ⨟ τ
(σ ▷ M) ⨟ (τ ▷ N) = σ ⨟ (τ ▷ N) ▷ (M [ τ ▷ N ]) 

sub-sub-compose : ∀(M : ABT) (σ τ : Subst) → (M [ σ ] [ τ ]) ≡ M [ σ ⨟ τ ]
sub-sub-compose-arg : ∀{b}(arg : Arg b) (σ τ : Subst) → arg [ σ ]ₐ [ τ ]ₐ ≡ arg [ σ ⨟ τ ]ₐ
sub-sub-compose-args : ∀{b}(args : Args b) (σ τ : Subst) → args [ σ ]* [ τ ]* ≡ args [ σ ⨟ τ ]*

sub-sub-compose M σ id = refl
sub-sub-compose M σ (τ ↑) = cong _↑ (sub-sub-compose M σ τ)
sub-sub-compose M id (τ ▷ N) = refl
sub-sub-compose M (σ ↑) (τ ▷ N) = sub-sub-compose M σ τ
sub-sub-compose • (σ ▷ L) (τ ▷ N) = refl
sub-sub-compose (M ↑) (σ ▷ L) (τ ▷ N) = sub-sub-compose M σ (τ ▷ N)
sub-sub-compose (op ⦅ args ⦆) (σ ▷ L) (τ ▷ N) = 
  cong (λ X → op ⦅ X ⦆) (sub-sub-compose-args args (σ ▷ L) (τ ▷ N))

sub-sub-compose-arg (ast M) σ τ = cong ast (sub-sub-compose M σ τ)
sub-sub-compose-arg (bind arg) σ τ = cong bind (sub-sub-compose-arg arg (σ ↑ ▷ •) (τ ↑ ▷ •))

sub-sub-compose-args nil σ τ = refl
sub-sub-compose-args (cons arg args) σ τ =
  cong₂ cons (sub-sub-compose-arg arg σ τ) (sub-sub-compose-args args σ τ)

{-# REWRITE sub-sub-compose sub-sub-compose-arg sub-sub-compose-args #-}

left-id : (τ : Subst) → id ⨟ τ ≡ τ
left-id id = refl
left-id (τ ↑) = cong _↑ (left-id τ)
left-id (τ ▷ N) = refl

{-# REWRITE left-id #-}

assoc : (σ τ ν : Subst) → (σ ⨟ τ) ⨟ ν ≡ σ ⨟ (τ ⨟ ν)
assoc σ τ id = refl
assoc σ τ (ν ↑) = cong _↑ (assoc σ τ ν)
assoc σ id (ν ▷ N) = refl
assoc σ (τ ↑) (ν ▷ N) = assoc σ τ ν
assoc id (τ ▷ M) (ν ▷ N) = refl
assoc (σ ↑) (τ ▷ M) (ν ▷ N) = assoc σ τ (ν ▷ N)
assoc (σ ▷ L) (τ ▷ M) (ν ▷ N) = cong₂ _▷_ (assoc σ (τ ▷ M) (ν ▷ N)) refl

{-# REWRITE assoc #-}

_[_]₀ : ABT → ABT → ABT
N [ M ]₀ = N [ id ▷ M ]

_[_]₁ : ABT → ABT → ABT
N [ M ]₁ = N [ (id ▷ M) ↑ ▷ • ]

_[_]₁[_]₀ : ABT → ABT → ABT → ABT
N [ M ]₁[ L ]₀ = N [ id ▷ M ▷ L ]

up-subst-id : ∀(M N : ABT) → (N ↑) [ M ]₀ ≡ N
up-subst-id M N = refl

commute-subst : ∀(L M N : ABT) → N [ M ]₀ [ L ]₀ ≡ N [ L ]₁ [ M [ L ]₀ ]₀
commute-subst L M N = refl

exts-subst-cons : ∀(σ : Subst)(N V : ABT) → N [ σ ↑ ▷ • ] [ V ]₀ ≡ N [ σ ▷ V ]
exts-subst-cons σ N V = refl
