{-

  This is an example of using Abstract Binding Trees to define the
  simply-typed lambda calculus and prove type safety via progress and
  preservation.

-}

{-# OPTIONS --rewriting #-}

module examples.Lambda where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

import Syntax
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

data Op : Set where
  op-lam : Op
  op-app : Op

sig : Op → List ℕ
sig op-lam = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []

open Syntax using (Rename; _•_; id; ↑; ⦉_⦊; ext; ext-0; ext-suc)

open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; exts; ⟦_⟧; rename)
  renaming (ABT to Term)

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

sub-app : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app = λ L M σ → refl

sub-lam : ∀ (N : Term) (σ : Subst) → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ exts σ ⟫ N)
sub-lam = λ N σ → refl 

ren-lam : ∀ (N : Term) (ρ : Rename) → rename ρ (ƛ N) ≡ ƛ (rename (ext ρ) N)
ren-lam = λ N σ → refl 

_ : ∀ M L → ⟦ M • L • id ⟧ 0 ≡ M
_ = λ M L → refl

_ : ∀ M L → ⟦ M • L • id ⟧ 1 ≡ L
_ = λ M L → refl

_ : ∀ M L → ⟦ M • L • id ⟧ 2 ≡ ` 0
_ = λ M L → refl

_ : ∀ M L → ⟦ M • L • id ⟧ 3 ≡ ` 1
_ = λ M L → refl

_ : ∀ M L → ⟪ M • L • id ⟫ (` 1 · ` 0) ≡ L · M
_ = λ M L → refl

_ : ∀ M → ⟪ M • id ⟫ (` 1 · ` 0) ≡ ` 0 · M
_ = λ M → refl

_ : ∀ N L → ((` 1 · ` 0) [ N ] ) [ L ] ≡ (L · N [ L ])
_ = λ N L → refl

infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M : Term}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {L M M′ : Term}
    → M —→ M′
      ---------------
    → L · M —→ L · M′

  ξ-ƛ : ∀ {N N′ : Term}
    → N —→ N′
      ---------------
    → (ƛ N) —→ (ƛ N′)

  β-ƛ : ∀ {N M : Term}
      --------------------
    → (ƛ N) · M —→ N [ M ]

_ : ∀ L M → (ƛ ((ƛ (` 0 · ` 1)) · M)) · L
         —→ (ƛ (M · ` 0)) · L
_ = λ L M → ξ-·₁ (ξ-ƛ β-ƛ)


data Type : Set where
  Bot   : Type
  _⇒_   : Type → Type → Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ 0 ⦂ A

  S : ∀ {Γ x A B}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , B ∋ (suc x) ⦂ A

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  ⊢ƛ : ∀ {Γ N A B}
    → Γ , A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ N ⦂ A ⇒ B

  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

data Value : Term → Set where

  V-ƛ : ∀ {N : Term}
      ---------------------------
    → Value (ƛ N)

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢· ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ                              =  step β-ƛ

WTRename : Context → Rename → Context → Set
WTRename Γ ρ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ⦉ ρ ⦊ x ⦂ A

ext-pres : ∀ {Γ Δ ρ B}
  → WTRename Γ ρ Δ
    --------------------------------
  → WTRename (Γ , B) (ext ρ) (Δ , B)
ext-pres {ρ = ρ } ⊢ρ Z =  Z
ext-pres {ρ = ρ } ⊢ρ (S {x = x} ∋x) =  S (⊢ρ ∋x)

rename-pres : ∀ {Γ Δ ρ M A}
  → WTRename Γ ρ Δ
  → Γ ⊢ M ⦂ A
    ------------------
  → Δ ⊢ rename ρ M ⦂ A
rename-pres ⊢ρ (⊢` ∋w)           =  ⊢` (⊢ρ ∋w)
rename-pres {ρ = ρ} ⊢ρ (⊢ƛ ⊢N)   =  ⊢ƛ (rename-pres (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
rename-pres ⊢ρ (⊢· ⊢L ⊢M)        =  ⊢· (rename-pres ⊢ρ ⊢L) (rename-pres ⊢ρ ⊢M)

WTSubst : Context → Subst → Context → Set
WTSubst Γ σ Δ = ∀ {A x} → Γ ∋ x ⦂ A → Δ ⊢ ⟦ σ ⟧ x ⦂ A

exts-pres : ∀ {Γ Δ σ B}
  → WTSubst Γ σ Δ
    --------------------------------
  → WTSubst (Γ , B) (exts σ) (Δ , B)
exts-pres {σ = σ} Γ⊢σ Z = ⊢` Z
exts-pres {σ = σ} Γ⊢σ (S {x = x} ∋x) = rename-pres S (Γ⊢σ ∋x)

subst : ∀ {Γ Δ σ N A}
  → WTSubst Γ σ Δ
  → Γ ⊢ N ⦂ A
    ---------------
  → Δ ⊢ ⟪ σ ⟫ N ⦂ A
subst Γ⊢σ (⊢` eq)              = Γ⊢σ eq
subst {σ = σ} Γ⊢σ (⊢ƛ ⊢N)      = ⊢ƛ (subst {σ = exts σ} (exts-pres {σ = σ} Γ⊢σ) ⊢N) 
subst {σ = σ} Γ⊢σ (⊢· ⊢L ⊢M)   = ⊢· (subst {σ = σ} Γ⊢σ ⊢L) (subst {σ = σ} Γ⊢σ ⊢M) 

substitution : ∀{Γ A B M N}
   → Γ ⊢ M ⦂ A
   → (Γ , A) ⊢ N ⦂ B
     ---------------
   → Γ ⊢ N [ M ] ⦂ B
substitution {Γ}{A}{B}{M}{N} ⊢M ⊢N = subst {σ = M • ↑ 0} G ⊢N
    where
    G : ∀ {A₁ : Type} {x : ℕ}
      → (Γ , A) ∋ x ⦂ A₁ → Γ ⊢ ⟪ M • ↑ 0 ⟫ (` x) ⦂ A₁
    G {A₁} {zero} Z = ⊢M
    G {A₁} {suc x} (S ∋x) = ⊢` ∋x

preserve : ∀ {Γ M N A}
  → Γ ⊢ M ⦂ A
  → M —→ N
    ----------
  → Γ ⊢ N ⦂ A
preserve (⊢· ⊢L ⊢M) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M
preserve (⊢· ⊢L ⊢M) (ξ-·₂ M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′)
preserve (⊢ƛ ⊢M) (ξ-ƛ M—→N) = ⊢ƛ (preserve ⊢M M—→N)
preserve (⊢· (⊢ƛ ⊢N) ⊢M) β-ƛ = substitution ⊢M ⊢N
