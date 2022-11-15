{-# OPTIONS --without-K --rewriting #-}
{-

  This is an example of using Abstract Binding Trees to define the
  simply-typed lambda calculus and prove type safety via progress and
  preservation.

-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Sig

module rewriting.examples.Lambda where

data Op : Set where
  op-lam : Op
  op-app : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []

open import rewriting.AbstractBindingTree Op sig

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

Term : Set
Term = ABT

{-------------      Examples regarding substitution   -------------}

sub-app : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app = λ L M σ → refl

sub-lam : ∀ (N : Term) (σ : Subst) → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ ` 0 • ⟰ σ ⟫ N)
sub-lam N σ = refl 

sub-lam2 : ∀ (N : Term) (σ : Subst) → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ ` 0 • (σ ⨟ ↑) ⟫ N)
sub-lam2 N σ = {!!} 

{-
ren-lam : ∀ (N : Term) (ρ : Rename) → ⟪ ren ρ ⟫ (ƛ N) ≡ ƛ (⟪ ren (0 •ᵣ ⟰ᵣ ρ) ⟫ N)
ren-lam N σ = refl
-}

_ : ∀ (M L : Term) → (M • L • id) 0 ≡ M
_ = λ M L → refl

_ : ∀ (M L : Term) → (M • L • id) 1 ≡ L
_ = λ M L → refl

_ : ∀ (M L : Term) → (M • L • id) 2 ≡ ` 0
_ = λ M L → refl

_ : ∀ (M L : Term) → (M • L • id) 3 ≡ ` 1
_ = λ M L → refl

_ : ∀ (M L : Term) → ⟪ M • L • id ⟫ (` 1 · ` 0) ≡ L · M
_ = λ M L → refl

_ : ∀ (M : Term) → ⟪ M • id ⟫ (` 1 · ` 0) ≡ ` 0 · M
_ = λ M → refl

_ : ∀ (N L : Term) → ((` 1 · ` 0) [ N ] ) [ L ] ≡ (L · N [ L ])
_ = λ N L → refl

{-------------      Reduction Semantics    -------------}

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


{-------------      Type System    -------------}


data Type : Set where
  Bot   : Type
  _⇒_   : Type → Type → Type

open import Var

𝑉 : List Type → Var → Type → Type → Set
𝑉 Γ x A B = A ≡ B

𝑃 : (op : Op) → Vec Type (length (sig op)) → BTypes Type (sig op) → Type → Set
𝑃 op-lam (B ∷̌ []̌) ⟨ ⟨ A , tt ⟩ , tt ⟩ A→B = A→B ≡ A ⇒ B
𝑃 op-app (A→B ∷̌ A ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ B = A→B ≡ A ⇒ B

open import rewriting.ABTPredicate Op sig 𝑉 𝑃

pattern ⊢` ∋x = var-p ∋x refl
pattern ⊢ƛ ⊢N eq = op-p {op = op-lam} (cons-p (bind-p (ast-p ⊢N)) nil-p) eq
pattern ⊢· ⊢L ⊢M eq = op-p {op = op-app}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) eq


{-------------      Proof of Progress    -------------}

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
  → [] ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N _)                          =  done V-ƛ
progress (⊢· ⊢L ⊢M _)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ                              =  step β-ƛ

{-------------      Proof of Preservation    -------------}

open SubstPreserve (λ x → refl) (λ x → x) (λ x → x) (λ x → x) (λ {refl ⊢M → ⊢M})
  using (preserve-substitution)

preserve : ∀ {Γ M N A}
  → Γ ⊢ M ⦂ A
  → M —→ N
    ----------
  → Γ ⊢ N ⦂ A
preserve (⊢· ⊢L ⊢M refl) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M refl
preserve (⊢· ⊢L ⊢M refl) (ξ-·₂ M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) refl
preserve (⊢ƛ ⊢M refl) (ξ-ƛ M—→N) = ⊢ƛ (preserve ⊢M M—→N) refl
preserve {Γ}{(ƛ N) · M}{_}{B} (⊢· (⊢ƛ ⊢N refl) ⊢M refl) β-ƛ =
    preserve-substitution N M ⊢N ⊢M

