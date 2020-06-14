{-

  This is an example of using Abstract Binding Trees to define the
  simply-typed lambda calculus and prove type safety via progress and
  preservation.

-}

import Syntax
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module examples.Lambda where

data Op : Set where
  op-lam : Op
  op-app : Op

sig : Op → List ℕ
sig op-lam = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []

open Syntax using (Rename; _•_; id; ↑; ⦉_⦊; ext; ext-0; ext-suc;
    RenameIsSubstable)

open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; exts; ⟦_⟧;
         rename; exts-0; exts-suc-rename;
         RenameIsMap; SubstIsSubstable; SubstIsMap)
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

open import Var using (Var)
open import Preserve Op sig

𝑉 : List Type → Var → Type → Set
𝑉 Γ x A = ⊤

𝑃 : (op : Op) → Vec Type (length (sig op)) → BTypes Type (sig op) → Type → Set
𝑃 op-lam (B ∷̌ []̌) ⟨ ⟨ A , tt ⟩ , tt ⟩ A→B = A→B ≡ A ⇒ B
𝑃 op-app (A→B ∷̌ A ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ B = A→B ≡ A ⇒ B

open ABTPred 𝑉 𝑃

pattern ⊢` ∋x = var-p ∋x tt
pattern ⊢ƛ ⊢N eq = op-p {op = op-lam} (cons-p (bind-p (ast-p ⊢N)) nil-p) eq
pattern ⊢· ⊢L ⊢M eq = op-p {op = op-app}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) eq

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
progress (⊢ƛ ⊢N _)                            =  done V-ƛ
progress (⊢· ⊢L ⊢M _)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ                              =  step β-ƛ


module _ where
  open FoldPred 𝑃 (λ Γ v A → ⊤) _∋_⦂_ _⊢_⦂_ RenameIsSubstable
  RenPres : PreserveMap {I = Type} RenameIsMap
  RenPres = record { 𝑉 = 𝑉 ; 𝑃 = 𝑃 ; _⊢v_⦂_ = _∋_⦂_ ; ∋→⊢v-var→val = λ x → x
            ; ext-⊢v = λ x → x ; ⊢v→⊢ = λ x → ⊢` x ; ⊢v0 = refl }
  open PreserveMap RenPres using ()
      renaming (preserve-map to rename-pres) public

open FoldPred 𝑃 (λ Γ v A → ⊤) _⊢_⦂_ _⊢_⦂_ SubstIsSubstable
SubstPres : PreserveMap SubstIsMap
SubstPres = record { 𝑉 = 𝑉 ; 𝑃 = 𝑃 ; _⊢v_⦂_ = _⊢_⦂_
              ; ∋→⊢v-var→val = λ ∋x → ⊢` ∋x
              ; ext-⊢v = λ {M} ⊢M → rename-pres ⊢M (λ z → z)
              ; ⊢v→⊢ = λ x → x ; ⊢v0 = λ {B}{Δ} → ⊢` refl }
open PreserveMap SubstPres using ()
    renaming (preserve-map to subst-pres) public

substitution : ∀{Γ A B M N}
   → Γ ⊢ M ⦂ A
   → (A ∷ Γ) ⊢ N ⦂ B
     ---------------
   → Γ ⊢ N [ M ] ⦂ B
substitution {Γ}{A}{B}{M}{N} ⊢M ⊢N =
    subst-pres {σ = M • ↑ 0} ⊢N (λ {x} → ext⦂ {x})
    where
    ext⦂ : (M • ↑ 0) ⦂ A ∷ Γ ⇒ Γ
    ext⦂ {zero} {B} refl = ⊢M
    ext⦂ {suc x} {B} ∋x = ⊢` ∋x

preserve : ∀ {Γ M N A}
  → Γ ⊢ M ⦂ A
  → M —→ N
    ----------
  → Γ ⊢ N ⦂ A
preserve (⊢· ⊢L ⊢M refl) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M refl
preserve (⊢· ⊢L ⊢M refl) (ξ-·₂ M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) refl
preserve (⊢ƛ ⊢M refl) (ξ-ƛ M—→N) = ⊢ƛ (preserve ⊢M M—→N) refl
preserve (⊢· (⊢ƛ ⊢N refl) ⊢M refl) β-ƛ = substitution ⊢M ⊢N
