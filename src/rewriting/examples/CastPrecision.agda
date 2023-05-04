{-# OPTIONS --rewriting #-}
{-
   A simple blame calculus partly based on a version 
   by Jeremy, Phil Wadler, and Peter Thiemann.
-}

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig hiding (Result)
open import Var
open import rewriting.examples.Cast

module rewriting.examples.CastPrecision where

src : Prec → Type
src (A , A′ , lt) = A

tgt : Prec → Type
tgt (A , A′ , lt) = A′

lookup-⊑-src : ∀{Γ}{A}{A′}{c}{x}
   → Γ ∋ x ⦂ (A , A′ , c)
   → map src Γ ∋ x ⦂ A
lookup-⊑-src {Γ = .(_ , _ , _) ∷ Γ} {x = zero} refl = refl
lookup-⊑-src {Γ = (B , B′ , b) ∷ Γ} {x = suc x} ∋x =
  lookup-⊑-src{Γ = Γ}{x = x} ∋x

lookup-⊑-tgt : ∀{Γ}{A}{A′}{c}{x}
   → Γ ∋ x ⦂ (A , A′ , c)
   → map tgt Γ ∋ x ⦂ A′
lookup-⊑-tgt {Γ = .(_ , _ , _) ∷ Γ} {x = zero} refl = refl
lookup-⊑-tgt {Γ = (B , B′ , b) ∷ Γ} {x = suc x} ∋x =
  lookup-⊑-tgt{Γ = Γ}{x = x} ∋x

precision→typed : ∀{Γ}{M}{M′}{A}{A′}{c : A ⊑ A′}
   → Γ ⊩ M ⊑ M′ ⦂ c
   → map src Γ ⊢ M ⦂ A  ×  map tgt Γ ⊢ M′ ⦂ A′ 
precision→typed{Γ} (⊑-var ∋x) =
  ⊢` (lookup-⊑-src{Γ} ∋x) , ⊢` (lookup-⊑-tgt{Γ} ∋x)
precision→typed{M = $ c} ⊑-lit = (⊢$ c) , (⊢$ c)
precision→typed (⊑-app L⊑L′ M⊑M′)
    with precision→typed L⊑L′ | precision→typed M⊑M′
... | ⊢L , ⊢L′ | ⊢M , ⊢M′ = (⊢· ⊢L ⊢M) , (⊢· ⊢L′ ⊢M′)
precision→typed (⊑-lam N⊑N′)
    with precision→typed N⊑N′
... | ⊢N , ⊢N′ = (⊢ƛ ⊢N) , (⊢ƛ ⊢N′)
precision→typed (⊑-inj-L M⊑M′)
    with precision→typed M⊑M′
... | ⊢M , ⊢M′ = (⊢⟨!⟩ ⊢M) , ⊢M′
precision→typed (⊑-inj-R M⊑M′)
    with precision→typed M⊑M′
... | ⊢M , ⊢M′ = ⊢M , ⊢⟨!⟩ ⊢M′
precision→typed (⊑-proj-L{H = H} M⊑M′) 
    with precision→typed M⊑M′
... | ⊢M , ⊢M′ = (⊢⟨?⟩ ⊢M H) , ⊢M′
precision→typed (⊑-proj-R{H = H} M⊑M′)
    with precision→typed M⊑M′
... | ⊢M , ⊢M′ = ⊢M , ⊢⟨?⟩ ⊢M′ H
precision→typed (⊑-blame x) = x , ⊢blame

{-------------      Proof of Progress    -------------}

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

  error :
      Blame M
      --------------
    → Progress M

progress : ∀ {M A}
  → [] ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢$ k)                           =  done ($̬ k)
progress (⊢ƛ ⊢N)                          =  done (ƛ̬ _)
progress (⊢· ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                          =  step (ξ (□· _) L—→L′)
... | error isBlame                       = step (ξ-blame (□· _))
... | done (ƛ̬ N)
    with progress ⊢M
... | step M—→M′                          =  step (ξ ((ƛ̬ _) ·□) M—→M′)
... | error isBlame                       = step (ξ-blame ((ƛ̬ _) ·□))
... | done w                              = step (β w)
progress (⊢⟨!⟩ ⊢M)
    with progress ⊢M
... | step M—→M′                          = step (ξ □⟨ _ !⟩ M—→M′)
... | error isBlame                       = step (ξ-blame □⟨ _ !⟩)
... | done v                              = done (v 〈 _ 〉)
progress (⊢⟨?⟩ ⊢M H) 
    with progress ⊢M
... | step M—→M′                          = step (ξ □⟨ _ ?⟩ M—→M′)
... | error isBlame                       = step (ξ-blame □⟨ _ ?⟩)
... | done v
    with v
... | v₁ 〈 G 〉
    with G ≡ᵍ H
... | yes refl                            = step (collapse v₁ refl)
... | no neq                              = step (collide v₁ neq refl)
progress ⊢blame                           = error isBlame


