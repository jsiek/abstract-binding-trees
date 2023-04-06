{-# OPTIONS --rewriting #-}
module rewriting.examples.CastDeterministic where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
--open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import Structures using (extensionality)
open import rewriting.examples.Cast

inject-eq : ∀{G}{N N′}
   → (N ⟨ G !⟩) ≡ (N′ ⟨ G !⟩)
   → N ≡ N′
inject-eq {G} {N} {.N} refl = refl

deterministic : ∀{M N N′}
  → M —→ N
  → M —→ N′
  → N ≡ N′
deterministic (ξ (□· M) M—→N) (ξ (□· M₁) M—→N′)
    with deterministic M—→N M—→N′
... | refl = refl
deterministic (ξ (□· M) M—→N) (ξ (v ·□) M—→N′) =
    ⊥-elim (value-irreducible v M—→N)
deterministic (ξ (□· M) M—→N) (ξ-blame (□· M₁)) =
    ⊥-elim (blame-irreducible M—→N)
deterministic (ξ (□· M) M—→N) (ξ-blame (v ·□)) =
    ⊥-elim (value-irreducible v M—→N)
deterministic (ξ (□· M) M—→N) (β v) =
    ⊥-elim (value-irreducible (ƛ̬ _) M—→N)
deterministic (ξ (v ·□) M—→N) (ξ (□· M) M—→N′) = 
    ⊥-elim (value-irreducible v M—→N′)
deterministic (ξ (v ·□) M—→N) (ξ (v₁ ·□) M—→N′)
    with deterministic M—→N M—→N′
... | refl = refl
deterministic (ξ (() ·□) M—→N) (ξ-blame (□· M))
deterministic (ξ (v ·□) M—→N) (ξ-blame (v₁ ·□)) =
    ⊥-elim (blame-irreducible M—→N)
deterministic (ξ (v ·□) M—→N) (β x) =
    ⊥-elim (value-irreducible x M—→N)
deterministic (ξ (□⟨ G !⟩) M—→N) (ξ (□⟨ _ !⟩) M—→N′)
    with deterministic M—→N M—→N′
... | refl = refl
deterministic (ξ (□⟨ G !⟩) M—→N) (ξ-blame (□⟨ _ !⟩)) =
    ⊥-elim (blame-irreducible M—→N)
deterministic (ξ (□⟨ H ?⟩) M—→N) (ξ (□⟨ _ ?⟩) M—→N′)
    with deterministic M—→N M—→N′
... | refl = refl
deterministic (ξ (□⟨ H ?⟩) M—→N) (ξ-blame (□⟨ _ ?⟩)) =
    ⊥-elim (blame-irreducible M—→N)
deterministic (ξ □⟨ H ?⟩ r) (collapse v refl) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (ξ □⟨ H ?⟩ r) (collide v neq refl) = 
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (ξ-blame (□· M)) (ξ (□· M₁) M—→N′) =
    ⊥-elim (blame-irreducible M—→N′)
deterministic (ξ-blame (□· M)) (ξ (() ·□) M—→N′)
deterministic (ξ-blame (□· M)) (ξ-blame (□· M₁)) = refl
deterministic (ξ-blame (□· M)) (ξ-blame (v ·□)) = refl
deterministic (ξ-blame (v ·□)) (ξ (□· M) M—→N′) =
    ⊥-elim (value-irreducible v M—→N′)
deterministic (ξ-blame (v ·□)) (ξ (v₁ ·□) M—→N′) =
    ⊥-elim (blame-irreducible M—→N′)
deterministic (ξ-blame (() ·□)) (ξ-blame (□· .blame))
deterministic (ξ-blame (v ·□)) (ξ-blame (v₁ ·□)) = refl
deterministic (ξ-blame (□⟨ G !⟩)) (ξ (□⟨ _ !⟩) M—→N′) =
    ⊥-elim (blame-irreducible M—→N′)
deterministic (ξ-blame (□⟨ G !⟩)) (ξ-blame (□⟨ _ !⟩)) = refl
deterministic (ξ-blame (□⟨ H ?⟩)) (ξ (□⟨ _ ?⟩) M—→N′) =
    ⊥-elim (blame-irreducible M—→N′)
deterministic (ξ-blame (□⟨ H ?⟩)) (ξ-blame (□⟨ _ ?⟩)) = refl
deterministic (β x) (ξ (□· M) M—→N′) = ⊥-elim (value-irreducible (ƛ̬ _) M—→N′)
deterministic (β x) (ξ (v ·□) M—→N′) = ⊥-elim (value-irreducible x M—→N′)
deterministic (β ()) (ξ-blame (v ·□))
deterministic (β x) (β x₁) = refl
deterministic (collapse v refl) (ξξ □⟨ _ ?⟩ refl refl r) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (collapse v refl) (ξξ-blame (□· M) ())
deterministic (collapse v refl) (ξξ-blame (v₁ ·□) ())
deterministic (collapse v refl) (ξξ-blame □⟨ _ !⟩ ())
deterministic (collapse v refl) (ξξ-blame □⟨ _ ?⟩ ())
deterministic (collapse v refl) (collapse x refl) = refl
deterministic (collapse v refl) (collide x neq refl) =
    ⊥-elim (neq refl)
deterministic (collide v neq refl) (ξξ □⟨ _ ?⟩ refl refl r) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) r)
deterministic (collide v neq refl) (ξξ-blame (□· M) ())
deterministic (collide v neq refl) (ξξ-blame (v₁ ·□) ())
deterministic (collide v neq refl) (ξξ-blame □⟨ _ !⟩ ())
deterministic (collide v neq refl) (ξξ-blame □⟨ _ ?⟩ ())
deterministic (collide v neq refl) (collapse x refl) =
    ⊥-elim (neq refl)
deterministic (collide v neq refl) (collide x x₁ x₂) = refl

frame-inv2 : ∀{L N : Term}{F}
   → reducible L
   → F ⟦ L ⟧ —→ N
   → ∃[ L′ ] ((L —→ L′) × (N ≡ F ⟦ L′ ⟧))
frame-inv2{L}{.((□· M₁) ⟦ _ ⟧)}{□· M} (L′ , L→L′) (ξξ (□· M₁) refl refl L→N) =
    L′ , (L→L′ , cong (λ X → X · M) (deterministic L→N L→L′))
frame-inv2 {L} {.((v ·□) ⟦ _ ⟧)} {□· M} (L′ , L→L′) (ξξ (v ·□) refl refl FL→N) =
   ⊥-elim (value-irreducible v L→L′)
frame-inv2 {L} {.blame} {□· M} (L′ , L→L′) (ξξ-blame (□· M₁) refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {.blame} {□· M} (L′ , L→L′) (ξξ-blame (v ·□) refl) =
    ⊥-elim (value-irreducible v L→L′)
frame-inv2 {ƛ N} {_} {□· M} (L′ , L→L′) (β x) =
    ⊥-elim (value-irreducible (ƛ̬ N) L→L′)
frame-inv2 {L} {N} {v ·□} (L′ , L→L′) (ξξ (□· M) refl refl FL→N) =
    ⊥-elim (value-irreducible v FL→N)
frame-inv2 {L} {N} {v ·□} (L′ , L→L′) (ξξ (v₁ ·□) refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {() ·□} (L′ , L→L′) (ξξ-blame (□· M) refl)
frame-inv2 {L} {.blame} {v ·□} (L′ , L→L′) (ξξ-blame (v₁ ·□) refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {_} {v ·□} (L′ , L→L′) (β w) =
    ⊥-elim (value-irreducible w L→L′)
frame-inv2 {L} {N} {□⟨ G !⟩} (L′ , L→L′) (ξξ □⟨ _ !⟩ refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {□⟨ G !⟩} (L′ , L→L′) (ξξ-blame □⟨ _ !⟩ refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {_} {□⟨ H ?⟩} (L′ , L→L′) (ξξ □⟨ _ ?⟩ refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {□⟨ H ?⟩} (L′ , L→L′) (ξξ-blame □⟨ _ ?⟩ refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {N} {□⟨ H ?⟩} (L′ , L→L′) (collapse v refl) = 
    ⊥-elim (value-irreducible (v 〈 _ 〉) L→L′)
frame-inv2 {L} {.blame} {□⟨ H ?⟩} (L′ , L→L′) (collide v neq refl) =
    ⊥-elim (value-irreducible (v 〈 _ 〉) L→L′)

