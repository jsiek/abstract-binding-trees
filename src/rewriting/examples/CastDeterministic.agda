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

inject-eq : ∀{G}{g : Ground G}{N N′}
   → (N ⟨ g !⟩) ≡ (N′ ⟨ g !⟩)
   → N ≡ N′
inject-eq {G} {g} {N} {.N} refl = refl

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
deterministic (ξ (□⟨ g !⟩) M—→N) (ξ (□⟨ g₁ !⟩) M—→N′)
    with deterministic M—→N M—→N′
... | refl = refl
deterministic (ξ (□⟨ g !⟩) M—→N) (ξ-blame (□⟨ g₁ !⟩)) =
    ⊥-elim (blame-irreducible M—→N)
deterministic (ξ (□⟨ h ?⟩) M—→N) (ξ (□⟨ h₁ ?⟩) M—→N′)
    with deterministic M—→N M—→N′
... | refl = refl
deterministic (ξ (□⟨ h ?⟩) M—→N) (ξ-blame (□⟨ h₁ ?⟩)) =
    ⊥-elim (blame-irreducible M—→N)
deterministic (ξ □⟨ h ?⟩ r) (collapse v g .h refl) =
    ⊥-elim (value-irreducible (v 〈 g 〉) r)
deterministic (ξ □⟨ h ?⟩ r) (collide v g .h neq refl) = 
    ⊥-elim (value-irreducible (v 〈 g 〉) r)
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
deterministic (ξ-blame (□⟨ g !⟩)) (ξ (□⟨ g₁ !⟩) M—→N′) =
    ⊥-elim (blame-irreducible M—→N′)
deterministic (ξ-blame (□⟨ g !⟩)) (ξ-blame (□⟨ g₁ !⟩)) = refl
deterministic (ξ-blame (□⟨ h ?⟩)) (ξ (□⟨ h₁ ?⟩) M—→N′) =
    ⊥-elim (blame-irreducible M—→N′)
deterministic (ξ-blame (□⟨ h ?⟩)) (ξ-blame (□⟨ h₁ ?⟩)) = refl
deterministic (β x) (ξ (□· M) M—→N′) = ⊥-elim (value-irreducible (ƛ̬ _) M—→N′)
deterministic (β x) (ξ (v ·□) M—→N′) = ⊥-elim (value-irreducible x M—→N′)
deterministic (β ()) (ξ-blame (v ·□))
deterministic (β x) (β x₁) = refl
--deterministic (collapse x g) (ξ (□↓ p) M—→N′) =
--    ⊥-elim (value-irreducible (x ⇑ g) M—→N′)
deterministic (collapse v g h refl) (ξξ □⟨ h₁ ?⟩ refl refl r) =
    ⊥-elim (value-irreducible (v 〈 g 〉) r)
deterministic (collapse v g h refl) (ξξ-blame (□· M) ())
deterministic (collapse v g h refl) (ξξ-blame (v₁ ·□) ())
deterministic (collapse v g h refl) (ξξ-blame □⟨ g₁ !⟩ ())
deterministic (collapse v g h refl) (ξξ-blame □⟨ h₁ ?⟩ ())
deterministic (collapse v g h refl) (collapse x g₁ h₁ refl) = refl
deterministic (collapse v g h refl) (collide x g₁ .h neq refl) =
    ⊥-elim (neq refl)
deterministic (collide v g h neq refl) (ξξ □⟨ h₁ ?⟩ refl refl r) =
    ⊥-elim (value-irreducible (v 〈 g 〉) r)
deterministic (collide v g h neq refl) (ξξ-blame (□· M) ())
deterministic (collide v g h neq refl) (ξξ-blame (v₁ ·□) ())
deterministic (collide v g h neq refl) (ξξ-blame □⟨ g₁ !⟩ ())
deterministic (collide v g h neq refl) (ξξ-blame □⟨ h₁ ?⟩ ())
deterministic (collide v g h neq refl) (collapse x g₁ .h refl) =
    ⊥-elim (neq refl)
deterministic (collide v g h neq refl) (collide x g₁ .h x₁ x₂) = refl

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
frame-inv2 {L} {N} {□⟨ g !⟩} (L′ , L→L′) (ξξ □⟨ g₁ !⟩ refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {□⟨ g !⟩} (L′ , L→L′) (ξξ-blame □⟨ g₁ !⟩ refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {_} {□⟨ h ?⟩} (L′ , L→L′) (ξξ □⟨ h₁ ?⟩ refl refl FL→N)
    with deterministic L→L′ FL→N
... | refl = L′ , (L→L′ , refl)
frame-inv2 {L} {.blame} {□⟨ h ?⟩} (L′ , L→L′) (ξξ-blame □⟨ h₁ ?⟩ refl) =
    ⊥-elim (blame-irreducible L→L′)
frame-inv2 {L} {N} {□⟨ h ?⟩} (L′ , L→L′) (collapse v g .h refl) = 
    ⊥-elim (value-irreducible (v 〈 g 〉) L→L′)
frame-inv2 {L} {.blame} {□⟨ h ?⟩} (L′ , L→L′) (collide v g .h neq refl) =
    ⊥-elim (value-irreducible (v 〈 g 〉) L→L′)

