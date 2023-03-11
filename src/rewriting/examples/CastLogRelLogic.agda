{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastLogRelLogic where

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
open import rewriting.examples.StepIndexedLogic

pre-𝓔 : (Type × Term) → Fun (Type × Term) ⊤ Wellfounded DownClosed
pre-𝓔 (A , M) = ∀ᵍ λ N → (index (λ k → Σ[ r ∈ M —↠ N ] len r < k))
                        →ᶠ (irred N)ᶠ
                        →ᶠ ((▷ᶠ (recur (A , N))) ⊎ᶠ (N ≡ blame)ᶠ)

pre-𝓥 : (Type × Term) → Fun (Type × Term) ⊤ Wellfounded DownClosed
pre-𝓥 (★ , op-inject {G} g ⦅ cons (ast V) nil ⦆) =
    ▷ᶠ (recur (G , V))
pre-𝓥 ($ₜ ι , op-lit {ι′} c ⦅ nil ⦆) = (ι ≡ ι′)ᶠ
pre-𝓥 (A ⇒ B , ƛ N) = ∀ᵍ λ W → (▷ᶠ (recur (A , W)) →ᶠ pre-𝓔 (A , N [ W ]))

-- bogus cases for ★
pre-𝓥 (★ , ` x) = (⊥)ᶠ
pre-𝓥 (★ , $ c) = (⊥)ᶠ
pre-𝓥 (★ , ƛ N) = (⊥)ᶠ
pre-𝓥 (★ , L · M) = (⊥)ᶠ
pre-𝓥 (★ , M ⟨ h ?⟩) = (⊥)ᶠ
pre-𝓥 (★ , blame) = (⊥)ᶠ
-- bogus cases for ι
pre-𝓥 ($ₜ ι , ` x) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , ƛ N) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , L · M) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , M ⟨ g !⟩) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , M ⟨ h ?⟩) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , blame) = (⊥)ᶠ
-- bogus cases for A ⇒ B
pre-𝓥 (A ⇒ B , ` x) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , $ c) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , L · M) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , M ⟨ g !⟩) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , M ⟨ h ?⟩) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , blame) = (⊥)ᶠ

𝓥⟦_⟧ : (A : Type) → Term → Setᵒ
𝓥⟦ A ⟧ V = μᶠ (flip pre-𝓥) (A , V)

𝓔⟦_⟧ : (A : Type) → Term → Setᵒ
𝓔⟦ A ⟧ V = fun (pre-𝓔 (A , V)) (μᶠ (flip pre-𝓥)) tt



