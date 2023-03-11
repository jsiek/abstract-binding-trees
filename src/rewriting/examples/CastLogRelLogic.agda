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

pre-𝓥 : (Type × Term) → Fun (Type × Term) ⊤ Wellfounded
pre-𝓥 (★ , op-inject {G} g ⦅ cons (ast V) nil ⦆) =
    ▷ᶠ (recur (G , V))
pre-𝓥 ($ₜ ι , op-lit {ι′} c ⦅ nil ⦆) = {!!}
pre-𝓥 (A ⇒ B , V) = {!!}

-- bogus cases for ★
pre-𝓥 (★ , ` x) = {!!}
pre-𝓥 (★ , $ c) = {!!}
pre-𝓥 (★ , ƛ N) = {!!}
pre-𝓥 (★ , L · M) = {!!}
pre-𝓥 (★ , M ⟨ h ?⟩) = {!!}
pre-𝓥 (★ , blame) = {!!}
-- bogus cases for ι
pre-𝓥 ($ₜ ι , ` x) = {!!}
pre-𝓥 ($ₜ ι , ƛ N) = {!!}
pre-𝓥 ($ₜ ι , L · M) = {!!}
pre-𝓥 ($ₜ ι , M ⟨ g !⟩) = {!!}
pre-𝓥 ($ₜ ι , M ⟨ h ?⟩) = {!!}
pre-𝓥 ($ₜ ι , blame) = {!!}


𝓥⟦_⟧ : (A : Type) → Term → Setᵒ
𝓥⟦ A ⟧ V = μᶠ (flip pre-𝓥) (A , V)


-- pre-𝓔 : Predᵒ (Type × Term) → Predᵒ (Type × Term)
-- pre-𝓔 𝓥 (A , M) = ∀ᵒ(λ N → (M —↠ N)ᵒ →ᵒ (irred N)ᵒ
--                       →ᵒ (𝓥 (A , N) ⊎ᵒ (N ≡ blame)ᵒ))

-- pre-𝓥 : Predᵒ (Type × Term) → Predᵒ (Type × Term)
-- pre-𝓥 𝓥 (★ , (op-inject {G} g ⦅ cons (ast V) nil ⦆)) = 𝓥 (G , V)
-- pre-𝓥 𝓥 ($ₜ ι , ((op-lit {ι′} c) ⦅ nil ⦆)) = (ι ≡ ι′)ᵒ
-- pre-𝓥 𝓥 (A ⇒ B , ƛ N) = ∀ᵒ(λ W → 𝓥 (A , W) →ᵒ pre-𝓔 𝓥 (A , N [ W ]))
-- -- bogus cases for ★
-- pre-𝓥 𝓥 (★ , ` x) = ⊥ᵒ
-- pre-𝓥 𝓥 (★ , $ c) = ⊥ᵒ
-- pre-𝓥 𝓥 (★ , ƛ N) = ⊥ᵒ
-- pre-𝓥 𝓥 (★ ,  L · M) = ⊥ᵒ
-- pre-𝓥 𝓥 (★ , M ⟨ h ?⟩) = ⊥ᵒ
-- pre-𝓥 𝓥 (★  , blame ) = ⊥ᵒ
-- -- bogus cases for $ₜ ι
-- pre-𝓥 𝓥 ($ₜ ι , ` x) = ⊥ᵒ
-- pre-𝓥 𝓥 ($ₜ ι , ƛ N) = ⊥ᵒ
-- pre-𝓥 𝓥 ($ₜ ι , L · M) = ⊥ᵒ
-- pre-𝓥 𝓥 ($ₜ ι , M ⟨ h ?⟩) = ⊥ᵒ
-- pre-𝓥 𝓥 ($ₜ ι , M ⟨ g !⟩) = ⊥ᵒ
-- pre-𝓥 𝓥 ($ₜ ι , blame) = ⊥ᵒ
-- -- bogus cases for A ⇒ B
-- pre-𝓥 𝓥 (A ⇒ B , ` x) = ⊥ᵒ
-- pre-𝓥 𝓥 (A ⇒ B , $ c) = ⊥ᵒ
-- pre-𝓥 𝓥 (A ⇒ B , L · M) = ⊥ᵒ
-- pre-𝓥 𝓥 (A ⇒ B , M ⟨ h ?⟩) = ⊥ᵒ
-- pre-𝓥 𝓥 (A ⇒ B , M ⟨ g !⟩) = ⊥ᵒ
-- pre-𝓥 𝓥 (A ⇒ B , blame) = ⊥ᵒ

-- 𝓥⟦_⟧ : (A : Type) → Term → Setᵒ
-- 𝓥⟦ A ⟧ V = μᵖ pre-𝓥 (A , V)


-- 𝓔⟦_⟧ : (A : Type) → Term → Setᵒ
-- 𝓔⟦ A ⟧ M = ∀ᵒ(λ N → (M —↠ N)ᵒ →ᵒ (irred N)ᵒ →ᵒ (𝓥⟦ A ⟧ N) ⊎ᵒ (N ≡ blame)ᵒ)

