{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastLogRelLogic where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
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
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import Structures using (extensionality)
open import rewriting.examples.Cast
open import rewriting.examples.StepIndexedLogic

𝓔⟦_⟧ : (A : Type) → Term → Setₖ

𝓥⟦_⟧ : (A : Type) → Term → Setₖ
𝓥⟦ ★ ⟧ (` x) = ⊥ₖ
𝓥⟦ ★ ⟧ ($ c) = ⊥ₖ
𝓥⟦ ★ ⟧ (ƛ N) = ⊥ₖ
𝓥⟦ ★ ⟧ (L · M) = ⊥ₖ
𝓥⟦ ★ ⟧ (op-inject {G} g ⦅ cons (ast V) nil ⦆) = ▷ (𝓥⟦ G ⟧ V)
𝓥⟦ ★ ⟧ (V ⟨ h ?⟩) = ⊥ₖ
𝓥⟦ ★ ⟧ blame = ⊥ₖ

𝓥⟦ $ₜ ι ⟧ (` x) = ⊥ₖ
𝓥⟦ $ₜ ι ⟧ ((op-lit {ι′} c) ⦅ nil ⦆) = (ι ≡ ι′)ₖ
𝓥⟦ $ₜ ι ⟧ (ƛ N) = ⊥ₖ
𝓥⟦ $ₜ ι ⟧ (L · M) = ⊥ₖ
𝓥⟦ $ₜ ι ⟧ (V ⟨ g !⟩) = ⊥ₖ
𝓥⟦ $ₜ ι ⟧ (V ⟨ h ?⟩) = ⊥ₖ
𝓥⟦ $ₜ ι ⟧ blame = ⊥ₖ

𝓥⟦ A ⇒ B ⟧ (` x) = ⊥ₖ
𝓥⟦ A ⇒ B ⟧ ($ c) = ⊥ₖ
𝓥⟦ A ⇒ B ⟧ (ƛ N) = ∀ₖ {Term} (λ W → 𝓥⟦ A ⟧ W →ₖ 𝓔⟦ B ⟧ (N [ W ]))
𝓥⟦ A ⇒ B ⟧ (L · M) = ⊥ₖ
𝓥⟦ A ⇒ B ⟧ (V ⟨ g !⟩) = ⊥ₖ
𝓥⟦ A ⇒ B ⟧ (V ⟨ h ?⟩) = ⊥ₖ
𝓥⟦ A ⇒ B ⟧ blame = ⊥ₖ
