{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastSafeLogic2 where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤ᵖ; tt to ttᵖ)
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
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.StepIndexedLogic2
open import rewriting.examples.CastLogRelLogic2

{-# REWRITE sub-var #-}

compatibility-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatibility-var {Γ}{A}{x} ∋x γ =
     let ⊢𝓥γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ A ⟧ (γ x)
         ⊢𝓥γx = lemma-𝓖 Γ γ ∋x in
     let ⊢𝓔γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⟧ (γ x)
         ⊢𝓔γx = 𝓥⇒𝓔{A}{𝓖⟦ Γ ⟧ γ} ⊢𝓥γx in
     ⊢𝓔γx

