{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastSafeLogic where

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
open import rewriting.examples.CastLogRelLogic

{-# REWRITE sub-var #-}

compatibility-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatibility-var {Γ}{A}{x} ∋x k γ 𝓖Γγk =
  let Vγx = lemma-𝓖 Γ γ k 𝓖Γγk ∋x in
  Val⇒Exp {A}{⟪ γ ⟫ (` x)} k Vγx

compatible-nat : ∀{Γ}{n : ℕ} → Γ ⊨ ($ n) ⦂ ($ₜ ′ℕ)
compatible-nat {Γ}{n} k γ 𝓖Γγk = Val⇒Exp{$ₜ ′ℕ} k (G k)
    where G : ∀ k → 𝓥⟦ $ₜ ′ℕ ⟧ ($ n) k
          G zero = tt
          G (suc k) = subst (λ X → X) (sym (V-base{k}{′ℕ}{′ℕ}{n})) refl

compatible-bool : ∀{Γ}{b : 𝔹} → Γ ⊨ ($ b) ⦂ ($ₜ ′𝔹)
compatible-bool {Γ}{b} k γ 𝓖Γγk = Val⇒Exp{$ₜ ′𝔹} k (G k)
    where G : ∀ k → 𝓥⟦ $ₜ ′𝔹 ⟧ ($ b) k
          G zero = tt
          G (suc k) = subst (λ X → X) (sym (V-base{k}{′𝔹}{′𝔹}{b})) refl

