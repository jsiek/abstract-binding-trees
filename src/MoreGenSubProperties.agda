import AbstractBindingTree
open import GenericSubstitution
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

module MoreGenSubProperties (Op : Set) (sig : Op → List ℕ)
  {V : Set}
  (S : Substable V)
  (val→abt : V → AbstractBindingTree.ABT Op sig)
  (val→abt∘var→val : ∀ x → val→abt (Substable.var→val S x) ≡ AbstractBindingTree.`_ x)
  where

open AbstractBindingTree Op sig
open Substable S
open SNF
open import GenericSubProperties S
open GenericSub V var→val shift
open GenericSubst V var→val shift Op sig val→abt val→abt∘var→val

⟪id⟫ : ∀ σ M  →  (∀ x → ⧼ σ ⧽ x ≡ var→val x) →  ⟪ σ ⟫ M ≡ M
⟪id⟫ₐ : ∀ σ b (arg : Arg b) →  (∀ x → ⧼ σ ⧽ x ≡ var→val x)
   → s-arg (fold-arg σ arg) ≡ arg
⟪id⟫ₐ₊ : ∀ σ bs (args : Args bs) →  (∀ x → ⧼ σ ⧽ x ≡ var→val x)
   → s-args (fold-args σ args) ≡ args

⟪id⟫ σ (` x) σ-id
    rewrite σ-id x = val→abt∘var→val x
⟪id⟫ σ (op ⦅ args ⦆) σ-id = cong (_⦅_⦆ op) (⟪id⟫ₐ₊ σ (sig op) args σ-id)

⟪id⟫ₐ σ zero (ast M) σ-id = cong ast (⟪id⟫ σ M σ-id)
⟪id⟫ₐ σ (suc b) (bind arg) σ-id =
    cong bind (⟪id⟫ₐ (extend σ (var→val 0)) b arg (extend-id {σ} σ-id))
⟪id⟫ₐ₊ σ [] nil σ-id = refl
⟪id⟫ₐ₊ σ (b ∷ bs) (cons arg args) σ-id =
    cong₂ cons (⟪id⟫ₐ σ b arg σ-id) (⟪id⟫ₐ₊ σ bs args σ-id)




{-
module Params
  (⦑id⦒ : ∀ v → ⦑ id ⦒ v ≡ v)
  where
-}
  
  
  
