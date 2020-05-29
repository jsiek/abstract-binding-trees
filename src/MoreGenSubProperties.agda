{-# OPTIONS --rewriting #-}

import AbstractBindingTree
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import GenericSubstitution
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
    using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

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
open GenericSubst V var→val shift Op sig val→abt {-val→abt∘var→val-}

⟪id⟫ : ∀ σ M  →  (∀ x → ⧼ σ ⧽ x ≡ var→val x) →  ⟪ σ ⟫ M ≡ M
⟪id⟫ₐ : ∀ σ b (arg : Arg b) →  (∀ x → ⧼ σ ⧽ x ≡ var→val x)
   → s-arg (⟪ σ ⟫ₐ arg) ≡ arg
⟪id⟫₊ : ∀ σ bs (args : Args bs) →  (∀ x → ⧼ σ ⧽ x ≡ var→val x)
   → s-args (⟪ σ ⟫₊ args) ≡ args

⟪id⟫ σ (` x) σ-id
    rewrite σ-id x = val→abt∘var→val x
⟪id⟫ σ (op ⦅ args ⦆) σ-id = cong (_⦅_⦆ op) (⟪id⟫₊ σ (sig op) args σ-id)

⟪id⟫ₐ σ zero (ast M) σ-id = cong ast (⟪id⟫ σ M σ-id)
⟪id⟫ₐ σ (suc b) (bind arg) σ-id =
    cong bind (⟪id⟫ₐ (extend σ (var→val 0)) b arg (extend-id {σ} σ-id))
⟪id⟫₊ σ [] nil σ-id = refl
⟪id⟫₊ σ (b ∷ bs) (cons arg args) σ-id =
    cong₂ cons (⟪id⟫ₐ σ b arg σ-id) (⟪id⟫₊ σ bs args σ-id)

module Params
  (⦑σ⦒-head : ∀ σ v → ⦑ v • σ ⦒ (var→val 0) ≡ v)
  (⦑σ⦒-tail : ∀ σ v w → ⦑ w • σ ⦒ (shift v) ≡ ⦑ σ ⦒ v)
  (⟪σ⟫-⦑σ⦒ : ∀ σ v → ⟪ σ ⟫ (val→abt v) ≡ val→abt (⦑ σ ⦒ v))
  (inc-shift : ∀ σ v → ⦑ gen-inc σ ⦒ v ≡ shift (⦑ σ ⦒ v))
  where

  inc-seq : ∀ σ₁ σ₂ → (gen-inc σ₁ ⨟ extend σ₂ (var→val 0)) ≡ gen-inc (σ₁ ⨟ σ₂)
  inc-seq (↑ k) σ₂ =
    begin
      gen-inc (↑ k) ⨟ extend σ₂ (var→val 0)
    ≡⟨⟩
      drop k (gen-inc σ₂)
    ≡⟨ drop-inc k σ₂ ⟩
      gen-inc (drop k σ₂)
    ≡⟨⟩      
      gen-inc (↑ k ⨟ σ₂)
    ∎
  inc-seq (v • σ₁) σ₂ =
    begin
      gen-inc (v • σ₁) ⨟ extend σ₂ (var→val 0)
    ≡⟨⟩
      ⦑ var→val 0 • gen-inc σ₂ ⦒ (shift v)
        • (gen-inc σ₁ ⨟ extend σ₂ (var→val 0))
    ≡⟨ cong₂ _•_ (⦑σ⦒-tail (gen-inc σ₂) v (var→val 0)) (inc-seq σ₁ σ₂) ⟩
      ⦑ gen-inc σ₂ ⦒ v
        • gen-inc (σ₁ ⨟ σ₂)
    ≡⟨ cong₂ _•_ (inc-shift σ₂ v) refl ⟩
      shift (⦑ σ₂ ⦒ v)
        • gen-inc (σ₁ ⨟ σ₂)
    ≡⟨⟩
      gen-inc (v • σ₁ ⨟ σ₂)
    ∎
  
  extend-seq : ∀ {σ₁} {σ₂}
     → extend σ₁ (var→val 0) ⨟ extend σ₂ (var→val 0)
       ≡ extend (σ₁ ⨟ σ₂) (var→val 0)
  extend-seq {↑ k} {σ₂}
      rewrite drop-inc k σ₂ | ⦑σ⦒-head (gen-inc σ₂) (var→val 0) =
    cong₂ _•_ refl refl
  extend-seq {v • σ₁} {σ₂}
      rewrite extend-0 σ₂ (var→val 0)
      | ⦑σ⦒-head (gen-inc σ₂) (var→val 0)
      | ⦑σ⦒-tail (gen-inc σ₂) v (var→val 0)
      | inc-seq σ₁ σ₂
      | inc-shift σ₂ v = refl

  sub-sub : ∀{M σ₁ σ₂}  →  ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
  sub-sub-arg : ∀{b}{arg : Arg b}{σ₁ σ₂}
     → s-arg (⟪ σ₂ ⟫ₐ (s-arg (⟪ σ₁ ⟫ₐ arg))) ≡ s-arg (⟪ σ₁ ⨟ σ₂ ⟫ₐ arg)
  sub-sub-args : ∀{bs}{args : Args bs}{σ₁ σ₂}
     → s-args (⟪ σ₂ ⟫₊ (s-args (⟪ σ₁ ⟫₊ args))) ≡ s-args (⟪ σ₁ ⨟ σ₂ ⟫₊ args)
     
  sub-sub {` x} {σ₁} {σ₂} rewrite seq-subst σ₁ σ₂ x = ⟪σ⟫-⦑σ⦒ σ₂ (⧼ σ₁ ⧽ x)
  sub-sub {op ⦅ args ⦆} {σ₁} {σ₂} = cong (_⦅_⦆ op) sub-sub-args
  sub-sub-arg {zero} {ast M} {σ₁} {σ₂} = cong ast (sub-sub {M = M})
  sub-sub-arg {suc b} {bind arg} {σ₁} {σ₂} =
    cong bind G
    where
    IH = (sub-sub-arg {b}{arg}{extend σ₁ (var→val 0)}{extend σ₂ (var→val 0)})
    G = begin
          s-arg (⟪ σ₂ ⟫ₐ (s-arg (⟪ σ₁ ⟫ₐ (bind arg))) (var→val 0))
        ≡⟨⟩
          s-arg (⟪ extend σ₂ (var→val 0) ⟫ₐ
                    (s-arg  (⟪ extend σ₁ (var→val 0) ⟫ₐ arg)))
        ≡⟨ IH ⟩
          s-arg (⟪ extend σ₁ (var→val 0) ⨟ extend σ₂ (var→val 0) ⟫ₐ arg)
        ≡⟨ cong (λ □ → s-arg (⟪ □ ⟫ₐ arg)) (extend-seq {σ₁}{σ₂}) ⟩
          s-arg (⟪ extend (σ₁ ⨟ σ₂) (var→val 0) ⟫ₐ arg)
        ≡⟨⟩
          s-arg (⟪ σ₁ ⨟ σ₂ ⟫ₐ (bind arg) (var→val 0))
        ∎
  sub-sub-args {[]} {nil} {σ₁} {σ₂} = refl
  sub-sub-args {b ∷ bs} {cons arg args} {σ₁} {σ₂} =
      cong₂ cons (sub-sub-arg {b}{arg}{σ₁}{σ₂})
                 (sub-sub-args {bs} {args} {σ₁} {σ₂})


