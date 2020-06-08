{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Syntax using (Substitution; ↑; _•_)
open import Var

module experimental.Rename (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig
open import experimental.Map Op sig

Rename : Set
Rename = Substitution Var

RenameIsMap : Map Var 
RenameIsMap = record { “_” = `_ ; var→val = λ x → x ; shift = suc
    ; var→val-suc-shift = λ {x} → refl ; “_”-0 = refl }
open Map RenameIsMap renaming (map-abt to rename; map-arg to ren-arg) public
open Map.S RenameIsMap using ()
    renaming (⧼_⧽ to ⦉_⦊; g-ext to ext; g-inc to inc;
    g-drop to dropr;
    g-drop-add to dropr-add; g-drop-drop to dropr-dropr;
    g-drop-ext to dropr-ext) public
open ComposeMaps RenameIsMap RenameIsMap ⦉_⦊ renaming (_⨟_ to _⨟ᵣ_) public

seq-rename : ∀ ρ₁ ρ₂ x → ⦉ ρ₁ ⨟ᵣ ρ₂ ⦊ x ≡ ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x)
seq-rename (↑ k) ρ₂ x = dropr-add k ρ₂
seq-rename (x₁ • ρ₁) ρ₂ zero = refl
seq-rename (x₁ • ρ₁) ρ₂ (suc x) = seq-rename ρ₁ ρ₂ x
{-# REWRITE seq-rename #-}

dropr-seq : ∀ k ρ ρ' → dropr k (ρ ⨟ᵣ ρ') ≡ (dropr k ρ ⨟ᵣ ρ')
dropr-seq k (↑ k₁) ρ' = sym (dropr-dropr k k₁ ρ')
dropr-seq zero (x • ρ) ρ' = refl
dropr-seq (suc k) (x • ρ) ρ' = dropr-seq k ρ ρ'
{-# REWRITE dropr-seq #-}

ren-assoc : ∀ {σ τ θ} → (σ ⨟ᵣ τ) ⨟ᵣ θ ≡ σ ⨟ᵣ τ ⨟ᵣ θ
ren-assoc {↑ k} {τ} {θ} = refl
ren-assoc {x • σ} {τ} {θ} rewrite ren-assoc {σ}{τ}{θ} = refl
{-# REWRITE ren-assoc #-}

{- why not other direction? -}
inc-seq : ∀ ρ₁ ρ₂ → (inc ρ₁ ⨟ᵣ ext ρ₂) ≡ inc (ρ₁ ⨟ᵣ ρ₂)
inc-seq (↑ k) ρ₂ = dropr-ext k ρ₂
inc-seq (x • ρ₁) ρ₂ rewrite inc-seq ρ₁ ρ₂ = refl

compose-ext : ∀(ρ₁ ρ₂) → (ext ρ₁ ⨟ᵣ ext ρ₂) ≡ ext (ρ₁ ⨟ᵣ ρ₂)
compose-ext ρ₁ ρ₂ rewrite inc-seq ρ₁ ρ₂ = refl

compose-rename : ∀(ρ₁ ρ₂ : Rename)(M : ABT)
   → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ ⨟ᵣ ρ₂) M
compose-rename ρ₁ ρ₂ M = fusion M
    where
    Fus : FusableMap RenameIsMap RenameIsMap
    Fus = record { ⌈_⌉ = ⦉_⦊ ; var = λ x ρ₁ ρ₂ → sym (seq-rename ρ₁ ρ₂ x)
        ; map-quote = λ v₁ ρ₂ → refl ; compose-ext = compose-ext}
    open FusableMap Fus
