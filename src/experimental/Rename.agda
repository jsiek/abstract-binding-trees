{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Syntax using (Substitution; ↑; _•_; Substable)
open import Var

module experimental.Rename (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig
open import experimental.Map Op sig

Rename : Set
Rename = Substitution Var

RenameIsSubstable : Substable Var
RenameIsSubstable = record { var→val = λ x → x ; shift = suc
    ; var→val-suc-shift = λ {x} → refl }

RenameIsMap : Map Var 
RenameIsMap = record { “_” = `_ ; S = RenameIsSubstable }
open Map RenameIsMap renaming (map-abt to rename; map-arg to ren-arg) public
open Map.GS RenameIsMap using ()
    renaming (⧼_⧽ to ⦉_⦊; g-ext to ext; g-inc to inc;
    g-drop to dropr; g-ext-cong to ext-cong;
    g-drop-add to dropr-add; g-drop-drop to dropr-dropr;
    g-drop-ext to dropr-ext; Shift to RenShift; g-Shift-var to ren-shift-var)
    public
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
compose-rename ρ₁ ρ₂ M = FusableMap.fusion FRR M
    where
    FRR : FusableMap RenameIsMap RenameIsMap
    FRR = record { ⌈_⌉ = ⦉_⦊ ; var = λ x ρ₁ ρ₂ → sym (seq-rename ρ₁ ρ₂ x)
          ; map-quote = λ v₁ ρ₂ → refl ; compose-ext = compose-ext}

rename-ext : ∀{ρ₁ ρ₂}{M : ABT}
   → (∀ x → ⦉ ρ₁ ⦊ x ≡ ⦉ ρ₂ ⦊ x)
   → rename ρ₁ M ≡ rename ρ₂ M
rename-ext {ρ₁}{ρ₂}{M} f = map-cong-abt {_}{ρ₁}{ρ₂} f M
  where
  MC : MapCong RenameIsMap RenameIsMap
  MC = record { _≈_ = λ ρ₁ ρ₂ → ∀ x → ⦉ ρ₁ ⦊ x ≡ ⦉ ρ₂ ⦊ x
              ; var = λ x f → cong `_ (f x) ; ext≈ = ext-cong }
  open MapCong MC
