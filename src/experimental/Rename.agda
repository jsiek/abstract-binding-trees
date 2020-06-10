{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Nat.Properties using (+-comm)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Var

module experimental.Rename (Op : Set) (sig : Op → List ℕ) where

open import GenericSubstitution
open import GenericSubstitution using ()
    renaming (g-drop to dropr; g-drop-drop to dropr-dropr) public
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
open GenericSubst RenameIsSubstable using ()
    renaming (⧼_⧽ to ⦉_⦊; g-ext to ext; g-inc to inc;
    g-ext-cong to ext-cong; g-inc-shift to inc-suc;
    g-drop-add to dropr-add;
    g-drop-inc to dropr-inc;
    g-drop-ext to dropr-ext; Shift to RenShift; g-Shift-var to ren-shift-var;
    ShftAbv to RenShftAbv; g-ext-ShftAbv to ext-ShftAbv;
    g-ShftAbv→Shift to ShftAbv→Shift)
    public
open ComposeMaps RenameIsMap RenameIsMap ⦉_⦊ (λ x → x)
    renaming (_⨟_ to _⨟ᵣ_) public

private
  ext-0 : ∀ ρ → ⦉ ext ρ ⦊ 0 ≡ 0
  ext-0 ρ = refl

ext-suc : ∀ ρ x → ⦉ ext ρ ⦊ (suc x) ≡ suc (⦉ ρ ⦊ x)
ext-suc ρ x rewrite inc-suc ρ x = refl

inc=⨟ᵣ↑ : ∀ ρ → inc ρ ≡ ρ ⨟ᵣ ↑ 1
inc=⨟ᵣ↑ (↑ k) rewrite +-comm k 1 = refl
inc=⨟ᵣ↑ (x • ρ) = cong (_•_ (suc x)) (inc=⨟ᵣ↑ ρ)

QRR : Quotable RenameIsMap RenameIsMap RenameIsMap
QRR = record
        { ⌈_⌉ = ⦉_⦊ ; val₂₃ = λ x → x ; quote-map = λ σ₂ v₁ → refl
        ; var→val₂₃ = λ x → refl ; quote-val₂₃ = λ v₂ → refl
        ; map₂-var→val₁ = λ x σ₂ → refl ; val₂₃-shift = λ v₂ → refl }

seq-rename : ∀ ρ₁ ρ₂ x → ⦉ ρ₁ ⨟ᵣ ρ₂ ⦊ x ≡ ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x)
seq-rename ρ₁ ρ₂ x = var-injective (Quotable.compose-sub QRR ρ₁ ρ₂ x)
{-# REWRITE seq-rename #-}

dropr-seq : ∀ k ρ ρ' → dropr k (ρ ⨟ᵣ ρ') ≡ (dropr k ρ ⨟ᵣ ρ')
dropr-seq = Quotable.g-drop-seq QRR
{-# REWRITE dropr-seq #-}

ren-assoc : ∀ {σ τ θ} → (σ ⨟ᵣ τ) ⨟ᵣ θ ≡ σ ⨟ᵣ τ ⨟ᵣ θ
ren-assoc {↑ k} {τ} {θ} = refl
ren-assoc {x • σ} {τ} {θ} rewrite ren-assoc {σ}{τ}{θ} = refl
{-# REWRITE ren-assoc #-}

{- why not other direction? -}
inc-seq : ∀ ρ₁ ρ₂ → (inc ρ₁ ⨟ᵣ ext ρ₂) ≡ inc (ρ₁ ⨟ᵣ ρ₂)
inc-seq (↑ k) ρ₂ = dropr-ext k ρ₂
inc-seq (x • ρ₁) ρ₂ rewrite inc-seq ρ₁ ρ₂ | inc-suc ρ₂ x = refl

compose-ext : ∀(ρ₁ ρ₂) → (ext ρ₁ ⨟ᵣ ext ρ₂) ≡ ext (ρ₁ ⨟ᵣ ρ₂)
compose-ext ρ₁ ρ₂ rewrite inc-seq ρ₁ ρ₂ = refl

compose-rename : ∀(ρ₁ ρ₂ : Rename)(M : ABT)
   → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ ⨟ᵣ ρ₂) M
compose-rename ρ₁ ρ₂ M = FusableMap.fusion FRR M
    where
    FRR : FusableMap RenameIsMap RenameIsMap RenameIsMap
    FRR = record { Q = QRR ; var = λ x ρ₁ ρ₂ → sym (seq-rename ρ₁ ρ₂ x)
                 ; compose-ext = compose-ext }

commute-↑1 : ∀ ρ M → rename (ext ρ) (rename (↑ 1) M) ≡ rename (↑ 1) (rename ρ M)
commute-↑1 ρ M =
  begin
      rename (ext ρ) (rename (↑ 1) M)
  ≡⟨ compose-rename (↑ 1) (ext ρ) M ⟩
      rename (↑ 1 ⨟ᵣ ext ρ)  M
  ≡⟨ refl ⟩
      rename (inc ρ)  M
  ≡⟨ cong (λ □ → rename □ M) (inc=⨟ᵣ↑ ρ) ⟩
      rename (ρ ⨟ᵣ ↑ 1) M
  ≡⟨ sym (compose-rename ρ (↑ 1) M) ⟩
      rename (↑ 1) (rename ρ M)
  ∎

rename-ext : ∀{ρ₁ ρ₂}{M : ABT}
   → (∀ x → ⦉ ρ₁ ⦊ x ≡ ⦉ ρ₂ ⦊ x)
   → rename ρ₁ M ≡ rename ρ₂ M
rename-ext {ρ₁}{ρ₂}{M} f = MapCong.map-cong-abt MC {_}{ρ₁}{ρ₂} f M
  where
  MC : MapCong RenameIsMap RenameIsMap
  MC = record { _≈_ = λ ρ₁ ρ₂ → ∀ x → ⦉ ρ₁ ⦊ x ≡ ⦉ ρ₂ ⦊ x
              ; var = λ x f → cong `_ (f x) ; ext≈ = ext-cong }

