open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open Eq.≡-Reasoning
open import Var 

module Renaming where

open import Environment using (Env)
open Env {{...}}
open import GenericSubstitution 
    
{----------------------------------------------------------------------------
                             Renaming
 ---------------------------------------------------------------------------}

Rename : Set
Rename = GSubst Var

ext-0 : ∀ (ρ : Rename) → ⟅ ext ρ ⟆ 0 ≡ 0
ext-0 ρ = refl

ext-suc : ∀ (ρ : Rename) x → ⟅ ext ρ ⟆ (suc x) ≡ suc (⟅ ρ ⟆ x)
ext-suc ρ x rewrite inc-shift ρ x = refl

module WithOpSig (Op : Set) (sig : Op → List ℕ)  where

  open import AbstractBindingTree Op sig
  open import Environment

  open import Map Op sig

  instance
    _ : Quotable Var
    _ = Var-is-Quotable
    
  rename : Rename → ABT → ABT
  rename = map

  open Composition Op sig using (ComposableProps)
  
  instance
    Ren-Composable : Composable Var Var Var
    Ren-Composable = record { ⌈_⌉ = ⟅_⟆ ; val₂₃ = λ x → x }

    Ren-ComposableProps : ComposableProps Var Var Var
    Ren-ComposableProps = record { var→val₂₃ = λ x → refl
        ; quote-val₂₃ = λ v₂ → refl ; val₂₃-shift = λ v₂ → refl
        ; quote-var→val₁ = λ x → refl ; quote-map = λ σ₂ v₁ → refl }

  instance
    ABT-is-Shiftable : Shiftable ABT
    ABT-is-Shiftable = record { var→val = `_ ; ⇑ = rename (↑ 1)
                       ; var→val-suc-shift = λ {x} → refl }
    ABT-is-Quotable : Quotable ABT
    ABT-is-Quotable = record { “_” = λ x → x }

  ren-up-seq : ∀ k (ρ : Rename) → ↑ k ⨟ ρ ≡ drop k ρ
  ren-up-seq k ρ rewrite up-seq k ρ | map-sub-id (drop k ρ) = refl

  ren-cons-seq : ∀ x (ρ₁ ρ₂ : Rename) → (x • ρ₁) ⨟ ρ₂ ≡ ⟅ ρ₂ ⟆ x • (ρ₁ ⨟ ρ₂)
  ren-cons-seq x ρ₁ ρ₂ rewrite cons-seq x ρ₁ ρ₂ = refl

  ren-head : ∀ (ρ : Rename) x → rename (x • ρ) (` 0) ≡ ` x
  ren-head ρ x = refl

  ren-tail : ∀ (ρ : Rename) x → (↑ 1 ⨟ x • ρ) ≡ ρ
  ren-tail ρ x rewrite ren-up-seq 1 (x • ρ) | drop-0 ρ = refl

  inc=⨟ᵣ↑ : ∀ (ρ : Rename) → ⟰ ρ ≡ ρ ⨟ ↑ 1
  inc=⨟ᵣ↑ (↑ k) rewrite ren-up-seq k (↑ 1) | +-comm k 1 = refl
  inc=⨟ᵣ↑ (x • ρ) rewrite ren-cons-seq x ρ (↑ 1) | inc=⨟ᵣ↑ ρ = refl

  ext-cons-shift : ∀ (ρ : Rename) → ext ρ ≡ (0 • (ρ ⨟ ↑ 1))
  ext-cons-shift ρ rewrite inc=⨟ᵣ↑ ρ = refl

  ren-η : ∀ (ρ : Rename) x → ⟅ ⟅ ρ ⟆ 0 • (↑ 1 ⨟ ρ) ⟆ x ≡ ⟅ ρ ⟆ x
  ren-η ρ 0 = refl
  ren-η ρ (suc x) rewrite ren-up-seq 1 ρ | drop-add 1 ρ x = refl

  ren-idL : ∀ (ρ : Rename) → id ⨟ ρ ≡ ρ
  ren-idL ρ rewrite ren-up-seq 0 ρ | drop-0 ρ = refl

  ren-dist :  ∀ x (ρ : Rename) τ → ((x • ρ) ⨟ τ) ≡ ((⟅ τ ⟆ x) • (ρ ⨟ τ))
  ren-dist x ρ τ rewrite ren-cons-seq x ρ τ = refl

  {------ Composing renamings -------}

  open Composition Op sig using (compose-sub; drop-seq)

  seq-rename : ∀ (ρ₁ ρ₂ : Rename) x → ⟅ ρ₁ ⨟ ρ₂ ⟆ x ≡ ⟅ ρ₂ ⟆ (⟅ ρ₁ ⟆ x)
  seq-rename ρ₁ ρ₂ x = var-injective (compose-sub ρ₁ ρ₂ x)

  ren-assoc : ∀ (σ τ θ : Rename) → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  ren-assoc (↑ k) τ θ rewrite ren-up-seq k τ
      | ren-up-seq k (τ ⨟ θ) | drop-seq k τ θ = refl
  ren-assoc (x • σ) τ θ = begin
    (x • σ ⨟ τ) ⨟ θ               ≡⟨ cong (λ □ → □ ⨟ θ) (ren-cons-seq _ _ _) ⟩
    (⟅ τ ⟆ x • (σ ⨟ τ)) ⨟ θ          ≡⟨  ren-cons-seq _ _ _ ⟩
    (⟅ θ ⟆ (⟅ τ ⟆ x)) • ((σ ⨟ τ) ⨟ θ)
                       ≡⟨ cong₂ _•_ (sym (seq-rename _ _ _)) (ren-assoc _ _ _) ⟩
    ⟅ τ ⨟ θ ⟆ x • (σ ⨟ (τ ⨟ θ))     ≡⟨ sym (ren-cons-seq _ _ _) ⟩
    (x • σ) ⨟ (τ ⨟ θ)               ∎

  ren-map-fusion-ext : ∀{ρ₁ : Rename}{ρ₂ : Rename}{ρ₃ : Rename}
                → ρ₂ ∘ ρ₁ ≈ ρ₃ → ext ρ₂ ∘ ext ρ₁ ≈ ext ρ₃
  ren-map-fusion-ext {ρ₁} {ρ₂} {ρ₃} ρ₂∘ρ₁≈ρ₃ zero = refl
  ren-map-fusion-ext {ρ₁} {ρ₂} {ρ₃} ρ₂∘ρ₁≈ρ₃ (suc x) rewrite inc-shift ρ₁ x
     | inc-shift ρ₃ x | inc-shift ρ₂ (⟅ ρ₁ ⟆ x) = 
     cong `_ (cong suc (var-injective (ρ₂∘ρ₁≈ρ₃ x)))

  compose-rename : ∀ (ρ₁ : Rename) (ρ₂ : Rename) M
     → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ ⨟ ρ₂) M
  compose-rename ρ₁ ρ₂ M =
      map-map-fusion-ext M (λ x → sym (cong `_ (seq-rename ρ₁ ρ₂ x)))
          ren-map-fusion-ext

  commute-↑1 : ∀ ρ M
     → rename (ext ρ) (rename (↑ 1) M) ≡ rename (↑ 1) (rename ρ M)
  commute-↑1 ρ M = begin
      rename (ext ρ) (rename (↑ 1) M)  ≡⟨ compose-rename (↑ 1) (ext ρ) M ⟩
      rename (↑ 1 ⨟ (ext ρ)) M
                        ≡⟨ cong (λ □ → rename (↑ 1 ⨟ □) M) (ext-cons-shift _) ⟩
      rename (↑ 1 ⨟ (0 • (ρ ⨟ ↑ 1))) M
                                     ≡⟨ cong (λ □ → rename □ M) (ren-tail _ _) ⟩
      rename (ρ ⨟ ↑ 1) M              ≡⟨ sym (compose-rename ρ (↑ 1) M) ⟩
      rename (↑ 1) (rename ρ M)        ∎

  rename-cong : ∀ ρ₁ ρ₂ M
     → (∀ x → ⟅ ρ₁ ⟆ x ≡ ⟅ ρ₂ ⟆ x)
     → rename ρ₁ M ≡ rename ρ₂ M
  rename-cong ρ₁ ρ₂ M f =
      map-cong M (λ x → cong `_ (f x))
              (λ ρ₁≈ρ₂ x → cong `_ (ext-cong (λ x → var-injective (ρ₁≈ρ₂ x)) x))

