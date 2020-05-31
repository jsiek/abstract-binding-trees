import AbstractBindingTree
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import GenericSubstitution
open import Var

module Rename (Op : Set) (sig : Op → List ℕ) where

  open AbstractBindingTree Op sig
      using (`_; _⦅_⦆; Arg; Args; ast; bind; nil; cons)
  open SNF using (Substitution; ↑; _•_) public

  Rename : Set
  Rename = Substitution Var

  open GenericSub Var (λ x → x) suc
    using (extend; drop-extend)
    renaming (⧼_⧽ to ⦉_⦊; drop to dropr; gen-inc to inc;
              drop-0 to dropr-0; drop-add to dropr-add;
              drop-inc to dropr-inc; drop-drop to dropr-dropr;
              gen-subst-is-env to rename-is-env) public

  ext : Rename → Rename
  ext ρ = extend ρ 0

  dropr-ext : ∀ k ρ → dropr (suc k) (ext ρ) ≡ inc (dropr k ρ)
  dropr-ext k ρ = drop-extend k ρ 0

  open GenericSubst Var (λ x → x) suc Op sig `_ 
      using ()
      renaming (gen-subst to rename;
                gen-subst-is-foldable to rename-is-foldable;
                s-arg to ren-res→arg; s-args to ren-res→args;
                ⟪_⟫ₐ to ren-arg; ⟪_⟫₊ to ren-args
                ) public
  import Fold
  open Fold.Folder rename-is-foldable
                
  rename-is-substable : Substable Var
  rename-is-substable = record
                          { var→val = λ x → x
                          ; shift = suc
                          ; ⦑_⦒ = ⦉_⦊
                          ; var→val-suc-shift = λ {x} → refl
                          ; sub-var→val = λ σ x → refl
                          ; shift-⦑↑1⦒ = λ v → refl
                          }
  open import GenericSubProperties rename-is-substable
    renaming (_⨟_ to _⨟ᵣ_; sub-tail to ren-tail;
              inc=⨟↑ to inc=⨟ᵣ↑; 
              sub-η to ren-η; sub-idL to ren-idL; sub-dist to ren-dist;
              seq-subst to seq-rename;
              extend-id to ext-id) public

  ext-cons-shift : ∀ ρ → ext ρ ≡ (0 • (ρ ⨟ᵣ ↑ 1))
  ext-cons-shift ρ = extend-cons-shift ρ 0

  ext-suc : ∀ ρ x → ⦉ ext ρ ⦊ (suc x) ≡ suc (⦉ ρ ⦊ x)
  ext-suc ρ x = extend-suc ρ 0 x

  inc-seq : ∀ ρ₁ ρ₂ → (inc ρ₁ ⨟ᵣ ext ρ₂) ≡ inc (ρ₁ ⨟ᵣ ρ₂)
  inc-seq (↑ k) ρ₂ = dropr-ext k ρ₂
  inc-seq (x • ρ₁) ρ₂ rewrite inc-seq ρ₁ ρ₂ | ext-suc ρ₂ x = refl

  open import MoreGenSubProperties Op sig rename-is-substable `_ (λ x → refl)
      renaming (⟪id⟫ to rename-id) public

{-
  compose-ext : ∀{ρ₁ ρ₂ : Rename}
              → (ext ρ₁ ⨟ᵣ ext ρ₂) ≡ ext (ρ₁ ⨟ᵣ ρ₂)
  compose-ext {ρ₁}{ρ₂}
      =
      begin
          ext ρ₁ ⨟ᵣ ext ρ₂
      ≡⟨ cong₂ (λ X Y → X ⨟ᵣ Y) (ext-cons-shift ρ₁) (ext-cons-shift ρ₂)  ⟩
          (0 • (ρ₁ ⨟ᵣ ↑ 1)) ⨟ᵣ (0 • (ρ₂ ⨟ᵣ ↑ 1))
      ≡⟨⟩
          0 • ((ρ₁ ⨟ᵣ ↑ 1) ⨟ᵣ (0 • (ρ₂ ⨟ᵣ ↑ 1)))
      ≡⟨ {!!} ⟩
          0 • ((ρ₁ ⨟ᵣ ρ₂) ⨟ᵣ ↑ 1)
      ≡⟨ sym (ext-cons-shift (ρ₁ ⨟ᵣ ρ₂))  ⟩
          ext (ρ₁ ⨟ᵣ ρ₂)
      ∎
{-
      rewrite ext-cons-shift ρ₁
      | ext-cons-shift ρ₂
      | ext-cons-shift (ρ₁ ⨟ᵣ ρ₂)
      | dropr-0 (ρ₂ ⨟ᵣ ↑ 1)
      = {!!}
-}

  open Params (λ σ v → refl) (λ σ v w → refl) (λ σ v → refl) inc-seq {- inc-suc -} {!!}
      renaming (extend-seq to compose-ext;
                sub-sub to compose-rename)
      public
-}
