open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
    using (begin_; _≡⟨_⟩_; _∎)
open import SimulateSubst
open import GenericSubstitution

module SubstProperties (Op : Set) (sig : Op → List ℕ) where

  open import AbstractBindingTree Op sig
  open import Rename Op sig using (rename)
  open import Subst Op sig
  open RenameSubst Op sig
              
  subst-is-substable : Substable ABT
  subst-is-substable = record
                          { var→val = `_
                          ; shift = rename (↑ 1)
                          ; ⦑_⦒ = ⟪_⟫
                          ; var→val-suc-shift = λ {x} → refl
                          ; sub-var→val = λ σ x → refl
                          ; shift-⦑↑1⦒ = λ M → rename-subst (↑ 1) M
                          }
  open import GenericSubProperties subst-is-substable
    renaming (inc-suc to incs-suc; extend-suc to exts-suc-rename) public
    
  open import MoreGenSubProperties Op sig subst-is-substable
      (λ M → M) (λ x → refl) public

{-
  {- need commute-subst-rename? -}

  inc-shift : ∀ σ M → ⟪ incs σ ⟫ M ≡ rename (↑ 1) (⟪ σ ⟫ M)
  inc-shift σ M = {!!}

  open Params (λ σ v → refl) {!!} (λ σ v → refl) inc-shift public
-}

{-
  open Substable subst-is-substable

  ⦑σ⦒-tail : (σ : Substitution ABT) (v w : ABT) →
      ⦑ w • σ ⦒ (shift v) ≡ ⦑ σ ⦒ v
  ⦑σ⦒-tail σ v w =
    begin
      ⟪ w • σ ⟫ (rename (↑ 1) v)
    ≡⟨ {!!} ⟩
      ⟪ σ ⟫ v
    ∎
  {-
      rewrite rename-subst (↑ 1) v
      | sub-tail w σ = {!refl!}
  -}

  open Params (λ σ v → refl) {!!} (λ σ v → refl) 
-}
