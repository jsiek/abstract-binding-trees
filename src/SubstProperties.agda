open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SimulateSubst
open import Substitution

module SubstProperties (Op : Set) (sig : Op → List ℕ) where

  open import AbstractBindingTree Op sig
  open import Rename Op sig using (rename)
  open import Subst Op sig
  open RenameSubst Op sig
              
  subst-is-substable : Substable ABT
  subst-is-substable = record
                          { var→val = `_
                          ; shift = rename (↑ 1)
                          ; ⟪_⟫ = ⟪_⟫
                          ; var→val-suc-shift = λ {x} → refl
                          ; sub-var→val = λ σ x → refl
                          ; shift-⟪↑1⟫ = λ M → rename-subst (↑ 1) M
                          }
  open GenericSubProperties subst-is-substable
    renaming (inc-suc to incs-suc; extend-suc to exts-suc-rename) public


