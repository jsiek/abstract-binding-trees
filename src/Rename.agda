import AbstractBindingTree
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Substitution
open import Var

module Rename (Op : Set) (sig : Op → List ℕ) where

  open AbstractBindingTree Op sig using (`_)
  open SNF public

  Rename : Set
  Rename = Substitution Var

  open GenericSubst Var (λ x → x) suc Op sig `_
      renaming (gen-subst to rename;
                gen-subst-is-foldable to rename-is-foldable) public
                
  rename-is-substable : Substable Var
  rename-is-substable = record
                          { var→val = λ x → x
                          ; shift = suc
                          ; ⟪_⟫ = ⦉_⦊
                          ; var→val-suc-shift = λ {x} → refl
                          ; sub-var→val = λ σ x → refl
                          ; shift-⟪↑1⟫ = λ v → refl
                          }
  open GenericSubProperties rename-is-substable
    renaming ( extend-suc to ext-suc) public


