import AbstractBindingTree
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import GenericSubstitution
open import Var

module Rename (Op : Set) (sig : Op → List ℕ) where

  open AbstractBindingTree Op sig using (`_)
  open SNF using (Substitution) public

  Rename : Set
  Rename = Substitution Var

  open GenericSub Var (λ x → x) suc
    using ()
    renaming (⧼_⧽ to ⦉_⦊; extend to ext; drop to dropr; gen-inc to inc;
              gen-subst-is-env to rename-is-env) public

  open GenericSubst Var (λ x → x) suc Op sig `_
      using ()
      renaming (gen-subst to rename;
                gen-subst-is-foldable to rename-is-foldable;
                s-arg to ren-arg; s-args to ren-args) public
                
  rename-is-substable : Substable Var
  rename-is-substable = record
                          { var→val = λ x → x
                          ; shift = suc
                          ; ⟪_⟫ = ⦉_⦊
                          ; var→val-suc-shift = λ {x} → refl
                          ; sub-var→val = λ σ x → refl
                          ; shift-⟪↑1⟫ = λ v → refl
                          }
  open import GenericSubProperties rename-is-substable
    renaming (extend-suc to ext-suc) public


