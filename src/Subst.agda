import AbstractBindingTree
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import GenericSubstitution
open import Var
import Rename

module Subst (Op : Set) (sig : Op → List ℕ) where

  open AbstractBindingTree Op sig using (ABT; `_)
  open Rename Op sig using (rename)
  open SNF public
  
  Subst : Set
  Subst = Substitution ABT

  open GenericSub ABT `_ (rename (↑ 1))
    renaming (⧼_⧽ to ⟦_⟧;
              extend to exts;
              gen-subst-is-env to subst-is-env)
    public
  open GenericSubst ABT `_ (rename (↑ 1)) Op sig (λ M → M)
    renaming (gen-subst to ⟪_⟫;
              gen-subst-is-foldable to subst-is-foldable) public
