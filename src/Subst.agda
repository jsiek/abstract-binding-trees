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
              gen-inc to incs;
              gen-subst-is-env to subst-is-env)
    public

  exts : Subst → Subst
  exts σ = extend σ (` 0)

  open GenericSubst ABT `_ (rename (↑ 1)) Op sig (λ M → M)
    using (⟪_⟫; ⟪_⟫ₐ; ⟪_⟫₊)
    renaming (gen-subst-is-foldable to subst-is-foldable;
              s-arg to sub-res→arg; s-args to sub-res→args)
    public

