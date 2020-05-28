open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans)

module IdentitySubst (Op : Set) (sig : Op → List ℕ) where

open import Subst Op sig
open import IdentityRename Op sig
open import SimulateSubst
open RenameSubst Op sig

sub-id : ∀ M → ⟪ id ⟫ M ≡ M
sub-id M = trans (sym (rename-subst id M)) (rename-id M)

