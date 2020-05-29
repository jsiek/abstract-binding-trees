import AbstractBindingTree
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import GenericSubstitution
open import Var

module Rename (Op : Set) (sig : Op → List ℕ) where

  open AbstractBindingTree Op sig
      using (`_; _⦅_⦆; Arg; Args; ast; bind; nil; cons)
  open SNF using (Substitution) public

  Rename : Set
  Rename = Substitution Var

  open GenericSub Var (λ x → x) suc
    using ()
    renaming (⧼_⧽ to ⦉_⦊; extend to ext; drop to dropr; gen-inc to inc;
              drop-0 to dropr-0; drop-add to dropr-add;
              gen-subst-is-env to rename-is-env) public

  open GenericSubst Var (λ x → x) suc Op sig `_ 
      using ()
      renaming (gen-subst to rename;
                gen-subst-is-foldable to rename-is-foldable;
                s-arg to ren-arg; s-args to ren-args) public
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
    renaming (extend-suc to ext-suc; _⨟_ to _⨟ᵣ_; sub-tail to ren-tail;
              inc=⨟↑ to inc=⨟ᵣ↑; extend-cons-shift to ext-cons-shift;
              sub-η to ren-η; sub-idL to ren-idL; sub-dist to ren-dist;
              seq-subst to seq-rename;
              extend-id to ext-id) public

  open import MoreGenSubProperties Op sig rename-is-substable `_ (λ x → refl)
      renaming (⟪id⟫ to rename-id) public

  open Params (λ σ v → refl) (λ σ v w → refl) (λ σ v → refl) inc-suc
      renaming (extend-seq to compose-ext;
                sub-sub to compose-rename)
      public
