open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
  renaming (subst to eq-subst)

module IdentityRename (Op : Set) (sig : Op → List ℕ) where

  open import Simulate
  open import SimulateSubst
  open import IdentityFold Op sig
  open import Rename Op sig
  open import Subst Op sig
  open import AbstractBindingTree Op sig
  open import Fold
  open import Var

  _∼_ : Var → ABT → Set
  _∼_ = λ x M → ` x ≡ M 

  open RelGenericSubst Var ABT _∼_

  open RelateSub Var ABT _∼_ (λ x → x) suc `_ (rename (↑ 1)) (λ {x} → refl)
    (λ { refl → refl })
    using (sub-is-rel-env)

  open Foldable rename-is-foldable
  

  op∼ : ∀{op}{Rs₁}{Rs₂} → ArgsRes∼ Rs₁ Rs₂ → fop₁ op Rs₁ ≈ fop₂ op Rs₂
  op∼ {op}{Rs₁}{Rs₂} Rs∼ = ?
  
  rel-rename-id : Related rename-is-foldable id-is-foldable
  rel-rename-id = record
                   { _∼_ = _∼_ ;
                     _≈_ = λ M₁ M₂ → M₁ ≡ M₂ ;
                     env∼ = sub-is-rel-env ;
                     ret≈ = λ {v₁} {v₂} z → z ;
                     vars∼ = λ {x} → refl ;
                     op∼ = {!!} }
  
  
