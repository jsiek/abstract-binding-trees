open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
  renaming (subst to eq-subst)

module IdentitySubst (Op : Set) (sig : Op → List ℕ) where

  open import Simulate
  open import IdentityFold Op sig
  open import Subst Op sig

  rel-subst-id : Related subst-is-foldable id-is-foldable
  rel-subst-id = record
                   { _∼_ = λ M₁ M₂ → M₁ ≡ M₂ ;
                   _≈_ = λ M₁ M₂ → M₁ ≡ M₂ ;
                   env∼ = {!!} ;
                   ret≈ = λ {v₁} {v₂} z → z ;
                   vars∼ = λ {x} → refl ;
                   op∼ = {!!} }
  
  
