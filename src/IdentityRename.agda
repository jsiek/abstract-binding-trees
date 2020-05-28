open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
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

  open Foldable rename-is-foldable renaming (fold-op to ren-op)
  open Foldable id-is-foldable renaming (fold-op to id-op)
  open SimArgResult {Op}{sig}{Var}{ABT}{ABT}{ABT} _∼_ _≡_

  arg∼ : ∀{b}{R₁ : ArgRes₁ b}{R₂ : ArgRes₂ b}
     → ArgRes∼ R₁ R₂
     → ren-arg R₁ ≡ res→arg R₂
  arg∼ {zero} {R₁} {.R₁} refl = refl
  arg∼ {suc b} {R₁} {R₂} r∼ = cong bind (arg∼ (r∼ refl))

  args∼ : ∀{bs}{Rs₁ : ArgsRes₁ bs}{Rs₂ : ArgsRes₂ bs}
     → ArgsRes∼ Rs₁ Rs₂
     → ren-args Rs₁ ≡ res→args Rs₂
  args∼ {[]} {ArgResult.rnil} {ArgResult.rnil} rnil∼ = refl
  args∼ {b ∷ bs} {ArgResult.rcons r1 Rs₁} {ArgResult.rcons r2 Rs₂}
      (rcons∼ r∼ rs∼) = cong₂ cons (arg∼ r∼) (args∼ rs∼)
  
  op∼ : ∀{op}{Rs₁ : ArgsRes₁ (sig op)}{Rs₂ : ArgsRes₂ (sig op)}
      → ArgsRes∼ Rs₁ Rs₂
      → ren-op op Rs₁ ≡ id-op op Rs₂
  op∼ {op}{Rs₁}{Rs₂} Rs∼ = cong (_⦅_⦆ op) (args∼ Rs∼)
  
  rel-rename-id : Related rename-is-foldable id-is-foldable
  rel-rename-id = record
                   { _∼_ = _∼_ ;
                     _≈_ = λ M₁ M₂ → M₁ ≡ M₂ ;
                     env∼ = sub-is-rel-env ;
                     ret≈ = λ {v₁} {v₂} z → z ;
                     vars∼ = λ {x} → refl ;
                     op∼ = op∼ }
  
  open Simulator rename-is-foldable id-is-foldable rel-rename-id

  rename-id-fold : ∀ M
     → rename id M ≡ id-fold id M
  rename-id-fold M = sim {M = M} r-up

  rename-id : ∀ M
     → rename id M ≡ M
  rename-id M = trans (rename-id-fold M) (id-is-id M)
