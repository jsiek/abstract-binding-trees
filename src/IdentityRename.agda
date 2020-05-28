open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to eq-subst)

module IdentityRename (Op : Set) (sig : Op → List ℕ) where

module A where
  {-
     Direct proof of rename-id. 
   -}
  open import AbstractBindingTree Op sig
  open import Rename Op sig
  open import Fold
  open Folder rename-is-foldable
  
  ren-id : ∀ ρ M
     → (∀ x → ⦉ ρ ⦊ x ≡ x)
     → rename ρ M ≡ M
  ren-id-arg : ∀ b ρ (arg : Arg b)
     → (∀ x → ⦉ ρ ⦊ x ≡ x)
     → ren-arg (fold-arg ρ arg) ≡ arg
  ren-id-args : ∀ bs ρ (args : Args bs)
     → (∀ x → ⦉ ρ ⦊ x ≡ x)
     → ren-args (fold-args ρ args) ≡ args
     
  ren-id-arg zero ρ (ast M) ρ-id = cong ast (ren-id ρ M ρ-id)
  ren-id-arg (suc b) ρ (bind arg) ρ-id =
      cong bind (ren-id-arg b (ext ρ 0) arg G)
      where
      G : (x : ℕ) → ⦉ ext ρ 0 ⦊ x ≡ x
      G zero = refl
      G (suc x) rewrite ext-suc ρ 0 x = cong suc (ρ-id x)
  ren-id-args [] ρ nil ρ-id = refl
  ren-id-args (b ∷ bs) ρ (cons arg args) ρ-id =
      cong₂ cons (ren-id-arg b ρ arg ρ-id) (ren-id-args bs ρ args ρ-id)
  ren-id ρ (` x) ρ-id = cong `_ (ρ-id x)
  ren-id ρ (op ⦅ args ⦆) ρ-id = cong (_⦅_⦆ op) (ren-id-args (sig op) ρ args ρ-id)

open A public

module B where
  {- 
      Proof of rename-id using simulation with identity fold.
      It's too long :(
   -}
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

  {-
   TODO: 
   * find a way to automate this arg∼/args∼ stuff
   -}

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

