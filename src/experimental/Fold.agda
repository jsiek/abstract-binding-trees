{-

  Experiments in generic functions and theorems over abstract binding trees.

  Drawing inspiration from the paper "A Type and Scope Safe Universe of
  Syntaxes with Binding", ICFP 2018.

-}

module Fold where

open import Var
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

{------------------------------------------

   Generic fold over abstract binding trees

 -------------------------------------------}
 
record EnvSig (E : Set) (V : Set) : Set where
  field lookup : E → Var → V
  field extend : E → V → E

module ArgResult (V : Set) (C : Set) where

  ArgRes : ℕ → Set
  ArgRes 0 = C
  ArgRes (suc n) = V → ArgRes n

  data ArgsRes : List ℕ → Set where
    rnil : ArgsRes []
    rcons : ∀{b bs} → ArgRes b → ArgsRes bs → ArgsRes (b ∷ bs)

record Foldable V C (Op : Set) (sig : Op → List ℕ) (Env : Set) : Set where
  open ArgResult V C
  field env : EnvSig Env V
  open EnvSig env public
  field ret : V → C
  field fold-free-var : Var → V
  field fold-op : (o : Op) → ArgsRes (sig o) → C

module Folder {V}{C}{Op}{sig}{Env} (F : Foldable V C Op sig Env) where

  open import AbstractBindingTree Op sig
  open Foldable F
  open ArgResult V C

  fold : Env → ABT → C
  fold-arg : ∀{b} → Env → Arg b → ArgRes b
  fold-args : ∀{bs} → Env → Args bs → ArgsRes bs

  fold σ (` x) = ret (lookup σ x)
  fold σ (o ⦅ args ⦆) = fold-op o (fold-args σ args)

  fold-arg σ (ast M) = fold σ M
  fold-arg σ (bind M) = λ v → fold-arg (extend σ v) M

  fold-args σ nil = rnil
  fold-args σ (cons arg args) = rcons (fold-arg σ arg) (fold-args σ args)

{-
module ComposeEnv {V₁ V₂}{Env₁ Env₂}
  (ES₁ : EnvSig Env₁ V₁)
  (ES₂ : EnvSig Env₂ V₂)
  (⦑_⦒ : Env₂ → V₁ → V₂)
  where

  Env : Set
  Env = Var → V₂

  _∘_ : (E₂ : Env₂) → (E₁ : Env₁) → Env
  (σ₂ ∘ σ₁) x = ⦑ σ₂ ⦒ (EnvSig.lookup ES₁ σ₁ x)

  compose-is-env : EnvSig Env V₂
  compose-is-env = record { lookup = λ σ x → σ x ; extend = {!!} }


module Fusion {V₁ V₂}{C₁ C₂}{Op}{sig}{Env₁ Env₂}
  (F₁ : Foldable V₁ C₁ Op sig Env₁)
  (F₂ : Foldable V₂ C₂ Op sig Env₂)
  where

  open Folder F₁ renaming (fold to fold₁)
  open Folder F₂ renaming (fold to fold₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

  open ComposeEnv (Foldable.env F₁) (Foldable.env F₂) {!!}

{-
  compose-is-foldable : Foldable V₂ C₂ Op sig Env
  compose-is-foldable = ?
-}

{-
 fusion : ∀ σ₁ σ₂ M
    → fold₂ σ₂ (fold₁ σ₁ M) ≡ fold (σ₂ ∘ σ₁) M
 fusion σ₁ σ₂ M = ?
-}
-}
