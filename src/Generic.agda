{-

  Experiments in generic functions and theorems over abstract binding trees.

  Trying to draw inspiration from "A Type and Scope Safe Universe of Syntaxes with Biding", ICFP 2018.

-}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)

open import Syntax

module Generic where


module Sub 
  (Op : Set)
  (sig : Op → List ℕ)
  (V : Set)
  (var-fun : Var → V)
  (apply : Substitution V → V → V)
  where

  ⧼_⧽ : Substitution V → Var → V
  ⧼ ↑ k ⧽ x = var-fun (k + x)
  ⧼ y • σ ⧽ 0 = y
  ⧼ y • σ ⧽ (suc x) = ⧼ σ ⧽ x

  private
    drop : (k : ℕ) → Substitution V → Substitution V
    drop k (↑ k') = ↑ (k + k')
    drop zero (x • σ) = x • σ
    drop (suc k) (x • σ) = drop k σ

  abstract
    infixr 5 _⨟_

    _⨟_ : Substitution V → Substitution V → Substitution V
    ↑ k ⨟ σ = drop k σ
    (v • σ₁) ⨟ σ₂ = (apply σ₂ v) • (σ₁ ⨟ σ₂)

module FoldMonad (V : Set) (C : Set) (ret : V → C) where

  ArgRes : ℕ → Set
  ArgRes 0 = C
  ArgRes (suc n) = V → ArgRes n

  data ArgsRes : List ℕ → Set where
    rnil : ArgsRes []
    rcons : ∀{b bs} → ArgRes b → ArgsRes bs → ArgsRes (b ∷ bs)

  module Fold
    (Op : Set)
    (sig : Op → List ℕ)
    (var-fun : Var → V)
    (op-fun : (o : Op) → ArgsRes (sig o) → C)
    (apply : Substitution V → V → V)
    where

    open OpSig Op sig hiding (_⨟_)
    open Sub Op sig V var-fun apply

    fold : Substitution V → ABT → C
    fold-arg : ∀{b} → Substitution V → Arg b → ArgRes b
    fold-args : ∀{bs} → Substitution V → Args bs → ArgsRes bs

    fold σ (` x) = ret (⧼ σ ⧽ x)
    fold σ (o ⦅ args ⦆) = op-fun o (fold-args σ args)

    fold-arg σ (ast M) = fold σ M
    fold-arg σ (bind M) = λ v → fold-arg (v • (σ ⨟ ↑ 1)) M

    fold-args σ nil = rnil
    fold-args σ (cons arg args) = rcons (fold-arg σ arg) (fold-args σ args)


module Rename 
  (Op : Set)
  (sig : Op → List ℕ)
  where

  open OpSig Op sig hiding (rename)
  module Ren = FoldMonad Var ABT (λ x → ` x)
  open Ren

  ren : (o : Op) → Ren.ArgsRes (sig o) → ABT
  ren o rs = o ⦅ r-args rs ⦆
      where
      r-arg : ∀{b} → ArgRes b → Arg b
      r-arg {zero} argr = ast argr
      r-arg {suc b} argr = bind (r-arg (argr 0))
      
      r-args : ∀{bs} → Ren.ArgsRes bs → Args bs
      r-args rnil = nil
      r-args (rcons argr argsr) = cons (r-arg argr) (r-args argsr)
  
  module RenFold = Ren.Fold Op sig (λ x → x) ren (λ ρ x → ⦉ ρ ⦊ x)

  rename : Rename → ABT → ABT
  rename = RenFold.fold

module LambdaExample where

  data Op : Set where
    op-lam : Op
    op-app : Op

  sig : Op → List ℕ
  sig op-lam = 1 ∷ []
  sig op-app = 0 ∷ 0 ∷ []

  open OpSig Op sig hiding (rename)

  pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

  infixl 7  _·_
  pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
  
  open Rename Op sig

  M₀ : ABT
  M₀ = (` 0) · (` 1)

  M₁ : ABT
  M₁ = ƛ (` 0) · (` 1)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

  _ : rename (↑ 1) M₀ ≡ (` 1) · (` 2)
  _ = refl

  _ : rename (↑ 1) M₁ ≡ ƛ (` 0) · (` 2)
  _ = refl

