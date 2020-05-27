open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)

module AbstractBindingTree (Op : Set) (sig : Op → List ℕ)  where

open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Var

data Args : List ℕ → Set

data ABT : Set where
  `_ : Var → ABT
  _⦅_⦆ : (op : Op) → Args (sig op) → ABT

data Arg : ℕ → Set where
  ast : ABT → Arg 0
  bind : ∀{n} → Arg n → Arg (suc n)

data Args where
  nil : Args []
  cons : ∀{n bs} → Arg n → Args bs → Args (n ∷ bs)

bind-arg : ∀{m} → (n : ℕ) → Arg m → Arg (n + m)
bind-arg  zero A = A
bind-arg {m} (suc n) A
    with bind-arg {suc m} n (bind A)
... | ih rewrite +-suc n m = ih

bind-ast : ∀(n : ℕ) → ABT → Arg n
bind-ast n M
    with bind-arg n (ast M)
... | A rewrite +-identityʳ n = A

max-var : ABT → ℕ
max-var-arg : ∀{b} → Arg b → ℕ
max-var-args : ∀{bs} → Args bs → ℕ

max-var (` x) = x
max-var (op ⦅ args ⦆) = max-var-args args

max-var-arg (ast M) = max-var M
max-var-arg (bind arg) = (max-var-arg arg) ∸ 1

max-var-args nil = 0
max-var-args (cons arg args) = (max-var-arg arg) ⊔ (max-var-args args)
