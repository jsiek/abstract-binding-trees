open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Syntax
open import Fold
open import Var

module examples.Arith where

  {---------------------------------------
   Function representation of environments
   ---------------------------------------}
 
  module FunEnv (V : Set) where

    extend : (Var → V) → V → (Var → V)
    extend ρ v zero = v
    extend ρ v (suc x) = ρ x

    fun-is-env : EnvSig (Var → V) V
    fun-is-env = record { lookup = λ ρ x → ρ x ; extend = extend }

  data Op : Set where
    op-num : ℕ → Op
    op-mult : Op
    op-let : Op

  sig : Op → List ℕ
  sig (op-num n) = []
  sig op-mult = 0 ∷ 0 ∷ []
  sig op-let = 0 ∷ 1 ∷ []

  open OpSig Op sig
  pattern $ n  = op-num n ⦅ nil ⦆
  infixl 7  _×_
  pattern _×_ L M = op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆
  pattern bind_｛_｝ L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆

  open import Data.Maybe using (Maybe; nothing; just)
  open ArgResult (Maybe ℕ) (Maybe ℕ)

  _>>=_ : Maybe ℕ → (ℕ → Maybe ℕ) → Maybe ℕ
  x >>= f
      with x
  ... | nothing = nothing
  ... | just n = f n

  eval-op : (o : Op) → ArgsRes (sig o) → Maybe ℕ
  eval-op (op-num n) res = just n
  eval-op op-mult (rcons x (rcons y rnil)) = do n ← x; m ← y; just (n * m)
  eval-op op-let (rcons x (rcons f rnil)) = do n ← x; f (just n)

  open FunEnv (Maybe ℕ)
  
  E : Foldable (Maybe ℕ) (Maybe ℕ) Op sig (Var → (Maybe ℕ))
  E = record { ret = λ x → x ; fold-free-var = λ x → nothing ;
               fold-op = eval-op ; env = fun-is-env }

  open Folder E

  eval : ABT → Maybe ℕ
  eval = fold (λ x → nothing)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

  _ : eval ($ 2 × $ 21) ≡ just 42
  _ = refl
  
  _ : eval (` 0) ≡ nothing
  _ = refl
  
  _ : eval (bind $ 21 ｛ $ 2 × ` 0 ｝) ≡ just 42
  _ = refl

  _ : eval (bind ` 0 ｛ $ 2 × $ 21 ｝) ≡ nothing
  _ = refl


