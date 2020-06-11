open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning

module experimental.Arith where

  data Op : Set where
    op-num : ℕ → Op
    op-mult : Op
    op-let : Op
    op-bool : 𝔹 → Op

  sig : Op → List ℕ
  sig (op-num n) = []
  sig op-mult = 0 ∷ 0 ∷ []
  sig op-let = 0 ∷ 1 ∷ []
  sig (op-bool b) = []

  open import experimental.Fold Op sig
  open import experimental.ScopedTuple
  open import experimental.Substitution using (Substable; ↑)

  open import experimental.ABT Op sig
    renaming (ABT to AST)
  pattern $ n  = op-num n ⦅ tt ⦆
  infixl 7  _⊗_
  pattern _⊗_ L M = op-mult ⦅ ⟨ L , ⟨ M , tt ⟩ ⟩ ⦆
  pattern bind_｛_｝ L M = op-let ⦅ ⟨ L , ⟨ M , tt ⟩ ⟩ ⦆

  open import Data.Maybe using (Maybe; nothing; just)

  data Val : Set where
    v-num : ℕ → Val
    v-bool : 𝔹 → Val

  _>>=_ : Maybe Val → (Val → Maybe Val) → Maybe Val
  x >>= f
      with x
  ... | nothing = nothing
  ... | just n = f n

  eval-op : (op : Op) → Tuple (sig op) (Bind (Maybe Val) (Maybe Val))
          → Maybe Val
  eval-op (op-num n) tt = just (v-num n)
  eval-op op-mult ⟨ x , ⟨ y , tt ⟩ ⟩ = do n ← x; m ← y; just (v-num (n * m))
  eval-op op-let ⟨ x , ⟨ f , tt ⟩ ⟩ = do n ← x; f (just n)
  eval-op (op-bool b) tt = just (v-bool b)

  S : Substable (Maybe Val)
  S = record { var→val = λ x → nothing ; shift = λ r → r
             ; var→val-suc-shift = refl }

  E : Fold (Maybe Val) (Maybe Val) 
  E = record { S = S ; ret = λ x → x ; fold-op = eval-op }
  open Fold E

  eval : AST → Maybe Val
  eval = fold (↑ 0)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

  _ : eval ($ 2 ⊗ $ 21) ≡ just 42
  _ = refl
  
  _ : eval (` 0) ≡ nothing
  _ = refl
  
  _ : eval (bind $ 21 ｛ $ 2 ⊗ ` 0 ｝) ≡ just 42
  _ = refl

  _ : eval (bind ` 0 ｛ $ 2 ⊗ $ 21 ｝) ≡ nothing
  _ = refl

