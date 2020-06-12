open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning

module examples.Arith where

  data Op : Set where
    op-num : ℕ → Op
    op-mult : Op
    op-let : Op
    op-bool : 𝔹 → Op
    op-if : Op

  sig : Op → List ℕ
  sig (op-num n) = []
  sig op-mult = 0 ∷ 0 ∷ []
  sig op-let = 0 ∷ 1 ∷ []
  sig (op-bool b) = []
  sig op-if = 0 ∷ 0 ∷ 0 ∷ []

  open import Fold Op sig
  open import ScopedTuple
  open import Syntax using (Substable; ↑)

  open import AbstractBindingTree Op sig
    renaming (ABT to AST)
  pattern $ n  = op-num n ⦅ nil ⦆
  infixl 7  _⊗_
  pattern _⊗_ L M = op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆
  pattern bind_｛_｝ L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆
  pattern cond_then_else_ L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆

  open import Data.Maybe using (Maybe; nothing; just)

  data Val : Set where
    v-num : ℕ → Val
    v-bool : 𝔹 → Val

  _>>=_ : Maybe Val → (Val → Maybe Val) → Maybe Val
  x >>= f
      with x
  ... | nothing = nothing
  ... | just n = f n

  num? : Val → (ℕ → Maybe Val) → Maybe Val
  num? mv f
      with mv
  ... | v-num n = f n
  ... | _ = nothing

  bool? : Val → (𝔹 → Maybe Val) → Maybe Val
  bool? mv f
      with mv
  ... | v-bool b = f b
  ... | _ = nothing

  eval-op : (op : Op) → Tuple (sig op) (Bind (Maybe Val) (Maybe Val))
          → Maybe Val
  eval-op (op-num n) tt = just (v-num n)
  eval-op op-mult ⟨ x , ⟨ y , tt ⟩ ⟩ = do
     v₁ ← x ; v₂ ← y 
     num? v₁ (λ n → num? v₂ (λ m → just (v-num (n * m))))
  eval-op op-let ⟨ x , ⟨ f , tt ⟩ ⟩ = do n ← x; f (just n)
  eval-op (op-bool b) tt = just (v-bool b)
  eval-op op-if ⟨ cnd , ⟨ thn , ⟨ els , tt ⟩ ⟩ ⟩ = do
     vᶜ ← cnd
     bool? vᶜ (λ b → if b then thn else els)

  S : Substable (Maybe Val)
  S = record { var→val = λ x → nothing ; shift = λ r → r
             ; var→val-suc-shift = refl }

  Eval : Fold (Maybe Val) (Maybe Val) 
  Eval = record { S = S ; ret = λ x → x ; fold-op = eval-op }
  open Fold Eval

  eval : AST → Maybe Val
  eval = fold (↑ 0)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

  _ : eval ($ 2 ⊗ $ 21) ≡ just (v-num 42)
  _ = refl
  
  _ : eval (` 0) ≡ nothing
  _ = refl
  
  _ : eval (bind $ 21 ｛ $ 2 ⊗ ` 0 ｝) ≡ just (v-num 42)
  _ = refl

  _ : eval (bind ` 0 ｛ $ 2 ⊗ $ 21 ｝) ≡ nothing
  _ = refl


  {--- Type Safety via preserve-fold ---}

  data Type : Set where
    t-nat : Type
    t-bool : Type

{-
  open import experimental.Preserve Op sig
  open PreserveFold Eval 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_
-}
