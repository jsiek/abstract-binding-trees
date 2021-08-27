open import Agda.Primitive
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
    using (ℕ; zero; suc; _+_; _*_; _⊔_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import GenericSubstitution
open import ListAux
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Structures
open import Syntax
  using (Sig; sig→ℕ; ∁; ν; ■; ↑; _•_; ext; id; Rename; Shiftable; Equiv;
         Relatable)
open import Var
open import Sig using (Result)

module examples.Arith where

data Op : Set where
  op-num : ℕ → Op
  op-mult : Op
  op-let : Op
  op-bool : 𝔹 → Op
  op-if : Op
  op-error : Op

sig : Op → List Sig
sig (op-num n) = []
sig op-mult = ■ ∷ ■ ∷ []
sig op-let = ■ ∷ ν ■ ∷ []
sig (op-bool b) = []
sig op-if = ■ ∷ ■ ∷ ■ ∷ []
sig op-error = []

open import ScopedTuple using (Tuple; _✖_; zip)
open import Fold2 Op sig

open import AbstractBindingTree Op sig renaming (ABT to AST)
pattern $ n  = op-num n ⦅ nil ⦆
pattern # b  = op-bool b ⦅ nil ⦆
infixl 7  _⊗_
pattern _⊗_ L M = op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern bind_｛_｝ L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆
pattern cond_then_else_ L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern error = op-error ⦅ nil ⦆

data Val : Set where
  v-num : ℕ → Val
  v-bool : 𝔹 → Val

instance
  MVal-is-Shiftable : Shiftable (Maybe Val)
  MVal-is-Shiftable = record { var→val = λ x → nothing ; ⇑ = λ r → r
                      ; var→val-suc-shift = refl }
open Shiftable MVal-is-Shiftable public

_>>=_ : ∀{V : Set} → (Maybe V) → (V → Maybe V) → Maybe V
x >>= f
    with x
... | nothing = nothing
... | just n = f n

num? : ∀{V : Set} → Val → (ℕ → Maybe V) → Maybe V
num? mv f
    with mv
... | v-num n = f n
... | _ = nothing

bool? : ∀{V : Set} → Val → (𝔹 → Maybe V) → Maybe V
bool? mv f
    with mv
... | v-bool b = f b
... | _ = nothing


eval-op : (op : Op) → Tuple (sig op) (Result (Maybe Val))
        → Maybe Val
eval-op (op-num n) tt = just (v-num n)
eval-op op-error tt = nothing
eval-op op-mult ⟨ x , ⟨ y , tt ⟩ ⟩ = do
   v₁ ← x ; v₂ ← y 
   num? v₁ (λ n → num? v₂ (λ m → just (v-num (n * m))))
eval-op op-let ⟨ mv , ⟨ f , tt ⟩ ⟩ = f mv
   {- skipping check on mv, simpler -}
eval-op (op-bool b) tt = just (v-bool b)
eval-op op-if ⟨ cnd , ⟨ thn , ⟨ els , tt ⟩ ⟩ ⟩ = do
   vᶜ ← cnd
   bool? vᶜ (λ b → if b then thn else els)

open Structures.WithOpSig Op sig

eval : (Var → Maybe Val) → AST → Maybe Val
eval = fold eval-op nothing

evaluate : AST → Maybe Val
evaluate M = eval (λ x → nothing) M

_ : evaluate ($ 2 ⊗ $ 21) ≡ just (v-num 42)
_ = refl

_ : evaluate (` 0) ≡ nothing
_ = refl

_ : evaluate (bind $ 21 ｛ $ 2 ⊗ ` 0 ｝) ≡ just (v-num 42)
_ = refl

_ : evaluate (bind ` 0 ｛ $ 2 ⊗ $ 21 ｝) ≡ just (v-num 42)
_ = refl {- call-by-name behavior wrt. errors because skipped check -}


