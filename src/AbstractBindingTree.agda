open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import ScopedTuple
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var

module AbstractBindingTree (Op : Set) (sig : Op → List ℕ)  where

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

var-injective : ∀ {x y} → ` x ≡ ` y → x ≡ y
var-injective refl = refl

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

{- Helper functions -}

map₊ : ∀{bs} → (∀ {b} → Arg b → Arg b) → Args bs → Args bs
map₊ {[]} f nil = nil
map₊ {b ∷ bs} f (cons arg args) = cons (f arg) (map₊ f args)

{- Convert to tuples -}

⌊_⌋ : ∀{bs} → Args bs → Tuple bs (λ _ → ABT)
⌊_⌋ₐ : ∀{b} → Arg b → ABT

⌊_⌋ₐ {zero} (ast M) = M
⌊_⌋ₐ {suc b} (bind arg) = ⌊ arg ⌋ₐ

⌊_⌋ {[]} args = tt
⌊_⌋ {b ∷ bs} (cons arg args) = ⟨ ⌊ arg ⌋ₐ , ⌊ args ⌋ ⟩


{----------------------------------------------------------------------------
  Contexts and Plug
  (for expressing contextual equivalence, not for evaluation contexts)
 ---------------------------------------------------------------------------}

data CArgs : (sig : List ℕ) → Set

data Ctx : Set where
  CHole : Ctx
  COp : (op : Op) → CArgs (sig op) → Ctx

data CArg : (b : ℕ) → Set where
  CAst : Ctx → CArg 0
  CBind : ∀{b} → CArg b → CArg (suc b)

data CArgs where
  tcons : ∀{b}{bs bs'} → Arg b → CArgs bs → bs' ≡ (b ∷ bs)
        → CArgs bs'
  ccons : ∀{b}{bs bs'} → CArg b → Args bs → bs' ≡ (b ∷ bs)
        → CArgs bs'  

plug : Ctx → ABT → ABT
plug-arg : ∀ {b} → CArg b → ABT → Arg b
plug-args : ∀ {bs} → CArgs bs → ABT → Args bs

plug CHole M = M
plug (COp op args) M = op ⦅ plug-args args M ⦆

plug-arg (CAst C) M = ast (plug C M)
plug-arg (CBind C) M = bind (plug-arg C M)

plug-args (tcons L Cs eq) M rewrite eq =
   cons L (plug-args Cs M)
plug-args (ccons C Ls eq) M rewrite eq =
   cons (plug-arg C M) Ls

cargs-not-empty : ¬ CArgs []
cargs-not-empty (tcons (ast _) _ ())
cargs-not-empty (tcons (bind _) _ ())
cargs-not-empty (ccons (CAst _) _ ())
cargs-not-empty (ccons (CBind _) _ ())

ctx-depth : Ctx → ℕ
ctx-depth-arg : ∀{n} → CArg n → ℕ
ctx-depth-args : ∀{bs} → CArgs bs → ℕ

ctx-depth CHole = 0
ctx-depth (COp op args) = ctx-depth-args args
ctx-depth-arg (CAst C) = ctx-depth C
ctx-depth-arg (CBind arg) = suc (ctx-depth-arg arg) 
ctx-depth-args (tcons arg cargs _) = ctx-depth-args cargs
ctx-depth-args (ccons carg args _) = ctx-depth-arg carg

