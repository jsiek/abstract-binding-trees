{-# OPTIONS --without-K  #-}
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_) renaming (map to lmap)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _≟_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import ScopedTuple
open import Sig
open import Structures
open import Var

module AbstractBindingTree (Op : Set) (sig : Op → List Sig) where

data Args : List Sig → Set

data ABT : Set where
  `_ : Var → ABT
  _⦅_⦆ : (op : Op) → Args (sig op) → ABT

data Arg : Sig → Set where
  ast : ABT → Arg ■
  bind : ∀{b} → Arg b → Arg (ν b)
  clear : ∀{b} → Arg b → Arg (∁ b)

data Args where
  nil : Args []
  cons : ∀{b bs} → Arg b → Args bs → Args (b ∷ bs)

var-injective : ∀ {x y} → ` x ≡ ` y → x ≡ y
var-injective refl = refl

{-
bind-arg : ∀{m} → (n : ℕ) → Arg m → Arg (n + m)
bind-arg  zero A = A
bind-arg {m} (suc n) A
    with bind-arg {suc m} n (bind A)
... | ih rewrite +-suc n m = ih

bind-ast : ∀(n : ℕ) → ABT → Arg n
bind-ast n M
    with bind-arg n (ast M)
... | A rewrite +-identityʳ n = A
-}

{- Return suc x where x is the largest free variable in a term. -}
max-var : ABT → ℕ
max-var-arg : ∀{b} → Arg b → ℕ
max-var-args : ∀{bs} → Args bs → ℕ

max-var (` x) = suc x
max-var (op ⦅ args ⦆) = max-var-args args

max-var-arg (ast M) = max-var M
max-var-arg (bind arg) = (max-var-arg arg) ∸ 1
max-var-arg (clear arg) = 0

max-var-args nil = 0
max-var-args (cons arg args) = (max-var-arg arg) ⊔ (max-var-args args)

{- Helper functions -}

map₊ : ∀{bs} → (∀ {b} → Arg b → Arg b) → Args bs → Args bs
map₊ {[]} f nil = nil
map₊ {b ∷ bs} f (cons arg args) = cons (f arg) (map₊ f args)

{- Convert to tuples -}

⌊_⌋ : ∀{bs} → Args bs → Tuple bs (λ _ → ABT)
⌊_⌋ₐ : ∀{b} → Arg b → ABT

⌊_⌋ₐ {■} (ast M) = M
⌊_⌋ₐ {ν b} (bind arg) = ⌊ arg ⌋ₐ
⌊_⌋ₐ {∁ b} (clear arg) = ⌊ arg ⌋ₐ

⌊_⌋ {[]} args = tt
⌊_⌋ {b ∷ bs} (cons arg args) = ⟨ ⌊ arg ⌋ₐ , ⌊ args ⌋ ⟩


{----------------------------------------------------------------------------
  Contexts and Plug
  (for expressing contextual equivalence, not for evaluation contexts)
 ---------------------------------------------------------------------------}

data CArgs : (sig : List Sig) → Set

data Ctx : Set where
  CHole : Ctx
  COp : (op : Op) → CArgs (sig op) → Ctx

data CArg : (b : Sig) → Set where
  CAst : Ctx → CArg ■
  CBind : ∀{b} → CArg b → CArg (ν b)
  CClear : ∀{b} → CArg b → CArg (∁ b)

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
plug-arg (CClear C) M = clear (plug-arg C M)

plug-args (tcons L Cs eq) M rewrite eq =
   cons L (plug-args Cs M)
plug-args (ccons C Ls eq) M rewrite eq =
   cons (plug-arg C M) Ls

cargs-not-empty : ¬ CArgs []
cargs-not-empty (tcons (ast _) _ ())
cargs-not-empty (tcons (bind _) _ ())
cargs-not-empty (ccons (CAst _) _ ())
cargs-not-empty (ccons (CBind _) _ ())

ctx-depth : Ctx → ℕ → ℕ
ctx-depth-arg : ∀{n} → CArg n → ℕ → ℕ 
ctx-depth-args : ∀{bs} → CArgs bs → ℕ → ℕ

ctx-depth CHole k = k
ctx-depth (COp op args) k = ctx-depth-args args k
ctx-depth-arg (CAst C) k = ctx-depth C k
ctx-depth-arg (CBind arg) k = ctx-depth-arg arg (suc k)
ctx-depth-arg (CClear arg) k = ctx-depth-arg arg 0
ctx-depth-args (tcons arg cargs _) k = ctx-depth-args cargs k
ctx-depth-args (ccons carg args _) k = ctx-depth-arg carg k

record Quotable {ℓ} (V : Set ℓ) : Set ℓ where
  field “_” : V → ABT

open Quotable {{...}} public

instance
  Var-is-Quotable : Quotable Var
  Var-is-Quotable = record { “_” = `_ }

  ABT-is-Quotable : Quotable ABT
  ABT-is-Quotable = record { “_” = λ x → x }

{----------------------------------------------------------------------------
 Free variables
----------------------------------------------------------------------------}

FV? : ABT → Var → Bool
FV-arg? : ∀{b} → Arg b → Var → Bool
FV-args? : ∀{bs} → Args bs → Var → Bool
FV? (` x) y
    with x ≟ y
... | yes xy = true
... | no xy = false
FV? (op ⦅ args ⦆) y = FV-args? args y
FV-arg? (ast M) y = FV? M y
FV-arg? (bind arg) y = FV-arg? arg (suc y)
FV-arg? (clear arg) y = false
FV-args? nil y = false
FV-args? (cons arg args) y = FV-arg? arg y ∨ FV-args? args y

{- Predicate Version -}

FV : ABT → Var → Set
FV-arg : ∀{b} → Arg b → Var → Set
FV-args : ∀{bs} → Args bs → Var → Set
FV (` x) y = x ≡ y
FV (op ⦅ args ⦆) y = FV-args args y
FV-arg (ast M) y = FV M y
FV-arg (bind arg) y = FV-arg arg (suc y)
FV-arg (clear arg) y = ⊥
FV-args nil y = ⊥
FV-args (cons arg args) y = FV-arg arg y ⊎ FV-args args y
