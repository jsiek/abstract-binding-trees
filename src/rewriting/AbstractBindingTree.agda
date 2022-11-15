{-# OPTIONS --without-K --rewriting #-}
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate) renaming (map to lmap)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _≟_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import ScopedTuple
open import Sig
open import Var
open import Structures using (extensionality)

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module rewriting.AbstractBindingTree (Op : Set) (sig : Op → List Sig) where

data Args : List Sig → Set

data ABT : Set where
  `_ : Var → ABT
  _⦅_⦆ : (op : Op) → Args (sig op) → ABT

data Arg : Sig → Set where
  ast : ABT → Arg ■
  bind : ∀{b} → Arg b → Arg (ν b)

data Args where
  nil : Args []
  cons : ∀{b bs} → Arg b → Args bs → Args (b ∷ bs)

{----------------------------------------------------------------------------
 Renaming
----------------------------------------------------------------------------}

Rename : Set
Rename = Var → Var

infixr 6 _•ᵣ_
_•ᵣ_ : Var → Rename → Rename
(y •ᵣ ρ) 0 = y
(y •ᵣ ρ) (suc x) = ρ x

⟰ᵣ : Rename → Rename
⟰ᵣ ρ x = suc (ρ x)

extr : Rename → Rename
extr ρ = 0 •ᵣ ⟰ᵣ ρ

rename : Rename → ABT → ABT
rename-arg : Rename → {b : Sig} → Arg b → Arg b
rename-args : Rename → {bs : List Sig} → Args bs → Args bs

rename ρ (` x) = ` ρ x
rename ρ (op ⦅ args ⦆) = op ⦅ rename-args ρ args ⦆
rename-arg ρ (ast M) = ast (rename ρ M)
rename-arg ρ (bind M) = bind (rename-arg (extr ρ) M)
rename-args ρ nil = nil
rename-args ρ (cons arg args) = cons (rename-arg ρ arg) (rename-args ρ args)

{----------------------------------------------------------------------------
 Substitution
----------------------------------------------------------------------------}

Subst : Set
Subst = Var → ABT

infixr 6 _•_
_•_ : ABT → Subst → Subst
(M • σ) 0 = M
(M • σ) (suc x) = σ x

⟰ : Subst → Subst
⟰ σ x = rename suc (σ x)

ext : Subst → Subst
ext σ = ` 0 • ⟰ σ

sub : Subst → ABT → ABT
sub-arg : Subst → {b : Sig} → Arg b → Arg b
sub-args : Subst → {bs : List Sig} → Args bs → Args bs

sub σ (` x) = σ x
sub σ (op ⦅ args ⦆) = op ⦅ sub-args σ args ⦆
sub-arg σ (ast M) = ast (sub σ M)
sub-arg σ (bind M) = bind (sub-arg (ext σ) M)
sub-args σ nil = nil
sub-args σ (cons arg args) = cons (sub-arg σ arg) (sub-args σ args)

ren : Rename → Subst
ren ρ x = ` ρ x

abstract 
  infixr 5 _⨟_
  _⨟_ : Subst → Subst → Subst
  (σ ⨟ τ) x = sub τ (σ x)

abstract
  seq-def : ∀ σ τ x → (σ ⨟ τ) x ≡ sub τ (σ x)
  seq-def σ τ x = refl
{-# REWRITE seq-def #-}
  
{-
ren-con : ∀ {y ρ} → ren (y •ᵣ ρ) ≡ ((` y) • ren ρ)
ren-con {y}{ρ} = extensionality aux   
    where
    aux : ∀ {y ρ} → ∀ x → ren (y •ᵣ ρ) x ≡ ((` y) • ren ρ) x
    aux {y} {ρ} zero = refl
    aux {y} {ρ} (suc x) = refl

ren-shift : ∀{ρ} → ren (⟰ᵣ ρ) ≡ ⟰ (ren ρ)
ren-shift {ρ} = extensionality aux
    where
    aux : ∀{ρ} → ∀ x → ren (⟰ᵣ ρ) x ≡ ⟰ (ren ρ) x
    aux {ρ} zero = refl
    aux {ρ} (suc x) = refl

-}

cons-seq : ∀ σ τ M → (M • σ) ⨟ τ ≡ sub τ M • (σ ⨟ τ)
cons-seq σ τ M = extensionality aux
    where
    aux : ∀{σ τ M} → ∀ x → ((M • σ) ⨟ τ) x ≡ (sub τ M • (σ ⨟ τ)) x
    aux {σ} {τ} {M} zero = refl
    aux {σ} {τ} {M} (suc x) = refl
{-# REWRITE cons-seq #-}

ext-ren : ∀{ρ} → (` 0) • ⟰ (ren ρ) ≡ ren (extr ρ)
ext-ren {ρ} = extensionality aux
    where
    aux : ∀{ρ} → ∀ x → ext (ren ρ) x ≡ ren (extr ρ) x
    aux {ρ} zero = refl
    aux {ρ} (suc x) = refl
{-# REWRITE ext-ren #-}

rename-ren : ∀{ρ M} → rename ρ M ≡ sub (ren ρ) M
rename-ren-arg : ∀{ρ b}{arg : Arg b} → rename-arg ρ arg ≡ sub-arg (ren ρ) arg
rename-ren-args : ∀{ρ bs}{args : Args bs}
   → rename-args ρ args ≡ sub-args (ren ρ) args
rename-ren {ρ} {` x} = refl
rename-ren {ρ} {op ⦅ args ⦆} = cong ((λ X → op ⦅ X ⦆)) rename-ren-args
rename-ren-arg {ρ} {.■} {ast M} = cong ast rename-ren
rename-ren-arg {ρ} {.(ν _)} {bind arg} =
    cong bind rename-ren-arg
rename-ren-args {ρ} {.[]} {nil} = refl
rename-ren-args {ρ} {.(_ ∷ _)} {cons arg args} =
    cong₂ cons rename-ren-arg rename-ren-args
{-# REWRITE rename-ren #-}

shift-ren-seq : ∀ {ρ τ} → ⟰ (ren ρ ⨟ τ) ≡ ⟰ (ren ρ) ⨟ (` 0 • ⟰ τ)
shift-ren-seq {ρ}{τ} = extensionality (aux {ρ}{τ})
    where
    aux : ∀ {ρ τ} → ∀ x → ⟰ (ren ρ ⨟ τ) x ≡  (⟰ (ren ρ) ⨟ (` 0 • ⟰ τ)) x
    aux zero = refl
    aux (suc x) = refl

shift-seq-ren : ∀ {ρ} → ren suc ⨟ ` 0 • ⟰ (ren ρ) ≡ ren (⟰ᵣ ρ)
shift-seq-ren {ρ} = extensionality aux
    where
    aux : ∀ {ρ} → ∀ x → (ren suc ⨟ ` 0 • ⟰ (ren ρ)) x ≡ ren (⟰ᵣ ρ) x
    aux {ρ} zero = refl
    aux {ρ} (suc x) = refl

shift-seq-sub : ∀{σ M} → ren suc ⨟ M • σ ≡ σ
shift-seq-sub {σ}{M} = extensionality (aux{σ}{M})
    where
    aux : ∀{σ M} → ∀ x → (ren suc ⨟ M • σ) x ≡ σ x
    aux {σ} {M} zero = refl
    aux {σ} {M} (suc x) = refl

ext-ren-sub : ∀ {ρ}{τ} → ext (ren ρ) ⨟ ext τ ≡ ext (ren ρ ⨟ τ)
ext-ren-sub {ρ}{τ} = extensionality (aux{ρ}{τ})
    where
    aux : ∀{ρ}{τ} → ∀ x → (ext (ren ρ) ⨟ ext τ) x ≡ ext (ren ρ ⨟ τ) x
    aux {ρ} {τ} zero = refl
    aux {ρ} {τ} (suc x) = refl
{-# REWRITE ext-ren-sub #-}

ren-sub : ∀ {τ ρ M} → sub τ (sub (ren ρ) M) ≡ sub (ren ρ ⨟ τ) M
ren-sub-arg : ∀ {τ ρ b}{arg : Arg b}
   → sub-arg τ (sub-arg (ren ρ) arg) ≡ sub-arg (ren ρ ⨟ τ) arg
ren-sub-args : ∀ {τ ρ bs}{args : Args bs}
   → sub-args τ (sub-args (ren ρ) args) ≡ sub-args (ren ρ ⨟ τ) args
ren-sub {τ} {ρ} {` x} = refl
ren-sub {τ} {ρ} {op ⦅ args ⦆} = cong ((λ X → op ⦅ X ⦆)) ren-sub-args
ren-sub-arg {τ} {ρ} {.■} {ast M} = cong ast (ren-sub{τ}{ρ}{M})
ren-sub-arg {τ} {ρ} {.(ν _)} {bind arg} = cong bind (ren-sub-arg{ext τ}{extr ρ})
ren-sub-args {τ} {ρ} {.[]} {nil} = refl
ren-sub-args {τ} {ρ} {.(_ ∷ _)} {cons arg args} =
   cong₂ cons ren-sub-arg ren-sub-args
{-# REWRITE ren-sub #-}

ren-suc-extr : ∀{ρ} → ren suc ⨟ ren (extr ρ) ≡ ren ρ ⨟ ren suc
ren-suc-extr {ρ} = extensionality aux
    where
    aux : ∀ x → (ren suc ⨟ ren (extr ρ)) x ≡ (ren ρ ⨟ ren suc) x
    aux zero = refl
    aux (suc x) = refl
{-# REWRITE ren-suc-extr #-}

ext-sub-ren : ∀ {σ ρ} → ext σ ⨟ ext (ren ρ) ≡ ext (σ ⨟ ren ρ)
ext-sub-ren {σ}{ρ} = extensionality (aux{σ}{ρ})
    where
    aux : ∀ {σ ρ} → ∀ x → (ext σ ⨟ ext (ren ρ)) x ≡ (ext (σ ⨟ ren ρ)) x
    aux {σ} {ρ} zero = refl
    aux {σ} {ρ} (suc x) = refl

sub-ren : ∀{ρ σ M} → sub (ren ρ) (sub σ M) ≡ sub (σ ⨟ ren ρ) M
sub-ren-arg : ∀{ρ σ b}{arg : Arg b} → sub-arg (ren ρ) (sub-arg σ arg) ≡ sub-arg (σ ⨟ ren ρ) arg
sub-ren-args : ∀{ρ σ bs}{args : Args bs} → sub-args (ren ρ) (sub-args σ args) ≡ sub-args (σ ⨟ ren ρ) args
sub-ren {ρ} {σ} {` x} = refl
sub-ren {ρ} {σ} {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-ren-args
sub-ren-arg {ρ} {σ} {.■} {ast M} = cong ast (sub-ren{ρ}{σ}{M})
sub-ren-arg {ρ} {σ} {.(ν _)} {bind arg} = cong bind sub-ren-arg
sub-ren-args {ρ} {σ} {.[]} {nil} = refl
sub-ren-args {ρ} {σ} {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-ren-arg sub-ren-args
{-# REWRITE sub-ren #-}

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
FV-args nil y = ⊥
FV-args (cons arg args) y = FV-arg arg y ⊎ FV-args args y
