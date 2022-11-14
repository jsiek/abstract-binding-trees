{-# OPTIONS --without-K  #-}
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
open import Relation.Nullary using (¬_; Dec; yes; no)
open import ScopedTuple
open import Sig
open import Var
open import Structures using (extensionality)

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

infixr 5 _⨟_
_⨟_ : Subst → Subst → Subst
(σ ⨟ τ) x = sub τ (σ x)

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

cons-seq : ∀{σ τ M} → (M • σ) ⨟ τ ≡ sub τ M • (σ ⨟ τ)
cons-seq {σ}{τ}{M} = extensionality aux
    where
    aux : ∀{σ τ M} → ∀ x → ((M • σ) ⨟ τ) x ≡ (sub τ M • (σ ⨟ τ)) x
    aux {σ} {τ} {M} zero = refl
    aux {σ} {τ} {M} (suc x) = refl

ext-ren : ∀{ρ} → ext (ren ρ) ≡ ren (extr ρ)
ext-ren {ρ} = extensionality aux
    where
    aux : ∀{ρ} → ∀ x → ext (ren ρ) x ≡ ren (extr ρ) x
    aux {ρ} zero = refl
    aux {ρ} (suc x) = refl

rename-ren : ∀{ρ M} → rename ρ M ≡ sub (ren ρ) M
rename-ren-arg : ∀{ρ b}{arg : Arg b} → rename-arg ρ arg ≡ sub-arg (ren ρ) arg
rename-ren-args : ∀{ρ bs}{args : Args bs}
   → rename-args ρ args ≡ sub-args (ren ρ) args
rename-ren {ρ} {` x} = refl
rename-ren {ρ} {op ⦅ args ⦆} = cong ((λ X → op ⦅ X ⦆)) rename-ren-args
rename-ren-arg {ρ} {.■} {ast M} = cong ast rename-ren
rename-ren-arg {ρ} {.(ν _)} {bind arg} rewrite ext-ren {ρ} =
    cong bind rename-ren-arg
rename-ren-args {ρ} {.[]} {nil} = refl
rename-ren-args {ρ} {.(_ ∷ _)} {cons arg args} =
    cong₂ cons rename-ren-arg rename-ren-args

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
