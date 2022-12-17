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
 Renaming (for internal use)
----------------------------------------------------------------------------}

module Renaming where

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

open Renaming

{----------------------------------------------------------------------------
 Substitution
----------------------------------------------------------------------------}

Subst : Set
Subst = Var → ABT

infixr 6 _•_
_•_ : ABT → Subst → Subst
(M • σ) 0 = M
(M • σ) (suc x) = σ x

{----------------------------------------------------------------------------
 The following module is for internal use only.
 ----------------------------------------------------------------------------}
module Private where

  ⟰ : Subst → Subst
  ⟰ σ x = rename suc (σ x)

  exts : Subst → Subst
  exts σ = ` 0 • ⟰ σ

  sub : Subst → ABT → ABT
  sub-arg : Subst → {b : Sig} → Arg b → Arg b
  sub-args : Subst → {bs : List Sig} → Args bs → Args bs

  sub σ (` x) = σ x
  sub σ (op ⦅ args ⦆) = op ⦅ sub-args σ args ⦆
  sub-arg σ (ast M) = ast (sub σ M)
  sub-arg σ (bind M) = bind (sub-arg (exts σ) M)
  sub-args σ nil = nil
  sub-args σ (cons arg args) = cons (sub-arg σ arg) (sub-args σ args)

  {- TODO: make ren abstract -}
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

  cons-seq-dist : ∀ σ τ M → (M • σ) ⨟ τ ≡ sub τ M • (σ ⨟ τ)
  cons-seq-dist σ τ M = extensionality aux
      where
      aux : ∀{σ τ M} → ∀ x → ((M • σ) ⨟ τ) x ≡ (sub τ M • (σ ⨟ τ)) x
      aux {σ} {τ} {M} zero = refl
      aux {σ} {τ} {M} (suc x) = refl
  {-# REWRITE cons-seq-dist #-}

  ext-ren : ∀{ρ} → (` 0) • ⟰ (ren ρ) ≡ ren (extr ρ)
  ext-ren {ρ} = extensionality aux
      where
      aux : ∀{ρ} → ∀ x → exts (ren ρ) x ≡ ren (extr ρ) x
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

  ext-ren-sub : ∀ {ρ}{τ} → exts (ren ρ) ⨟ exts τ ≡ exts (ren ρ ⨟ τ)
  ext-ren-sub {ρ}{τ} = extensionality (aux{ρ}{τ})
      where
      aux : ∀{ρ}{τ} → ∀ x → (exts (ren ρ) ⨟ exts τ) x ≡ exts (ren ρ ⨟ τ) x
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
  ren-sub-arg {τ} {ρ} {.(ν _)} {bind arg} = cong bind (ren-sub-arg{exts τ}{extr ρ})
  ren-sub-args {τ} {ρ} {.[]} {nil} = refl
  ren-sub-args {τ} {ρ} {.(_ ∷ _)} {cons arg args} =
     cong₂ cons ren-sub-arg ren-sub-args
  {-# REWRITE ren-sub #-}

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

  sub-sub : ∀{σ τ M} → sub τ (sub σ M) ≡ sub (σ ⨟ τ) M
  sub-sub-arg : ∀{σ τ b}{arg : Arg b} → sub-arg τ (sub-arg σ arg) ≡ sub-arg (σ ⨟ τ) arg
  sub-sub-args : ∀{σ τ bs}{args : Args bs} → sub-args τ (sub-args σ args) ≡ sub-args (σ ⨟ τ) args
  sub-sub {σ} {τ} {` x} = refl
  sub-sub {σ} {τ} {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-sub-args
  sub-sub-arg {σ} {τ} {.■} {ast M} = cong ast (sub-sub{σ}{τ}{M})
  sub-sub-arg {σ} {τ} {.(ν _)} {bind arg} = cong bind sub-sub-arg
  sub-sub-args {σ} {τ} {.[]} {nil} = refl
  sub-sub-args {σ} {τ} {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-sub-arg sub-sub-args
  {-# REWRITE sub-sub #-}

  shift-seq : ∀{σ} → ⟰ σ ≡ σ ⨟ ren suc
  shift-seq {σ} = refl

  idᵣ : Rename
  idᵣ x = x

  extr-id : (0 •ᵣ ⟰ᵣ idᵣ) ≡ idᵣ {- extr idᵣ ≡ idᵣ -}
  extr-id = extensionality aux
    where
    aux : ∀ x → extr idᵣ x ≡ idᵣ x
    aux zero = refl
    aux (suc x) = refl
  {-# REWRITE extr-id #-}

  id : Subst
  id x = ` x

  ext-id : exts id ≡ id
  ext-id = refl

  sub-id : ∀ {M} → sub id M ≡ M
  sub-arg-id : ∀ {b}{arg : Arg b} → sub-arg id arg ≡ arg
  sub-args-id : ∀ {bs}{args : Args bs} → sub-args id args ≡ args
  sub-id {` x} = refl
  sub-id {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-args-id
  sub-arg-id {.■} {ast M} = cong ast sub-id
  sub-arg-id {.(ν _)} {bind arg} = cong bind sub-arg-id
  sub-args-id {.[]} {nil} = refl
  sub-args-id {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-arg-id sub-args-id
  {-# REWRITE sub-id #-}

{----------------------------------------------------------------------------
 Public
----------------------------------------------------------------------------}

abstract {- experimenting with making ren abstract -Jeremy -}
  ren : Rename → Subst
  ren = Private.ren

  ren-def : ∀ ρ x → ren ρ x ≡ ` ρ x
  ren-def ρ x = refl

abstract
  
  ↑ : Subst
  ↑ = ren suc

  up-def : ↑ ≡ ren suc
  up-def = refl

  infixr 5 _⨟_
  _⨟_ : Subst → Subst → Subst
  σ ⨟ τ = Private._⨟_ σ τ

  id : Subst
  id = Private.id
    
ext : Subst → Subst
ext σ = ` 0 • (σ ⨟ ↑)

abstract
  ⟪_⟫ : Subst → ABT → ABT
  ⟪ σ ⟫ M = Private.sub σ M

  ⟪_⟫₊ : Subst → {bs : List Sig} → Args bs → Args bs
  ⟪ σ ⟫₊ args = Private.sub-args σ args

  ⟪_⟫ₐ : Subst → {b : Sig} → Arg b → Arg b
  ⟪ σ ⟫ₐ arg = Private.sub-arg σ arg

  id-var : ∀{x} → id x ≡ ` x
  id-var {x} = refl
  {-# REWRITE id-var #-}
  
  sub-var : ∀ σ x → ⟪ σ ⟫ (` x) ≡ σ x
  sub-var σ x = refl
  {- REWRITE sub-var -}
  
  sub-op : ∀{σ : Subst}{op : Op}{args : Args (sig op)}
     → ⟪ σ ⟫ (op ⦅ args ⦆) ≡ op ⦅ ⟪ σ ⟫₊ args ⦆
  sub-op {σ}{op}{args} = refl
  {-# REWRITE sub-op #-}

  sub-arg-ast : ∀{σ M} → ⟪ σ ⟫ₐ (ast M) ≡ ast (⟪ σ ⟫ M)
  sub-arg-ast {σ}{M} = refl
  {-# REWRITE sub-arg-ast #-}
  
  sub-arg-bind : ∀{σ b}{arg : Arg b}
     → ⟪ σ ⟫ₐ (bind arg) ≡ bind (⟪ ext σ ⟫ₐ arg)
  sub-arg-bind {σ}{b}{arg} = refl
  {-# REWRITE sub-arg-bind #-}

  sub-args-nil : ∀{σ} → ⟪ σ ⟫₊ nil ≡ nil
  sub-args-nil {σ} = refl
  {-# REWRITE sub-args-nil #-}

  sub-args-cons : ∀{σ}{b}{bs}{arg : Arg b}{args : Args bs}
     → ⟪ σ ⟫₊ (cons arg args) ≡ cons (⟪ σ ⟫ₐ arg) (⟪ σ ⟫₊ args)
  sub-args-cons {σ}{arg}{args} = refl
  {-# REWRITE sub-args-cons #-}

  sub-head : ∀ σ M → ⟪ M • σ ⟫ (` 0) ≡ M
  sub-head σ M = refl
  {-# REWRITE sub-head #-}

  sub-tail : ∀ σ M → ↑ ⨟ M • σ ≡ σ
  sub-tail σ M = extensionality (aux{σ}{M})
      where
      aux : ∀{σ M} → ∀ x → (↑ ⨟ M • σ) x ≡ σ x
      aux {σ} {M} zero = refl
      aux {σ} {M} (suc x) = refl
  {-# REWRITE sub-tail #-}

  sub-id : ∀ M → ⟪ id ⟫ M ≡ M
  sub-id M = Private.sub-id
  {-# REWRITE sub-id #-}  

  sub-eta : ∀ σ → (⟪ σ ⟫ (` 0)) • (↑ ⨟ σ) ≡ σ
  sub-eta σ = extensionality aux
    where
    aux : ∀ {σ} x → ((⟪ σ ⟫ (` 0)) • (↑ ⨟ σ)) x ≡ σ x
    aux {σ} zero = refl
    aux {σ} (suc x) = refl
  {-# REWRITE sub-eta #-}  

  sub-id-right : ∀ (σ : Subst) → σ ⨟ id ≡ σ 
  sub-id-right σ = refl
  {-# REWRITE sub-id-right #-}  

  sub-id-left : (σ : Subst) → id ⨟ σ ≡ σ
  sub-id-left σ = refl
  {-# REWRITE sub-id-left #-}

  sub-assoc : ∀ σ τ θ → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  sub-assoc σ τ θ = refl
  {-# REWRITE sub-assoc #-}
  
  cons-seq : ∀ σ τ M → (M • σ) ⨟ τ ≡ ⟪ τ ⟫ M • (σ ⨟ τ)
  cons-seq σ τ M = refl
  {-# REWRITE cons-seq #-}  

  compose-sub : ∀ σ τ M → ⟪ τ ⟫ (⟪ σ ⟫ M) ≡ ⟪ σ ⨟ τ ⟫ M
  compose-sub σ τ M = refl
  {-# REWRITE compose-sub #-}  

  cons-zero-up : ` 0 • ↑ ≡ id
  cons-zero-up = refl
  {-# REWRITE cons-zero-up #-}  

  seq-def : ∀ σ τ x → (σ ⨟ τ) x ≡ ⟪ τ ⟫ (σ x)
  seq-def σ τ x = refl

  up-var : ∀ x → ↑ x ≡ ` suc x
  up-var x = refl

  ext-ren-extr : ∀ ρ → (` 0) • (ren ρ ⨟ ↑) ≡ ren (extr ρ)
  ext-ren-extr ρ = refl
  {- REWRITE ext-ren-extr -}
  
  ren-extr-def : ∀ ρ → ren (extr ρ) ≡ ` 0 • (ren ρ ⨟ ↑)
  ren-extr-def ρ = refl
  {-# REWRITE ren-extr-def #-}

  ren-extr-zero : ∀ ρ → ren (extr ρ) 0 ≡ ` 0
  ren-extr-zero ρ = refl
  {- REWRITE ren-extr-zero -}

  ren-extr-suc : ∀ ρ x → ren (extr ρ) (suc x) ≡ ` suc (ρ x)
  ren-extr-suc ρ x = refl
  {- REWRITE ren-extr-suc -}

  seq-up-ren-suc : ∀ σ x → (σ ⨟ ↑) x ≡ Private.sub (Private.ren suc) (σ x)  
  seq-up-ren-suc σ x = refl

  ren-seq-up : ∀ ρ x → (ren ρ ⨟ ↑) x ≡ ` suc (ρ x)
  ren-seq-up ρ x = refl
  {- REWRITE ren-seq-up -}

_[_] : ABT → ABT → ABT
N [ M ] =  ⟪ M • id ⟫ N

_〔_〕 : ABT → ABT → ABT
_〔_〕 N M = ⟪ ext (M • id) ⟫ N

substitution : ∀{M N L} → M [ N ] [ L ] ≡ M 〔 L 〕 [ N [ L ] ]
substitution {M}{N}{L} = refl

exts-sub-cons : ∀ {σ N V} → (⟪ ext σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
exts-sub-cons {σ}{N}{V} = refl

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
