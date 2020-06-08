{-# OPTIONS --rewriting #-}

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)

module Syntax where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Var

infixr 6 _•_

data Substitution : (V : Set) → Set where
  ↑ : (k : ℕ) → ∀{V} → Substitution V
  _•_ : ∀{V} → V → Substitution V → Substitution V

id : ∀ {V} → Substitution V
id = ↑ 0

module GenericSubst (V : Set) (var→val : Var → V) (shift : V → V)
  (var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x)) where

  ⧼_⧽ : Substitution V → Var → V
  ⧼ ↑ k ⧽ x = var→val (k + x)
  ⧼ y • σ ⧽ 0 = y
  ⧼ y • σ ⧽ (suc x) = ⧼ σ ⧽ x

  g-inc : Substitution V → Substitution V
  g-inc (↑ k) = ↑ (suc k)
  g-inc (v • ρ) = shift v • g-inc ρ

  g-extend : V → Substitution V → Substitution V
  g-extend v σ = v • g-inc σ
  
  g-ext : Substitution V → Substitution V
  g-ext σ = g-extend (var→val 0) σ
  
  g-drop : (k : ℕ) → Substitution V → Substitution V
  g-drop k (↑ k') = ↑ (k + k')
  g-drop zero (v • σ) = v • σ
  g-drop (suc k) (v • σ) = g-drop k σ

  g-drop-0 : ∀ σ → g-drop 0 σ ≡ σ
  g-drop-0 (↑ k) = refl
  g-drop-0 (v • σ) = refl

  {-# REWRITE g-drop-0 #-}

  g-drop-add : ∀{x : Var} (k : ℕ) (σ : Substitution V)
           → ⧼ g-drop k σ ⧽ x ≡ ⧼ σ ⧽ (k + x)
  g-drop-add {x} k (↑ k') rewrite +-comm k k' | +-assoc k' k x = refl
  g-drop-add {x} zero (v • σ) = refl
  g-drop-add {x} (suc k) (v • σ) = g-drop-add k σ

  g-drop-drop : ∀ k k' σ → g-drop (k + k') σ ≡ g-drop k (g-drop k' σ)
  g-drop-drop k k' (↑ k₁) rewrite +-assoc k k' k₁ = refl
  g-drop-drop zero k' (v • σ) = refl
  g-drop-drop (suc k) zero (v • σ) rewrite +-comm k 0 = refl
  g-drop-drop (suc k) (suc k') (v • σ)
      with g-drop-drop (suc k) k' σ
  ... | IH rewrite +-comm k (suc k') | +-comm k k' = IH

  g-drop-inc : ∀ k σ → g-drop k (g-inc σ) ≡ g-inc (g-drop k σ)
  g-drop-inc k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
  g-drop-inc zero (v • σ) = refl
  g-drop-inc (suc k) (v • σ) = g-drop-inc k σ

  g-Z-shift : ∀ x → ⧼ var→val 0 • ↑ 1 ⧽ x ≡ var→val x
  g-Z-shift 0 = refl
  g-Z-shift (suc x) = refl

  g-inc-shift : ∀ ρ x → ⧼ g-inc ρ ⧽ x ≡ shift (⧼ ρ ⧽ x)
  g-inc-shift (↑ k) x rewrite +-comm k x = var→val-suc-shift
  g-inc-shift (y • ρ) zero = refl
  g-inc-shift (y • ρ) (suc x) = g-inc-shift ρ x

  g-drop-ext : ∀ k ρ → g-drop (suc k) (g-ext ρ) ≡ g-inc (g-drop k ρ)
  g-drop-ext k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
  g-drop-ext zero (x • ρ) = refl
  g-drop-ext (suc k) (x • ρ) = g-drop-inc k ρ

open GenericSubst Var (λ x → x) suc (λ {x} → refl)
    using () renaming (⧼_⧽ to ⦉_⦊; g-Z-shift to Z-shiftr) public
open GenericSubst Var (λ x → x) suc (λ {x} → refl)
    using ()
    renaming (g-inc to inc; g-drop to dropr; g-drop-0 to dropr-0;
              g-drop-add to dropr-add; g-drop-drop to dropr-dropr;
              g-drop-inc to dropr-inc;
              g-inc-shift to inc-suc; g-drop-ext to dropr-ext)
{-# REWRITE inc-suc #-}

Rename : Set
Rename = Substitution Var

abstract
  ext : Rename → Rename
  ext ρ = 0 • inc ρ

abstract
  infixr 5 _⨟ᵣ_

  _⨟ᵣ_ : Rename → Rename → Rename
  ↑ k ⨟ᵣ ρ = dropr k ρ
  (x • ρ₁) ⨟ᵣ ρ₂ = ⦉ ρ₂ ⦊ x • (ρ₁ ⨟ᵣ ρ₂)

abstract
  ext-0 : ∀ ρ → ⦉ ext ρ ⦊ 0 ≡ 0
  ext-0 (↑ k) = refl
  ext-0 (x • ρ) = refl

  ext-suc : ∀ ρ x → ⦉ ext ρ ⦊ (suc x) ≡ suc (⦉ ρ ⦊ x)
  ext-suc (↑ k) x = refl
  ext-suc (x₁ • ρ) zero = refl
  ext-suc (x₁ • ρ) (suc x) = inc-suc ρ x

{-# REWRITE ext-0 ext-suc #-}

module OpSig (Op : Set) (sig : Op → List ℕ)  where

  open import AbstractBindingTree Op sig public

  {----------------------------------------------------------------------------
    Renaming
   ---------------------------------------------------------------------------}

  rename : Rename → ABT → ABT
  ren-arg : ∀ {n}→ Rename → Arg n → Arg n
  ren-args : ∀ {S} → Rename → Args S → Args S

  rename ρ (` x) = ` ⦉ ρ ⦊ x
  rename ρ (o ⦅ As ⦆) = o ⦅ ren-args ρ As ⦆

  ren-arg ρ (ast M) = ast (rename ρ M)
  ren-arg ρ (bind A) = bind (ren-arg (ext ρ) A)

  ren-args ρ nil = nil
  ren-args ρ (cons A As) = cons (ren-arg ρ A) (ren-args ρ As)

  abstract

    ren-head  : ∀{ρ : Rename}{x : Var}
             → rename (x • ρ) (` 0) ≡ ` x
    ren-head = refl

    ren-tail : ∀{ρ : Rename}{x : Var}
             → (↑ 1 ⨟ᵣ x • ρ) ≡ ρ
    ren-tail {ρ = ↑ k} = refl
    ren-tail {ρ = x • ρ} = refl

    {-# REWRITE ren-tail #-}

    inc=⨟ᵣ↑ : ∀ ρ → inc ρ ≡ ρ ⨟ᵣ ↑ 1
    inc=⨟ᵣ↑ (↑ k) rewrite +-comm k 1 = refl
    inc=⨟ᵣ↑ (x • ρ) = cong (_•_ (suc x)) (inc=⨟ᵣ↑ ρ)

    ext-cons-shift : ∀ ρ → ext ρ ≡ (0 • (ρ ⨟ᵣ ↑ 1))
    ext-cons-shift (↑ k) rewrite +-comm k 1 = refl
    ext-cons-shift (x • ρ) rewrite inc=⨟ᵣ↑ ρ = refl

    {- REWRITE ext-cons-shift -}
    
  abstract

    ren-η : ∀ (ρ : Rename) (x : Var)
          → ⦉ ⦉ ρ ⦊ 0 • (↑ 1 ⨟ᵣ ρ) ⦊ x ≡ ⦉ ρ ⦊ x
    ren-η ρ 0 = refl
    ren-η ρ (suc x) = dropr-add 1 ρ

    ren-idL : (ρ : Rename)
           → id ⨟ᵣ ρ ≡ ρ
    ren-idL (↑ k) = refl
    ren-idL (x • ρ) = refl

    ren-dist :  ∀ {ρ : Rename} {τ : Rename}{x : Var}
             → ((x • ρ) ⨟ᵣ τ) ≡ ((⦉ τ ⦊ x) • (ρ ⨟ᵣ τ))
    ren-dist = refl

    ren-op : ∀ {σ : Rename} {o : Op}{Ms : Args (sig o)}
            → rename σ (o ⦅ Ms ⦆)  ≡ o ⦅ ren-args σ Ms ⦆
    ren-op = refl        

    seq-rename : ∀ ρ₁ ρ₂ x → ⦉ ρ₁ ⨟ᵣ ρ₂ ⦊ x ≡ ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x)
    seq-rename (↑ k) ρ₂ x = dropr-add k ρ₂
    seq-rename (x₁ • ρ₁) ρ₂ zero = refl
    seq-rename (x₁ • ρ₁) ρ₂ (suc x) = seq-rename ρ₁ ρ₂ x

  private

    abstract 
      dropr-seq : ∀ k ρ ρ' → dropr k (ρ ⨟ᵣ ρ') ≡ (dropr k ρ ⨟ᵣ ρ')
      dropr-seq k (↑ k₁) ρ' = sym (dropr-dropr k k₁ ρ')
      dropr-seq zero (x • ρ) ρ' = refl
      dropr-seq (suc k) (x • ρ) ρ' = dropr-seq k ρ ρ'

    abstract
      inc-seq : ∀ ρ₁ ρ₂ → (inc ρ₁ ⨟ᵣ ext ρ₂) ≡ inc (ρ₁ ⨟ᵣ ρ₂)
      inc-seq (↑ k) ρ₂ = dropr-ext k ρ₂
      inc-seq (x • ρ₁) ρ₂ rewrite inc-seq ρ₁ ρ₂ | ext-suc ρ₂ x = refl

  abstract

    ren-assoc : ∀ {σ τ θ : Rename}
              → (σ ⨟ᵣ τ) ⨟ᵣ θ ≡ σ ⨟ᵣ τ ⨟ᵣ θ
    ren-assoc {↑ k} {τ} {θ} = sym (dropr-seq k τ θ)
    ren-assoc {x • σ} {τ} {θ}
        rewrite seq-rename τ θ x | ren-assoc {σ}{τ}{θ} = refl

    {-# REWRITE ren-assoc #-}

    compose-ext : ∀{ρ₁ ρ₂ : Rename}
                → (ext ρ₁ ⨟ᵣ ext ρ₂) ≡ ext (ρ₁ ⨟ᵣ ρ₂)
    compose-ext {ρ₁}{ρ₂} =
      begin
          ext ρ₁ ⨟ᵣ ext ρ₂
      ≡⟨ cong₂ (λ X Y → X ⨟ᵣ Y) (ext-cons-shift ρ₁) (ext-cons-shift ρ₂)  ⟩
          (0 • (ρ₁ ⨟ᵣ ↑ 1)) ⨟ᵣ (0 • (ρ₂ ⨟ᵣ ↑ 1))
      ≡⟨⟩
          0 • ((ρ₁ ⨟ᵣ ρ₂) ⨟ᵣ ↑ 1)
      ≡⟨ sym (ext-cons-shift (ρ₁ ⨟ᵣ ρ₂))  ⟩
          ext (ρ₁ ⨟ᵣ ρ₂)
      ∎

    compose-rename : ∀{M : ABT}{ρ₁ ρ₂ : Rename}
      → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ ⨟ᵣ ρ₂) M
    compose-rename-arg : ∀{n}{A : Arg n}{ρ₁ ρ₂ : Rename}
      → ren-arg ρ₂ (ren-arg ρ₁ A) ≡ ren-arg (ρ₁ ⨟ᵣ ρ₂) A
    compose-rename-args : ∀{S}{As : Args S}{ρ₁ ρ₂ : Rename}
      → ren-args ρ₂ (ren-args ρ₁ As) ≡ ren-args (ρ₁ ⨟ᵣ ρ₂) As
    compose-rename {` x} {ρ₁} {ρ₂} = cong `_ (sym (seq-rename ρ₁ ρ₂ x))
    compose-rename {op ⦅ As ⦆} {ρ₁} {ρ₂} =
        cong (λ □ → op ⦅ □ ⦆) compose-rename-args
    compose-rename-arg {.0} {ast M} {ρ₁} {ρ₂} = cong ast compose-rename
    compose-rename-arg {.(suc _)} {bind A} {ρ₁} {ρ₂}
        rewrite sym (compose-ext {ρ₁}{ρ₂}) = cong bind compose-rename-arg
    compose-rename-args {.[]} {nil} {ρ₁} {ρ₂} = refl
    compose-rename-args {.(_ ∷ _)} {cons x As} {ρ₁} {ρ₂} =
        cong₂ cons compose-rename-arg compose-rename-args

  {----------------------------------------------------------------------------
   Substitution
   ---------------------------------------------------------------------------}

  Subst : Set
  Subst = Substitution ABT

  open GenericSubst ABT `_ (rename (↑ 1)) (λ {x} → refl)
      using () renaming (⧼_⧽ to ⟦_⟧; g-Z-shift to Z-shift) public
  {-# REWRITE Z-shift #-}
  open GenericSubst ABT `_ (rename (↑ 1)) (λ {x} → refl)
      using () renaming (g-inc to incs; g-drop to drop; g-drop-0 to drop-0;
                         g-drop-add to drop-add; g-drop-drop to drop-drop;
                         g-drop-inc to drop-incs;
                         g-inc-shift to incs-rename)
  
  abstract
    exts : Subst → Subst
    exts σ = ` 0 • incs σ

  ⟪_⟫ : Subst → ABT → ABT
  ⟪_⟫ₐ : ∀{n} → Subst → Arg n → Arg n
  ⟪_⟫₊ : ∀{S} → Subst → Args S → Args S

  ⟪ σ ⟫ (` x) = ⟦ σ ⟧ x
  ⟪ σ ⟫ (o ⦅ As ⦆) = o ⦅ ⟪ σ ⟫₊ As ⦆

  ⟪ σ ⟫ₐ (ast M) = ast (⟪ σ ⟫ M)
  ⟪ σ ⟫ₐ (bind M) = bind (⟪ (exts σ) ⟫ₐ M)

  ⟪ σ ⟫₊ nil = nil
  ⟪ σ ⟫₊ (cons A As) = cons (⟪ σ ⟫ₐ A) (⟪ σ ⟫₊ As)

  subst-zero : ABT → Subst
  subst-zero M = M • id

  _ : ∀{x : Var} → ⟦ subst-zero (` x) ⟧ 0 ≡ (` x)
  _ = refl

  _ : ∀{x : Var} → ⟦ subst-zero (` x) ⟧ 1 ≡ ` 0
  _ = refl

  _[_] : ABT → ABT → ABT
  _[_] N M =  ⟪ subst-zero M ⟫ N

  abstract
    infixr 5 _⨟_

    _⨟_ : Subst → Subst → Subst
    ↑ k ⨟ τ = drop k τ
    (M • σ) ⨟ τ = ⟪ τ ⟫ M • (σ ⨟ τ)

    sub-head : (M : ABT) (σ : Subst)
             → ⟦ M • σ ⟧ 0 ≡ M
    sub-head M σ = refl

    sub-tail : (M : ABT) (σ : Subst)
             → (↑ 1 ⨟ M • σ) ≡ σ
    sub-tail M (↑ k) = refl
    sub-tail M (L • σ) = refl

    {-# REWRITE sub-tail #-}

    sub-suc : (M : ABT) (σ : Subst) (x : Var)
             → ⟪ M • σ ⟫ (` suc x) ≡ ⟪ σ ⟫ (` x)
    sub-suc M σ x = refl

  abstract
    sub-η : ∀ (σ : Subst) (x : Var)
          → ⟦ (⟪ σ ⟫ (` 0) • (↑ 1 ⨟ σ)) ⟧ x ≡ ⟦ σ ⟧ x
    sub-η σ 0 = refl
    sub-η σ (suc x) = drop-add 1 σ

    {-# REWRITE sub-η #-}
    
  abstract
    shift : ∀ x k → ⟪ ↑ k ⟫ (` x) ≡ ` (k + x)
    shift x k = refl

    sub-idL : (σ : Subst)
           → id ⨟ σ ≡ σ
    sub-idL (↑ k) = refl
    sub-idL (M • σ) = refl

    {-# REWRITE sub-idL #-}

    sub-dist :  ∀ {σ : Subst} {τ : Subst} {M : ABT}
             → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
    sub-dist = refl

    sub-op : ∀ {σ op args} → ⟪ σ ⟫ (op ⦅ args ⦆) ≡ op ⦅ ⟪ σ ⟫₊ args ⦆
    sub-op = refl

    sub-ast : ∀ {σ M} → ⟪ σ ⟫ₐ (ast M) ≡ ast (⟪ σ ⟫ M)
    sub-ast = refl

    sub-bind : ∀ {σ n arg} → ⟪ σ ⟫ₐ (bind {n} arg) ≡ bind (⟪ exts σ ⟫ₐ arg)
    sub-bind = refl

    sub-nil : ∀ {σ} → ⟪ σ ⟫₊ nil ≡ nil
    sub-nil = refl

    sub-cons : ∀{σ n bs arg args}
             → ⟪ σ ⟫₊ (cons {n}{bs} arg args) ≡ cons (⟪ σ ⟫ₐ arg) (⟪ σ ⟫₊ args)
    sub-cons = refl

  rename→subst : Rename → Subst
  rename→subst (↑ k) = ↑ k 
  rename→subst (x • ρ) = ` x • rename→subst ρ

  private

    incs-rename-inc : ∀ ρ → incs (rename→subst ρ) ≡ rename→subst (inc ρ)
    incs-rename-inc (↑ k) = refl
    incs-rename-inc (x • ρ) = cong (_•_ (` suc x)) (incs-rename-inc ρ)

  abstract
    exts-rename-ext : ∀ ρ → exts (rename→subst ρ) ≡ rename→subst (ext ρ)
    exts-rename-ext (↑ k) = refl
    exts-rename-ext (x • ρ) =
        cong (λ □ → (` 0) • (` suc x) • □) (incs-rename-inc ρ)

  rename-subst-interp : ∀ ρ x → (` ⦉ ρ ⦊ x) ≡ ⟦ rename→subst ρ ⟧ x
  rename-subst-interp (↑ k) x = refl
  rename-subst-interp (y • ρ) zero = refl
  rename-subst-interp (y • ρ) (suc x) = rename-subst-interp ρ x

  rename-subst : ∀ ρ M → rename ρ M ≡ ⟪ rename→subst ρ ⟫ M
  ren-arg-subst : ∀ {n} ρ A → ren-arg {n} ρ A ≡ ⟪ (rename→subst ρ) ⟫ₐ A
  ren-args-subst : ∀ {S} ρ As → ren-args {S} ρ As ≡ ⟪ rename→subst ρ ⟫₊ As

  rename-subst (↑ k) (` x) = refl
  rename-subst (y • ρ) (` zero) = refl
  rename-subst (y • ρ) (` suc x) = rename-subst-interp ρ x
  rename-subst ρ (op ⦅ As ⦆) = cong (λ □ → op ⦅ □ ⦆) (ren-args-subst ρ As)

  ren-arg-subst ρ (ast M) = cong ast (rename-subst ρ M)
  ren-arg-subst ρ (bind A) =
    let IH = ren-arg-subst (ext ρ) A in
    begin
      bind (ren-arg (ext ρ) A)                ≡⟨ cong bind IH ⟩
      bind (⟪ rename→subst (ext ρ) ⟫ₐ A)      ≡⟨ cong (λ □ → bind (⟪ □ ⟫ₐ A))
                                                    (sym (exts-rename-ext ρ)) ⟩
      bind (⟪ exts (rename→subst ρ) ⟫ₐ A)     ∎
  ren-args-subst ρ nil = refl
  ren-args-subst ρ (cons A As) =
    cong₂ cons (ren-arg-subst ρ A) (ren-args-subst ρ As)

  private
    abstract
      incs=⨟↑ : ∀ σ → incs σ ≡ σ ⨟ ↑ 1
      incs=⨟↑ (↑ k) rewrite +-comm k 1 = refl
      incs=⨟↑ (M • σ) = cong₂ _•_ (rename-subst (↑ 1) M) (incs=⨟↑ σ)

  abstract
    exts-cons-shift : ∀ σ → exts σ ≡ (` 0 • (σ ⨟ ↑ 1))
    exts-cons-shift (↑ k) rewrite +-comm k 1 = refl
    exts-cons-shift (M • σ) rewrite rename-subst (↑ 1) M | incs=⨟↑ σ = refl

    seq-subst : ∀ σ τ x → ⟦ σ ⨟ τ ⟧ x ≡ ⟪ τ ⟫ (⟦ σ ⟧ x)
    seq-subst (↑ k) τ x = drop-add k τ
    seq-subst (M • σ) τ zero = refl
    seq-subst (M • σ) τ (suc x) = seq-subst σ τ x

  exts-ids : ∀{σ : Subst} → (∀ x → ⟦ σ ⟧ x ≡ ` x) → (∀ x → ⟦ exts σ ⟧ x ≡ ` x)
  exts-ids {σ} is-id zero
      rewrite exts-cons-shift σ = refl
  exts-ids {σ} is-id (suc x)
      rewrite exts-cons-shift σ | seq-subst σ (↑ 1) x | is-id x = refl

  sub-id' : ∀ {M : ABT} {σ : Subst}
           → (∀ x → ⟦ σ ⟧ x ≡ ` x)
           → ⟪ σ ⟫ M ≡ M
  sub-arg-id : ∀{n} {A : Arg n} {σ : Subst}
           → (∀ x → ⟦ σ ⟧ x ≡ ` x)
           → ⟪ σ ⟫ₐ A ≡ A
  subs-id : ∀{S} {Ms : Args S} {σ : Subst}
           → (∀ x → ⟦ σ ⟧ x ≡ ` x)
           → ⟪ σ ⟫₊ Ms ≡ Ms

  sub-id' {` x} is-id = is-id x
  sub-id' {op ⦅ As ⦆} is-id = cong (λ □ → op ⦅ □ ⦆) (subs-id is-id)

  sub-arg-id {A = ast M} is-id = cong ast (sub-id' is-id)
  sub-arg-id {A = bind A}{σ} is-id =
      cong bind (sub-arg-id (exts-ids {σ = σ} is-id) )

  subs-id {Ms = nil} is-id = refl
  subs-id {Ms = cons A Ms} is-id = cong₂ cons (sub-arg-id is-id) (subs-id is-id)

  sub-id : ∀ {M : ABT} 
           → ⟪ id ⟫ M ≡ M
  sub-id = sub-id' λ x → refl

  {-# REWRITE sub-id #-}

  rename-id : {M : ABT} → rename (↑ 0) M ≡ M
  rename-id {M} =
    begin
      rename (↑ 0) M         ≡⟨ rename-subst (↑ 0) M ⟩
      ⟪ ↑ 0 ⟫ M              ≡⟨ refl {- sub-id' (λ x → refl)-} ⟩
      M                      ∎

  {-# REWRITE rename-id #-}
    
  abstract
    sub-idR : ∀ σ → σ ⨟ id ≡ σ 
    sub-idR (↑ k) rewrite +-comm k 0 = refl
    sub-idR (M • σ) rewrite sub-idR σ = refl

    {-# REWRITE sub-idR #-}
    
  exts-0 : ∀ σ → ⟦ exts σ ⟧ 0 ≡ ` 0
  exts-0 σ rewrite exts-cons-shift σ = refl

  {-# REWRITE exts-0 #-}
    
  exts-suc' : ∀ σ x → ⟦ exts σ ⟧ (suc x) ≡ rename (↑ 1) (⟦ σ ⟧ x)
  exts-suc' σ x rewrite exts-cons-shift σ | rename-subst (↑ 1) (⟦ σ ⟧ x)
      | seq-subst σ (↑ 1) x = refl

  exts-suc-rename : ∀ σ x → ⟦ exts σ ⟧ (suc x) ≡ rename (↑ 1) (⟪ σ ⟫ (` x))
  exts-suc-rename σ x rewrite exts-cons-shift σ | rename-subst (↑ 1) (⟦ σ ⟧ x)
      | seq-subst σ (↑ 1) x = refl

  {-# REWRITE exts-suc-rename #-}

  abstract
    commute-subst-rename : ∀{M : ABT}{σ : Subst}
                            {ρ : Rename}
         → (∀{x : Var} → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
         → ⟪ exts σ ⟫ (rename ρ M) ≡ rename ρ (⟪ σ ⟫ M)
    commute-subst-rename-arg : ∀{n}{A : Arg n}{σ : Subst}
                            {ρ : Rename}
         → (∀{x : Var} → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
         → ⟪ exts σ ⟫ₐ (ren-arg ρ A) ≡ ren-arg ρ (⟪ σ ⟫ₐ A)
    commute-subst-renames : ∀{S}{Ms : Args S}{σ : Subst}
                            {ρ : Rename}
         → (∀{x : Var} → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
         → ⟪ exts σ ⟫₊ (ren-args ρ Ms) ≡ ren-args ρ (⟪ σ ⟫₊ Ms)
    commute-subst-rename {` x} r = r
    commute-subst-rename {op ⦅ As ⦆} r =
        cong (λ □ → op ⦅ □ ⦆) (commute-subst-renames r)
    commute-subst-rename-arg {.0} {ast M}{σ}{ρ} r
        rewrite commute-subst-rename {M}{σ}{ρ} r = refl
    commute-subst-rename-arg {.(suc _)} {bind A}{σ}{ρ} r =
       cong bind (commute-subst-rename-arg (λ {x} → G{x}))
       where
       G : ∀{x} → ⟦ exts (exts σ) ⟧ (⦉ ext ρ ⦊ x) ≡ rename (ext ρ) (⟦ exts σ ⟧ x)
       G {zero} = refl
       G {suc x} =
         begin
            ⟦ exts (exts σ) ⟧ (⦉ ext ρ ⦊ (suc x))
         ≡⟨ cong (λ □ → ⟦ exts □ ⟧ (⦉ ext ρ ⦊ (suc x))) (exts-cons-shift σ) ⟩
            ⟦ exts (` 0 • (σ ⨟ ↑ 1)) ⟧ (⦉ ext ρ ⦊ (suc x))
         ≡⟨ cong (λ □ → ⟦ (` 0) • (` 1 • □) ⟧ (suc (⦉ ρ ⦊ x))) (incs=⨟↑ (σ ⨟ ↑ 1)) ⟩
            ⟦ (` 0) • (` 1 • ((σ ⨟ ↑ 1) ⨟ ↑ 1)) ⟧ (suc (⦉ ρ ⦊ x))
         ≡⟨ cong (λ □ → ⟦ (` 1 • (□ ⨟ ↑ 1)) ⟧ (⦉ ρ ⦊ x)) (sym (incs=⨟↑ σ)) ⟩
            ⟦ exts σ ⨟ ↑ 1 ⟧ (⦉ ρ ⦊ x)
         ≡⟨ seq-subst (exts σ) (↑ 1) (⦉ ρ ⦊ x) ⟩
            ⟪ ↑ 1 ⟫ (⟦ exts σ ⟧ (⦉ ρ ⦊ x))
         ≡⟨ sym (rename-subst (↑ 1) (⟦ exts σ ⟧ (⦉ ρ ⦊ x))) ⟩
            rename (↑ 1) (⟦ exts σ ⟧ (⦉ ρ ⦊ x))
         ≡⟨ cong (λ □ → rename (↑ 1) □) (r {x}) ⟩
            rename (↑ 1) (rename ρ (⟦ σ ⟧ x))
         ≡⟨ compose-rename {⟦ σ ⟧ x}{ρ} ⟩
            rename (ρ ⨟ᵣ ↑ 1) (⟦ σ ⟧ x)
         ≡⟨ cong (λ □ → rename □ (⟦ σ ⟧ x)) (sym (inc=⨟ᵣ↑ ρ)) ⟩
            rename (inc ρ) (⟦ σ ⟧ x)
         ≡⟨ cong (λ □ → rename □ (⟦ σ ⟧ x)) (ren-tail {inc ρ}{x}) ⟩
            rename (↑ 1 ⨟ᵣ (0 • inc ρ)) (⟦ σ ⟧ x)
         ≡⟨ sym (compose-rename {⟦ σ ⟧ x}{↑ 1}{0 • inc ρ}) ⟩
            rename (0 • inc ρ) (rename (↑ 1) (⟦ σ ⟧ x))
         ≡⟨ cong (λ □ → rename (0 • inc ρ) □) (sym (incs-rename σ x)) ⟩
            rename (0 • inc ρ) (⟦ incs σ ⟧ x)
         ≡⟨⟩
            rename (ext ρ) (⟦ exts σ ⟧ (suc x))
         ∎
    commute-subst-renames {.[]} {nil} r = refl
    commute-subst-renames {.(_ ∷ _)} {cons A As} r =
        cong₂ cons (commute-subst-rename-arg r) (commute-subst-renames r)

  private

    abstract
      drop-seq : ∀ k ρ ρ' → drop k (ρ ⨟ ρ') ≡ (drop k ρ ⨟ ρ')
      drop-seq k (↑ k₁) ρ' = sym (drop-drop k k₁ ρ')
      drop-seq zero (x • ρ) ρ' = refl
      drop-seq (suc k) (x • ρ) ρ' = drop-seq k ρ ρ'

    abstract
      drop-exts : ∀ k ρ → drop (suc k) (exts ρ) ≡ incs (drop k ρ)
      drop-exts k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
      drop-exts zero (M • ρ) = refl
      drop-exts (suc k) (M • ρ) = drop-incs k ρ

      incs-seq : ∀ ρ₁ ρ₂ → (incs ρ₁ ⨟ exts ρ₂) ≡ incs (ρ₁ ⨟ ρ₂)
      incs-seq (↑ k) ρ₂ = drop-exts k ρ₂
      incs-seq (M • ρ₁) ρ₂ rewrite incs-seq ρ₁ ρ₂
          | commute-subst-rename {M}{ρ₂}{↑ 1} (λ {x} → exts-suc' ρ₂ x) = refl

  abstract
    exts-seq : ∀ {σ₁ : Subst} {σ₂ : Subst}
             → exts σ₁ ⨟ exts σ₂ ≡ exts (σ₁ ⨟ σ₂)
    exts-seq {↑ k} {σ₂} rewrite drop-incs k σ₂ = refl
    exts-seq {M • σ₁} {σ₂} rewrite exts-0 σ₂
        | commute-subst-rename {M}{σ₂}{↑ 1} (λ {x} → exts-suc' σ₂ x)
        | incs-seq σ₁ σ₂ = refl

  sub-sub : ∀{M : ABT} {σ₁ : Subst}{σ₂ : Subst} 
              → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
  sub-sub-arg : ∀{n}{A : Arg n} {σ₁ : Subst}{σ₂ : Subst} 
              → ⟪ σ₂ ⟫ₐ (⟪ σ₁ ⟫ₐ A) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ₐ A
  sub-subs : ∀{S}{Ms : Args S} {σ₁ : Subst}{σ₂ : Subst} 
              → ⟪ σ₂ ⟫₊ (⟪ σ₁ ⟫₊ Ms) ≡ ⟪ σ₁ ⨟ σ₂ ⟫₊ Ms
  sub-sub {` x} {σ₁} {σ₂} rewrite seq-subst σ₁ σ₂ x = refl
  sub-sub {op ⦅ As ⦆} {σ₁} {σ₂} = cong (λ □ → op ⦅ □ ⦆) (sub-subs {Ms = As})
  sub-sub-arg {.0} {ast M} {σ₁} {σ₂} = cong ast (sub-sub{M}{σ₁}{σ₂})
  sub-sub-arg {.(suc _)} {bind A} {σ₁} {σ₂}
      rewrite sub-sub-arg {A = A}{exts σ₁}{exts σ₂}
      | exts-seq {σ₁} {σ₂} = cong bind refl
  sub-subs {.[]} {nil} {σ₁} {σ₂} = refl
  sub-subs {.(_ ∷ _)} {cons A Ms} {σ₁} {σ₂} = cong₂ cons sub-sub-arg sub-subs

  {-# REWRITE sub-sub #-}

  abstract
    sub-assoc : ∀ {σ τ θ : Subst}
              → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
    sub-assoc {↑ k} {τ} {θ} = sym (drop-seq k τ θ)
    sub-assoc {M • σ} {τ} {θ}
        rewrite sub-assoc {σ}{τ}{θ} = refl

    {-# REWRITE sub-assoc #-}
    
  exts-suc : ∀ σ x → ⟦ exts σ ⟧ (suc x) ≡ ⟦ σ ⨟ ↑ 1 ⟧ x
  exts-suc σ x rewrite exts-cons-shift σ = refl

  abstract
    subst-zero-exts-cons : ∀{σ : Subst}{M : ABT}
                         → exts σ ⨟ subst-zero M ≡ M • σ
    subst-zero-exts-cons {σ}{M} rewrite incs=⨟↑ σ = refl
    {-
    rewrite exts-cons-shift σ = {!!} {- refl -}
    -}

    subst-commute : ∀{N : ABT}{M : ABT}{σ : Subst }
        → (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
    subst-commute {N}{M}{σ} rewrite exts-cons-shift σ = refl

  commute-subst : ∀{N : ABT}{M : ABT}{σ : Subst }
      → ⟪ σ ⟫ (N [ M ]) ≡ (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ]
  commute-subst {N}{M}{σ} = sym (subst-commute {N}{M}{σ})

  abstract
    rename-subst-commute : ∀{N : ABT}{M : ABT}{ρ : Rename }
        → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
    rename-subst-commute{N}{M}{ρ}
        rewrite rename-subst ρ M | rename-subst (ext ρ) N
        | rename-subst ρ (⟪ M • ↑ 0 ⟫ N)
        | sym (exts-rename-ext ρ)
        | exts-cons-shift (rename→subst ρ)
        = refl

  _〔_〕 : ABT → ABT → ABT
  _〔_〕 N M = ⟪ exts (subst-zero M) ⟫ N

  substitution : ∀{M : ABT}{N : ABT}{L : ABT}
      → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
  substitution {M}{N}{L} =
     sym (subst-commute{N = M}{M = N}{σ = subst-zero L})

  abstract
    exts-sub-cons : ∀ σ N V → (⟪ exts σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
    exts-sub-cons σ N V
        rewrite exts-cons-shift σ = refl

  {----------------------------------------------------------------------------
    Well-formed Abstract Binding Trees
   ---------------------------------------------------------------------------}

  data WF-arg : ℕ → {b : ℕ} → Arg b → Set
  data WF-args : ℕ → {bs : List ℕ} → Args bs → Set 
  data WF : ℕ → ABT → Set 

  data WF-arg where
    WF-ast : ∀ {n} {M} → WF n M → WF-arg n (ast M)
    WF-bind : ∀ {n b} {A : Arg b} → WF-arg (suc n) A → WF-arg n (bind A)

  data WF-args where
    WF-nil : ∀{n} → WF-args n nil
    WF-cons : ∀{n b bs} {A : Arg b} {As : Args bs}
            → WF-arg n A → WF-args n As → WF-args n (cons A As)

  data WF where
    WF-var : ∀ {n} x → x < n → WF n (` x)
    WF-op : ∀ {n} {op : Op} {args : Args (sig op)}
          → WF-args n args
          → WF n (op ⦅ args ⦆)

  WF? : (n : ℕ) → (M : ABT) → Dec (WF n M)
  WF-arg? : (n : ℕ) → {b : ℕ} → (A : Arg b) → Dec (WF-arg n A)
  WF-args? : (n : ℕ) → {bs : List ℕ} → (As : Args bs) → Dec (WF-args n As)
  WF? n (` x)
      with suc x ≤? n
  ... | yes x<n = yes (WF-var x x<n)
  ... | no ¬x<n = no G
      where G : ¬ WF n (` x)
            G (WF-var x lt) = ¬x<n lt
  WF? n (op ⦅ As ⦆)
      with WF-args? n As
  ... | yes wf = yes (WF-op wf)
  ... | no ¬wf = no G
      where G : ¬ WF n (op ⦅ As ⦆)
            G (WF-op wf) = ¬wf wf
  WF-arg? n (ast M)
      with WF? n M
  ... | yes wf = yes (WF-ast wf)
  ... | no ¬wf = no G
      where G : ¬ WF-arg n (ast M)
            G (WF-ast wf) = ¬wf wf
  WF-arg? n (bind A)
      with WF-arg? (suc n) A
  ... | yes wf = yes (WF-bind wf)
  ... | no ¬wf = no G
      where G : ¬ WF-arg n (bind A)
            G (WF-bind wf) = ¬wf wf

  WF-args? n nil = yes WF-nil
  WF-args? n (cons A As)
      with WF-arg? n A
  ... | no ¬wf = no G
      where G : ¬ WF-args n (cons A As)
            G (WF-cons wfA wfAs) = ¬wf wfA
  ... | yes wfA
      with WF-args? n As
  ... | no ¬wf = no G
      where G : ¬ WF-args n (cons A As)
            G (WF-cons wfA wfAs) = ¬wf wfAs
  ... | yes wfAs = yes (WF-cons wfA wfAs)

  WF-rel : (M : ABT) {n : ℕ} → .(WF n M) → WF n M
  WF-rel M {n} wfM
      with WF? n M
  ... | yes wf = wf
  ... | no ¬wf = ⊥-elimi (¬wf wfM)

  WFRename : ℕ → Rename → ℕ → Set
  WFRename Γ ρ Δ = ∀ {x} → x < Γ → (⦉ ρ ⦊ x) < Δ

  WF-ext : ∀ {Γ Δ ρ}
    → WFRename Γ ρ Δ
      --------------------------------
    → WFRename (suc Γ) (ext ρ) (suc Δ)
  WF-ext {ρ = ρ} ⊢ρ (s≤s z≤n) rewrite ext-0 ρ = s≤s z≤n
  WF-ext {ρ = ρ} ⊢ρ (s≤s (s≤s {m = m}{n = n} m≤n))
      rewrite ext-suc ρ m = s≤s (⊢ρ (s≤s m≤n))

  WF-rename : ∀ {Γ Δ ρ M} → WFRename Γ ρ Δ → WF Γ M → WF Δ (rename ρ M)
  WF-ren-arg : ∀ {Γ Δ ρ b}{A : Arg b} → WFRename Γ ρ Δ
     → WF-arg Γ A → WF-arg Δ (ren-arg ρ A)
  WF-ren-args : ∀ {Γ Δ ρ bs}{As : Args bs} → WFRename Γ ρ Δ
     → WF-args Γ As → WF-args Δ (ren-args ρ As)

  WF-rename {ρ = ρ} ⊢ρ (WF-var x x<Γ) = WF-var (⦉ ρ ⦊ x) (⊢ρ x<Γ)
  WF-rename {Γ}{Δ}{ρ = ρ} ⊢ρ (WF-op {Γ}{op}{As} wfAs) =
      WF-op {Δ}{op}{ren-args ρ As} (WF-ren-args ⊢ρ wfAs)

  WF-ren-arg {ρ = ρ} ⊢ρ (WF-ast wfM) = WF-ast (WF-rename {ρ = ρ} ⊢ρ wfM)
  WF-ren-arg {ρ = ρ} ⊢ρ (WF-bind wfA) =
      WF-bind (WF-ren-arg (WF-ext ⊢ρ) wfA)

  WF-ren-args {ρ = ρ} ⊢ρ WF-nil = WF-nil
  WF-ren-args {ρ = ρ} ⊢ρ (WF-cons wfA wfAs) =
      WF-cons (WF-ren-arg ⊢ρ wfA) (WF-ren-args ⊢ρ wfAs)

  WFSubst : ℕ → Subst → ℕ → Set
  WFSubst Γ σ Δ = ∀ {x} → x < Γ → WF Δ (⟦ σ ⟧ x)

  WF-subst : ∀{Γ Δ σ M} → WFSubst Γ σ Δ → WF Γ M → WF Δ (⟪ σ ⟫ M)
  WF-subst-arg : ∀{Γ Δ σ b}{A : Arg b} → WFSubst Γ σ Δ
     → WF-arg Γ A → WF-arg Δ (⟪ σ ⟫ₐ A)
  WF-subst-args : ∀{Γ Δ σ bs}{As : Args bs} → WFSubst Γ σ Δ
     → WF-args Γ As → WF-args Δ (⟪ σ ⟫₊ As)

  WF-exts : ∀{Γ Δ σ}
     → WFSubst Γ σ Δ
     → WFSubst (suc Γ) (exts σ) (suc Δ)
  WF-exts {σ = σ} wfσ (s≤s z≤n) = WF-var zero (s≤s z≤n)
  WF-exts {σ = σ} wfσ (s≤s (s≤s {m = m} x<Γ)) rewrite exts-suc-rename σ m =
      WF-rename {ρ = ↑ 1} (λ {x} → s≤s) (wfσ {m} (s≤s x<Γ))

  WF-subst Γ⊢σ:Δ (WF-var x x<Γ) = Γ⊢σ:Δ x<Γ
  WF-subst {σ = σ} Γ⊢σ:Δ (WF-op wfAs) =
      WF-op (WF-subst-args Γ⊢σ:Δ wfAs)

  WF-subst-arg {σ = σ} Γ⊢σ:Δ (WF-ast wfM) =
      WF-ast (WF-subst {σ = σ} Γ⊢σ:Δ wfM)
  WF-subst-arg {σ = σ} Γ⊢σ:Δ (WF-bind wfA) =
      WF-bind (WF-subst-arg (WF-exts Γ⊢σ:Δ) wfA)

  WF-subst-args Γ⊢σ:Δ WF-nil = WF-nil
  WF-subst-args {σ = σ} Γ⊢σ:Δ (WF-cons wfA wfAs) =
      WF-cons (WF-subst-arg Γ⊢σ:Δ wfA) (WF-subst-args Γ⊢σ:Δ wfAs) 

  {----------------------------------------------------------------------------
   Extra Things
  ----------------------------------------------------------------------------}

  exts-ext : ∀ σ τ → ((x : ℕ) → ⟦ σ ⟧ x ≡ ⟦ τ ⟧ x)
           → ((x : ℕ) → ⟦ exts σ ⟧ x ≡ ⟦ exts τ ⟧ x)
  exts-ext σ τ eq 0
      rewrite exts-cons-shift σ | exts-cons-shift τ = refl
  exts-ext σ τ eq (suc x)
      rewrite exts-cons-shift σ | exts-cons-shift τ
            | seq-subst σ (↑ 1) x | seq-subst τ (↑ 1) x | eq x = refl

  subst-extensionality : ∀{M : ABT}{σ τ : Subst}
      → (∀ x → ⟦ σ ⟧ x ≡ ⟦ τ ⟧ x)
      → ⟪ σ ⟫ M ≡ ⟪ τ ⟫ M
  sub-arg-ext : ∀{n} {A : Arg n} {σ τ : Subst}
           → (∀ x → ⟦ σ ⟧ x ≡ ⟦ τ ⟧ x)
           → ⟪ σ ⟫ₐ A ≡ ⟪ τ ⟫ₐ A
  sub-args-ext : ∀{S} {Ms : Args S} {σ τ : Subst}
           → (∀ x → ⟦ σ ⟧ x ≡ ⟦ τ ⟧ x)
           → ⟪ σ ⟫₊ Ms ≡ ⟪ τ ⟫₊ Ms

  abstract 
    subst-extensionality {` x} {σ} {τ} eq = eq x
    subst-extensionality {op ⦅ As ⦆} {σ} {τ} eq =
        cong (λ □ → op ⦅ □ ⦆) (sub-args-ext eq)

    sub-arg-ext {A = ast M}{σ}{τ} eq =
        cong ast (subst-extensionality {M}{σ}{τ} eq)
    sub-arg-ext {A = bind A}{σ}{τ} eq =
        cong bind (sub-arg-ext (exts-ext σ τ eq))

    sub-args-ext {Ms = nil} eq = refl
    sub-args-ext {Ms = cons A Ms} eq =
        cong₂ cons (sub-arg-ext eq) (sub-args-ext eq)

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

  data WF-Ctx : ℕ → Ctx → Set
  data WF-CArg : ℕ → ∀{b} → CArg b → Set
  data WF-CArgs : ℕ → ∀{bs} → CArgs bs → Set

  data WF-Ctx where
    WF-hole : ∀{n} → WF-Ctx n CHole
    WF-op : ∀{n}{op}{cargs : CArgs (sig op)}
       → WF-CArgs n cargs
       → WF-Ctx n (COp op cargs)

  data WF-CArg where
    WF-c-ast : ∀{n}{C : Ctx}
       → WF-Ctx n C
       → WF-CArg n (CAst C)
    WF-c-bind : ∀{n}{b}{CA : CArg b}
       → WF-CArg (suc n) {b} CA
       → WF-CArg n (CBind {b} CA)

  data WF-CArgs where
    WF-tcons : ∀{n}{b}{bs}{bs'}{A : Arg b}{cargs : CArgs bs}{eq : bs' ≡ b ∷ bs}
       → WF-arg n A
       → WF-CArgs n cargs
       → WF-CArgs n (tcons {b}{bs}{bs'} A cargs eq)
    WF-ccons : ∀{n}{b}{bs}{bs'}{C : CArg b}{args : Args bs}{eq : bs' ≡ b ∷ bs}
       → WF-CArg n C
       → WF-args n args
       → WF-CArgs n (ccons {b}{bs}{bs'} C args eq)

  WF-plug : ∀{C : Ctx}{N : ABT}{k}
     → WF-Ctx k C
     → WF (k + ctx-depth C) N
     → WF k (plug C N)
  WF-plug-arg : ∀{b}{A : CArg b}{N : ABT}{k}
     → WF-CArg k A
     → WF (k + ctx-depth-arg A) N
     → WF-arg k (plug-arg A N)
  WF-plug-args : ∀{bs}{Cs : CArgs bs}{N : ABT}{k}
     → WF-CArgs k Cs
     → WF (k + ctx-depth-args Cs) N
     → WF-args k (plug-args Cs N)
     
  WF-plug {CHole} {N} {k} wfC wfN
      rewrite +-comm k 0 = wfN
  WF-plug {COp op cargs} {N} {k} (WF-op wf-cargs) wfN =
      WF-op (WF-plug-args{Cs = cargs} wf-cargs wfN )
  WF-plug-arg {zero} {CAst C} {N} {k} (WF-c-ast wfC) wfN =
      WF-ast (WF-plug wfC wfN)
  WF-plug-arg {suc n} {CBind A} {N} {k} (WF-c-bind wfA) wfN =
      WF-bind (WF-plug-arg wfA wfN')
      where
      wfN' : WF (suc k + ctx-depth-arg A) N
      wfN' rewrite +-suc k (ctx-depth-arg A) = wfN
  WF-plug-args {b ∷ bs} {tcons A Cs refl} {N} {k} (WF-tcons wfA wfCs) wfN =
      WF-cons wfA (WF-plug-args {Cs = Cs} wfCs wfN)
  WF-plug-args {b ∷ bs} {ccons C As refl} {N} {k} (WF-ccons wfC wfAs) wfN =
      WF-cons (WF-plug-arg wfC wfN) wfAs

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
  FV? (op ⦅ As ⦆) y = FV-args? As y
  FV-arg? (ast M) y = FV? M y
  FV-arg? (bind A) y = FV-arg? A (suc y)
  FV-args? nil y = false
  FV-args? (cons A As) y = FV-arg? A y ∨ FV-args? As y

  {----------------------------------------------------------------------------
   Convert (Var → Var) Function to Renaming
  ----------------------------------------------------------------------------}

  private
    make-ren : (Var → Var) → ℕ → ℕ → Rename
    make-ren ρ x zero = ↑ 0
    make-ren ρ x (suc m) = ρ x • make-ren ρ (suc x) m

    ⦉make-ren⦊ : ∀{m}{x}{i}{ρ}
       → x < m
       → ⦉ make-ren ρ i m ⦊ x ≡ ρ (x + i)
    ⦉make-ren⦊ {suc m} {zero} {i} {ρ} x<m = refl
    ⦉make-ren⦊ {suc m} {suc x} {i} {ρ} x<m
        with ⦉make-ren⦊ {m} {x} {suc i} {ρ} (≤-pred x<m)
    ... | IH rewrite +-suc x i = 
        IH
     
  make-renaming : (Var → Var) → ℕ → Rename
  make-renaming ρ Γ = make-ren ρ 0 Γ

  ⦉make-renaming⦊ : ∀{Γ}{x}{ρ}
     → x < Γ
     → ⦉ make-renaming ρ Γ ⦊ x ≡ ρ x
  ⦉make-renaming⦊ {Γ}{x}{ρ} x<Γ
      with ⦉make-ren⦊ {i = 0}{ρ} x<Γ
  ... | mr rewrite +-comm x 0 = mr

