open import Data.Bool
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Nat.Properties
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (¬_)

module Syntax (Op : Set) (sig : Op → List ℕ) where

Var : Set
Var = ℕ

data Args : (sig : List ℕ) → Set

data ABT : Set where
  `_ : Var → ABT
  _⦅_⦆ : (op : Op) → Args (sig op) → ABT

data Arg : (sig : ℕ) → Set where
  ast : ABT → Arg 0
  bind : ∀{n} → Arg n → Arg (suc n)

data Args where
  nil : Args []
  cons : ∀{n bs} → Arg n → Args bs → Args (n ∷ bs)

bind-arg : ∀{m} → (n : ℕ) → Arg m → Arg (n + m)
bind-arg  zero A = A
bind-arg {m} (suc n) A
    with bind-arg {suc m} n (bind A)
... | ih rewrite +-suc n m = ih

bind-ast : ∀(n : ℕ) → ABT → Arg n
bind-ast n M
    with bind-arg n (ast M)
... | A rewrite +-identityʳ n = A


{----------------------------------------------------------------
  Renaming
-----------------------------------------------------------------}

infixr 6 _·_

data Rename : Set where
  ↑ : ∀ (k : ℕ) → Rename
  _·_ : Var → Rename → Rename

⟦_⟧ :  Rename → Var → Var
⟦ ↑ k ⟧ x = k + x
⟦ y · ρ ⟧ 0 = y
⟦ y · ρ ⟧ (suc x) = ⟦ ρ ⟧ x

idᵣ : Rename
idᵣ = ↑ 0

inc : Rename → Rename
inc (↑ k) = ↑ (suc k)
inc (x · ρ) = suc x · inc ρ

ext : Rename → Rename
ext (↑ k) = 0 · ↑ (suc k)
ext (x · ρ) = 0 · suc x · inc ρ

rename : Rename → ABT → ABT
ren-arg : ∀ {n}→ Rename → Arg n → Arg n
ren-args : ∀ {S} → Rename → Args S → Args S

rename ρ (` x) = ` ⟦ ρ ⟧ x
rename ρ (o ⦅ As ⦆) = o ⦅ ren-args ρ As ⦆

ren-arg ρ (ast M) = ast (rename ρ M)
ren-arg ρ (bind A) = bind (ren-arg (ext ρ) A)

ren-args ρ nil = nil
ren-args ρ (cons A As) = cons (ren-arg ρ A) (ren-args ρ As)


dropr : (k : ℕ) → Rename → Rename
dropr k (↑ k') = ↑ (k + k')
dropr zero (x · ρ) = x · ρ
dropr (suc k) (x · ρ) = dropr k ρ

infixr 5 _⨟ᵣ_

_⨟ᵣ_ : Rename → Rename → Rename
↑ k ⨟ᵣ ρ = dropr k ρ
(x · ρ₁) ⨟ᵣ ρ₂ = ⟦ ρ₂ ⟧ x · (ρ₁ ⨟ᵣ ρ₂)

ren-head  : ∀{M : ABT}{ρ : Rename}{x : Var}
         → rename (x · ρ) (` 0) ≡ ` x
ren-head = refl

ren-tail : ∀{M : ABT} {ρ : Rename}{x : Var}
         → (↑ 1 ⨟ᵣ x · ρ) ≡ ρ
ren-tail {ρ = ↑ k} = refl
ren-tail {ρ = x · ρ} = refl

inc=⨟ᵣ↑ : ∀ ρ → inc ρ ≡ ρ ⨟ᵣ ↑ 1
inc=⨟ᵣ↑ (↑ k) rewrite +-comm k 1 = refl
inc=⨟ᵣ↑ (x · ρ) = cong (_·_ (suc x)) (inc=⨟ᵣ↑ ρ)

inc-suc : ∀ ρ x → ⟦ inc ρ ⟧ x ≡ suc (⟦ ρ ⟧ x)
inc-suc (↑ k) x = refl
inc-suc (x₁ · ρ) zero = refl
inc-suc (x₁ · ρ) (suc x) = inc-suc ρ x

ext-cons-shift : ∀ ρ → ext ρ ≡ (0 · (ρ ⨟ᵣ ↑ 1))
ext-cons-shift (↑ k) rewrite +-comm k 1 = refl
ext-cons-shift (x · ρ) rewrite inc=⨟ᵣ↑ ρ = refl

ext-0 : ∀ ρ → ⟦ ext ρ ⟧ 0 ≡ 0
ext-0 (↑ k) = refl
ext-0 (x · ρ) = refl

ext-s : ∀ ρ x → ⟦ ext ρ ⟧ (suc x) ≡ suc (⟦ ρ ⟧ x)
ext-s (↑ k) x = refl
ext-s (x₁ · ρ) zero = refl
ext-s (x₁ · ρ) (suc x) = inc-suc ρ x

dropr-add : ∀{x : Var} (k : ℕ) (σ : Rename)
         → ⟦ dropr k σ ⟧ x ≡ ⟦ σ ⟧ (k + x)
dropr-add {x} k (↑ k') rewrite +-comm k k' | +-assoc k' k x = refl
dropr-add {x} zero (y · σ) = refl
dropr-add {x} (suc k) (y · σ) = dropr-add k σ

ren-η : ∀ (ρ : Rename) (x : Var)
      → ⟦ ⟦ ρ ⟧ 0 · (↑ 1 ⨟ᵣ ρ) ⟧ x ≡ ⟦ ρ ⟧ x
ren-η ρ 0 = refl
ren-η ρ (suc x) = dropr-add 1 ρ

Z-shiftr : ∀{x : Var}
        → ⟦ 0 · ↑ 1 ⟧ x ≡ ⟦ idᵣ ⟧ x
Z-shiftr {0} = refl
Z-shiftr {suc x} = refl

ren-idL : (ρ : Rename)
       → idᵣ ⨟ᵣ ρ ≡ ρ
ren-idL (↑ k) = refl
ren-idL (x · ρ) = refl

ren-dist :  ∀ {ρ : Rename} {τ : Rename}{x : Var}
         → ((x · ρ) ⨟ᵣ τ) ≡ ((⟦ τ ⟧ x) · (ρ ⨟ᵣ τ))
ren-dist = refl

ren-op : ∀ {σ : Rename} {o : Op}{Ms : Args (sig o)}
        → rename σ (o ⦅ Ms ⦆)  ≡ o ⦅ ren-args σ Ms ⦆
ren-op = refl        

seq-rename : ∀ ρ₁ ρ₂ x → ⟦ ρ₁ ⨟ᵣ ρ₂ ⟧ x ≡ ⟦ ρ₂ ⟧ (⟦ ρ₁ ⟧ x)
seq-rename (↑ k) ρ₂ x = dropr-add k ρ₂
seq-rename (x₁ · ρ₁) ρ₂ zero = refl
seq-rename (x₁ · ρ₁) ρ₂ (suc x) = seq-rename ρ₁ ρ₂ x

dropr-0 : ∀ ρ → dropr 0 ρ ≡ ρ
dropr-0 (↑ k) = refl
dropr-0 (x · ρ) = refl

dropr-dropr : ∀ k k' ρ → dropr (k + k') ρ ≡ dropr k (dropr k' ρ)
dropr-dropr k k' (↑ k₁) rewrite +-assoc k k' k₁ = refl
dropr-dropr zero k' (x · ρ) rewrite dropr-0 (dropr k' (x · ρ)) = refl
dropr-dropr (suc k) zero (x · ρ) rewrite +-comm k 0 = refl
dropr-dropr (suc k) (suc k') (x · ρ)
    with dropr-dropr (suc k) k' ρ
... | IH rewrite +-comm k (suc k') | +-comm k k' = IH

dropr-seq : ∀ k ρ ρ' → dropr k (ρ ⨟ᵣ ρ') ≡ (dropr k ρ ⨟ᵣ ρ')
dropr-seq k (↑ k₁) ρ' = sym (dropr-dropr k k₁ ρ')
dropr-seq zero (x · ρ) ρ' = refl
dropr-seq (suc k) (x · ρ) ρ' = dropr-seq k ρ ρ'

dropr-inc : ∀ k ρ → dropr k (inc ρ) ≡ inc (dropr k ρ)
dropr-inc k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
dropr-inc zero (x · ρ) = refl
dropr-inc (suc k) (x · ρ) = dropr-inc k ρ

dropr-ext : ∀ k ρ → dropr (suc k) (ext ρ) ≡ inc (dropr k ρ)
dropr-ext k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
dropr-ext zero (x · ρ) = refl
dropr-ext (suc k) (x · ρ) = dropr-inc k ρ

inc-seq : ∀ ρ₁ ρ₂ → (inc ρ₁ ⨟ᵣ ext ρ₂) ≡ inc (ρ₁ ⨟ᵣ ρ₂)
inc-seq (↑ k) ρ₂ = dropr-ext k ρ₂
inc-seq (x · ρ₁) ρ₂ rewrite inc-seq ρ₁ ρ₂ | ext-s ρ₂ x = refl

ren-assoc : ∀ {σ τ θ : Rename}
          → (σ ⨟ᵣ τ) ⨟ᵣ θ ≡ σ ⨟ᵣ τ ⨟ᵣ θ
ren-assoc {↑ k} {τ} {θ} = sym (dropr-seq k τ θ)
ren-assoc {x · σ} {τ} {θ} rewrite seq-rename τ θ x | ren-assoc {σ}{τ}{θ} = refl

compose-ext : ∀{ρ₁ ρ₂ : Rename}
            → (ext ρ₁ ⨟ᵣ ext ρ₂) ≡ ext (ρ₁ ⨟ᵣ ρ₂)
compose-ext {ρ₁}{ρ₂} rewrite ext-cons-shift ρ₁ | ext-cons-shift ρ₂
    | ext-cons-shift (ρ₁ ⨟ᵣ ρ₂) | ren-assoc {ρ₁} {↑ 1} {ρ₂ ⨟ᵣ ↑ 1}
    | ren-assoc {ρ₁}{↑ 1}{0 · (ρ₂ ⨟ᵣ ↑ 1)} | dropr-0 (ρ₂ ⨟ᵣ ↑ 1)
    | ren-assoc {ρ₁}{ρ₂}{↑ 1} = refl

compose-rename : ∀{M : ABT}{ρ₁ ρ₂ : Rename}
  → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ ⨟ᵣ ρ₂) M
compose-rename-arg : ∀{n}{A : Arg n}{ρ₁ ρ₂ : Rename}
  → ren-arg ρ₂ (ren-arg ρ₁ A) ≡ ren-arg (ρ₁ ⨟ᵣ ρ₂) A
compose-rename-args : ∀{S}{As : Args S}{ρ₁ ρ₂ : Rename}
  → ren-args ρ₂ (ren-args ρ₁ As) ≡ ren-args (ρ₁ ⨟ᵣ ρ₂) As
compose-rename {` x} {ρ₁} {ρ₂} = cong `_ (sym (seq-rename ρ₁ ρ₂ x))
compose-rename {op ⦅ As ⦆} {ρ₁} {ρ₂} = cong (λ □ → op ⦅ □ ⦆) compose-rename-args
compose-rename-arg {.0} {ast M} {ρ₁} {ρ₂} = cong ast compose-rename
compose-rename-arg {.(suc _)} {bind A} {ρ₁} {ρ₂}
    rewrite sym (compose-ext {ρ₁}{ρ₂}) = cong bind compose-rename-arg
compose-rename-args {.[]} {nil} {ρ₁} {ρ₂} = refl
compose-rename-args {.(_ ∷ _)} {cons x As} {ρ₁} {ρ₂} =
    cong₂ cons compose-rename-arg compose-rename-args

{-------------------------------------------------------------------------------
 Substitution
-------------------------------------------------------------------------------}

infixr 6 _•_

data Subst : Set  where
  ⇑ : (k : ℕ) → Subst
  _•_ : ABT → Subst → Subst

∣_∣ : Subst → Var → ABT
∣ ⇑ k ∣ x = ` (k + x)
∣ M • σ ∣ 0 = M
∣ M • σ ∣ (suc x) = ∣ σ ∣ x

incs : Subst → Subst
incs (⇑ k) = ⇑ (suc k)
incs (M • σ) =  rename (↑ 1) M • incs σ

exts : Subst → Subst
exts (⇑ k) = ` 0 • ⇑ (suc k)
exts (M • σ) = ` 0 • incs (M • σ)

⟪_⟫ : Subst → ABT → ABT
subst-arg : ∀{n} → Subst → Arg n → Arg n
subst-args : ∀{S} → Subst → Args S → Args S

⟪ σ ⟫ (` x) = ∣ σ ∣ x
⟪ σ ⟫ (o ⦅ As ⦆) = o ⦅ subst-args σ As ⦆

subst-arg σ (ast M) = ast (⟪ σ ⟫ M)
subst-arg σ (bind M) = bind (subst-arg (exts σ) M)

subst-args σ nil = nil
subst-args σ (cons A As) = cons (subst-arg σ A) (subst-args σ As)

ids : Subst
ids = ⇑ 0

subst-zero : ABT → Subst
subst-zero M = M • ids

_ : ∀{x : Var} → ∣ subst-zero (` x) ∣ 0 ≡ (` x)
_ = refl

_ : ∀{x : Var} → ∣ subst-zero (` x) ∣ 1 ≡ ` 0
_ = refl

_[_] : ABT → ABT → ABT
_[_] N M =  ⟪ subst-zero M ⟫ N

drop : (k : ℕ) → Subst → Subst
drop k (⇑ k') = ⇑ (k + k')
drop zero (M • σ) = M • σ
drop (suc k) (M • σ) = drop k σ

infixr 5 _⨟_

_⨟_ : Subst → Subst → Subst
⇑ k ⨟ τ = drop k τ
(M • σ) ⨟ τ = ⟪ τ ⟫ M • (σ ⨟ τ)

sub-head : ∀{M : ABT}{σ : Subst}
         → ⟪ M • σ ⟫ (` 0) ≡ M
sub-head = refl

sub-tail : ∀{M : ABT} {σ : Subst}
         → (⇑ 1 ⨟ M • σ) ≡ σ
sub-tail {σ = ⇑ k} = refl
sub-tail {σ = M • σ} = refl

drop-add : ∀{x : Var} (k : ℕ) (σ : Subst)
         → ∣ drop k σ ∣ x ≡ ∣ σ ∣ (k + x)
drop-add {x} k (⇑ k') rewrite +-comm k k' | +-assoc k' k x = refl
drop-add {x} zero (M • σ) = refl
drop-add {x} (suc k) (M • σ) = drop-add k σ

sub-η : ∀ (σ : Subst) (x : Var)
      → ∣ (⟪ σ ⟫ (` 0) • (⇑ 1 ⨟ σ)) ∣ x ≡ ∣ σ ∣ x
sub-η σ 0 = refl
sub-η σ (suc x) = drop-add 1 σ

Z-shift : ∀{x : Var}
        → ∣ ` 0 • ⇑ 1 ∣ x ≡ ∣ ids ∣ x
Z-shift {0} = refl
Z-shift {suc x} = refl

sub-idL : (σ : Subst)
       → ids ⨟ σ ≡ σ
sub-idL (⇑ k) = refl
sub-idL (M • σ) = refl

sub-dist :  ∀ {σ : Subst} {τ : Subst} {M : ABT}
         → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
sub-dist = refl

sub-op : ∀ {σ : Subst} {o : Op}{Ms : Args (sig o)}
        → ⟪ σ ⟫ (o ⦅ Ms ⦆)  ≡ o ⦅ subst-args σ Ms ⦆
sub-op = refl        

rename→subst : Rename → Subst
rename→subst (↑ k) = ⇑ k 
rename→subst (x · ρ) = ` x • rename→subst ρ

incs-rename-inc : ∀ ρ → incs (rename→subst ρ) ≡ rename→subst (inc ρ)
incs-rename-inc (↑ k) = refl
incs-rename-inc (x · ρ) = cong (_•_ (` suc x)) (incs-rename-inc ρ)

exts-rename-ext : ∀ ρ → exts (rename→subst ρ) ≡ rename→subst (ext ρ)
exts-rename-ext (↑ k) = refl
exts-rename-ext (x · ρ) = cong (λ □ → (` 0) • (` suc x) • □) (incs-rename-inc ρ)

rename-subst-interp : ∀ ρ x → (` ⟦ ρ ⟧ x) ≡ ∣ rename→subst ρ ∣ x
rename-subst-interp (↑ k) x = refl
rename-subst-interp (y · ρ) zero = refl
rename-subst-interp (y · ρ) (suc x) = rename-subst-interp ρ x

rename-subst : ∀ ρ M → rename ρ M ≡ ⟪ rename→subst ρ ⟫ M
ren-arg-subst : ∀ {n} ρ A → ren-arg {n} ρ A ≡ subst-arg (rename→subst ρ) A
ren-args-subst : ∀ {S} ρ As → ren-args {S} ρ As ≡ subst-args (rename→subst ρ) As

rename-subst (↑ k) (` x) = refl
rename-subst (y · ρ) (` zero) = refl
rename-subst (y · ρ) (` suc x) = rename-subst-interp ρ x
rename-subst ρ (op ⦅ As ⦆) = cong (λ □ → op ⦅ □ ⦆) (ren-args-subst ρ As)

ren-arg-subst ρ (ast M) = cong ast (rename-subst ρ M)
ren-arg-subst ρ (bind A) =
  let IH = ren-arg-subst (ext ρ) A in
  begin
     bind (ren-arg (ext ρ) A)                       ≡⟨ cong bind IH ⟩
     bind (subst-arg (rename→subst (ext ρ)) A)      ≡⟨ cong (λ □ → bind (subst-arg □ A)) (sym (exts-rename-ext ρ)) ⟩
     bind (subst-arg (exts (rename→subst ρ)) A)     ∎
ren-args-subst ρ nil = refl
ren-args-subst ρ (cons A As) =
  cong₂ cons (ren-arg-subst ρ A) (ren-args-subst ρ As)

incs=⨟⇑ : ∀ σ → incs σ ≡ σ ⨟ ⇑ 1
incs=⨟⇑ (⇑ k) rewrite +-comm k 1 = refl
incs=⨟⇑ (M • σ) = cong₂ _•_ (rename-subst (↑ 1) M) (incs=⨟⇑ σ)

exts-cons-shift : ∀ σ → exts σ ≡ (` 0 • (σ ⨟ ⇑ 1))
exts-cons-shift (⇑ k) rewrite +-comm k 1 = refl
exts-cons-shift (M • σ) rewrite rename-subst (↑ 1) M | incs=⨟⇑ σ = refl

seq-subst : ∀ σ τ x → ∣ σ ⨟ τ ∣ x ≡ ⟪ τ ⟫ (∣ σ ∣ x)
seq-subst (⇑ k) τ x = drop-add k τ
seq-subst (M • σ) τ zero = refl
seq-subst (M • σ) τ (suc x) = seq-subst σ τ x

exts-ids : ∀{σ : Subst} → (∀ x → ∣ σ ∣ x ≡ ` x) → (∀ x → ∣ exts σ ∣ x ≡ ` x)
exts-ids {σ} id zero
    rewrite exts-cons-shift σ = refl
exts-ids {σ} id (suc x)
    rewrite exts-cons-shift σ | seq-subst σ (⇑ 1) x | id x = refl

sub-id' : ∀ {M : ABT} {σ : Subst}
         → (∀ x → ∣ σ ∣ x ≡ ` x)
         → ⟪ σ ⟫ M ≡ M
sub-arg-id : ∀{n} {A : Arg n} {σ : Subst}
         → (∀ x → ∣ σ ∣ x ≡ ` x)
         → subst-arg σ A ≡ A
subs-id : ∀{S} {Ms : Args S} {σ : Subst}
         → (∀ x → ∣ σ ∣ x ≡ ` x)
         → subst-args σ Ms ≡ Ms

sub-id' {` x} id = id x
sub-id' {op ⦅ As ⦆} id = cong (λ □ → op ⦅ □ ⦆) (subs-id id)

sub-arg-id {A = ast M} id = cong ast (sub-id' id)
sub-arg-id {A = bind A}{σ} id = cong bind (sub-arg-id (exts-ids {σ = σ} id) )

subs-id {Ms = nil} id = refl
subs-id {Ms = cons A Ms} id = cong₂ cons (sub-arg-id id) (subs-id id)

sub-id : ∀ {M : ABT} 
         → ⟪ ids ⟫ M ≡ M
sub-id = sub-id' λ x → refl

rename-id : {M : ABT} → rename (↑ 0) M ≡ M
rename-id {M} =
  begin
    rename (↑ 0) M         ≡⟨ rename-subst (↑ 0) M ⟩
    ⟪ ⇑ 0 ⟫ M              ≡⟨ sub-id' (λ x → refl) ⟩
    M                      ∎

sub-idR : ∀ σ → σ ⨟ ids ≡ σ 
sub-idR (⇑ k) rewrite +-comm k 0 = refl
sub-idR (M • σ) rewrite sub-id {M} | sub-idR σ = refl

exts-0 : ∀ σ → ∣ exts σ ∣ 0 ≡ ` 0
exts-0 σ rewrite exts-cons-shift σ = refl

exts-s : ∀ σ x → ∣ exts σ ∣ (suc x) ≡ rename (↑ 1) (∣ σ ∣ x)
exts-s σ x rewrite exts-cons-shift σ | rename-subst (↑ 1) (∣ σ ∣ x)
    | seq-subst σ (⇑ 1) x = refl

commute-subst-rename : ∀{M : ABT}{σ : Subst}
                        {ρ : Rename}
     → (∀{x : Var} → ∣ exts σ ∣ (⟦ ρ ⟧ x) ≡ rename ρ (∣ σ ∣ x))
     → ⟪ exts σ ⟫ (rename ρ M) ≡ rename ρ (⟪ σ ⟫ M)
commute-subst-rename-arg : ∀{n}{A : Arg n}{σ : Subst}
                        {ρ : Rename}
     → (∀{x : Var} → ∣ exts σ ∣ (⟦ ρ ⟧ x) ≡ rename ρ (∣ σ ∣ x))
     → subst-arg (exts σ) (ren-arg ρ A) ≡ ren-arg ρ (subst-arg σ A)
commute-subst-renames : ∀{S}{Ms : Args S}{σ : Subst}
                        {ρ : Rename}
     → (∀{x : Var} → ∣ exts σ ∣ (⟦ ρ ⟧ x) ≡ rename ρ (∣ σ ∣ x))
     → subst-args (exts σ) (ren-args ρ Ms) ≡ ren-args ρ (subst-args σ Ms)
commute-subst-rename {` x} r = r
commute-subst-rename {op ⦅ As ⦆} r =
    cong (λ □ → op ⦅ □ ⦆) (commute-subst-renames r)
commute-subst-rename-arg {.0} {ast M} r = cong ast (commute-subst-rename {M} r)
commute-subst-rename-arg {.(suc _)} {bind A}{σ}{ρ} r =
   cong bind (commute-subst-rename-arg G)
   where
   G : {x : Var} → ∣ exts (exts σ) ∣ (⟦ ext ρ ⟧ x) ≡ rename (ext ρ) (∣ exts σ ∣ x)
   G {zero} rewrite ext-0 ρ | exts-cons-shift σ | ext-0 ρ = refl
   G {suc x} rewrite ext-s ρ x | exts-cons-shift (exts σ)
      | seq-subst (exts σ) (⇑ 1) (⟦ ρ ⟧ x) | r {x}
      | exts-cons-shift σ | seq-subst σ (⇑ 1) x
      | sym (rename-subst (↑ 1) (rename ρ (∣ σ ∣ x)))
      | sym (rename-subst (↑ 1) (∣ σ ∣ x)) | compose-rename {∣ σ ∣ x} {ρ} {↑ 1}
      | compose-rename {∣ σ ∣ x} {↑ 1} {ext ρ}
      | dropr-ext 0 ρ | sym (dropr-inc 0 ρ)
      | dropr-0 (inc ρ) | inc=⨟ᵣ↑ ρ = refl

commute-subst-renames {.[]} {nil} r = refl
commute-subst-renames {.(_ ∷ _)} {cons A As} r =
    cong₂ cons (commute-subst-rename-arg r) (commute-subst-renames r)

drop-0 : ∀ ρ → drop 0 ρ ≡ ρ
drop-0 (⇑ k) = refl
drop-0 (M • ρ) = refl

drop-drop : ∀ k k' ρ → drop (k + k') ρ ≡ drop k (drop k' ρ)
drop-drop k k' (⇑ k₁) rewrite +-assoc k k' k₁ = refl
drop-drop zero k' (M • ρ) rewrite drop-0 (drop k' (M • ρ)) = refl
drop-drop (suc k) zero (M • ρ) rewrite +-comm k 0 = refl
drop-drop (suc k) (suc k') (M • ρ)
    with drop-drop (suc k) k' ρ
... | IH rewrite +-comm k (suc k') | +-comm k k' = IH

drop-seq : ∀ k ρ ρ' → drop k (ρ ⨟ ρ') ≡ (drop k ρ ⨟ ρ')
drop-seq k (⇑ k₁) ρ' = sym (drop-drop k k₁ ρ')
drop-seq zero (x • ρ) ρ' = refl
drop-seq (suc k) (x • ρ) ρ' = drop-seq k ρ ρ'

drop-incs : ∀ k ρ → drop k (incs ρ) ≡ incs (drop k ρ)
drop-incs k (⇑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
drop-incs zero (M • ρ) = refl
drop-incs (suc k) (M • ρ) = drop-incs k ρ

drop-exts : ∀ k ρ → drop (suc k) (exts ρ) ≡ incs (drop k ρ)
drop-exts k (⇑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
drop-exts zero (M • ρ) = refl
drop-exts (suc k) (M • ρ) = drop-incs k ρ

incs-seq : ∀ ρ₁ ρ₂ → (incs ρ₁ ⨟ exts ρ₂) ≡ incs (ρ₁ ⨟ ρ₂)
incs-seq (⇑ k) ρ₂ = drop-exts k ρ₂
incs-seq (M • ρ₁) ρ₂ rewrite incs-seq ρ₁ ρ₂
    | commute-subst-rename {M}{ρ₂}{↑ 1} (λ {x} → exts-s ρ₂ x) = refl

exts-seq : ∀ {σ₁ : Subst} {σ₂ : Subst}
         → exts σ₁ ⨟ exts σ₂ ≡ exts (σ₁ ⨟ σ₂)
exts-seq {⇑ k} {σ₂} rewrite exts-cons-shift σ₂ | exts-cons-shift (drop k σ₂)
    | drop-seq k σ₂ (⇑ 1) = refl
exts-seq {M • σ₁} {σ₂} rewrite exts-0 σ₂
    | commute-subst-rename {M}{σ₂}{↑ 1} (λ {x} → exts-s σ₂ x)
    | incs-seq σ₁ σ₂ = refl

sub-sub : ∀{M : ABT} {σ₁ : Subst}{σ₂ : Subst} 
            → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-sub-arg : ∀{n}{A : Arg n} {σ₁ : Subst}{σ₂ : Subst} 
            → subst-arg σ₂ (subst-arg σ₁ A) ≡ subst-arg (σ₁ ⨟ σ₂) A
sub-subs : ∀{S}{Ms : Args S} {σ₁ : Subst}{σ₂ : Subst} 
            → subst-args σ₂ (subst-args σ₁ Ms) ≡ subst-args (σ₁ ⨟ σ₂) Ms
sub-sub {` x} {σ₁} {σ₂} rewrite seq-subst σ₁ σ₂ x = refl
sub-sub {op ⦅ As ⦆} {σ₁} {σ₂} = cong (λ □ → op ⦅ □ ⦆) (sub-subs {Ms = As})
sub-sub-arg {.0} {ast M} {σ₁} {σ₂} = cong ast (sub-sub{M})
sub-sub-arg {.(suc _)} {bind A} {σ₁} {σ₂}
    rewrite sub-sub-arg {A = A}{exts σ₁}{exts σ₂}
    | exts-seq {σ₁} {σ₂} = cong bind refl
sub-subs {.[]} {nil} {σ₁} {σ₂} = refl
sub-subs {.(_ ∷ _)} {cons A Ms} {σ₁} {σ₂} = cong₂ cons sub-sub-arg sub-subs

sub-assoc : ∀ {σ τ θ : Subst}
          → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
sub-assoc {⇑ k} {τ} {θ} = sym (drop-seq k τ θ)
sub-assoc {M • σ} {τ} {θ} rewrite sub-sub {M}{τ}{θ} | sub-assoc {σ}{τ}{θ} = refl

subst-zero-exts-cons : ∀{σ : Subst}{M : ABT}
                     → exts σ ⨟ subst-zero M ≡ M • σ
subst-zero-exts-cons {σ}{M} rewrite exts-cons-shift σ
  | sub-assoc {σ} {⇑ 1} {M • ⇑ 0} | sub-idR σ = refl

subst-commute : ∀{N : ABT}{M : ABT}{σ : Subst }
    → (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {N}{M}{σ} rewrite exts-cons-shift σ
  | sub-sub {N}{(` 0) • (σ ⨟ ⇑ 1)}{⟪ σ ⟫ M • ⇑ 0 }
  | sub-sub {N}{M • ⇑ 0}{σ}
  | sub-assoc {σ}{⇑ 1}{ ⟪ σ ⟫ M • ⇑ 0}
  | sub-idR σ
  | drop-0 σ
  = refl

rename-subst-commute : ∀{N : ABT}{M : ABT}{ρ : Rename }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute{N}{M}{ρ}
    rewrite rename-subst ρ M | rename-subst (ext ρ) N
    | rename-subst ρ (⟪ M • ⇑ 0 ⟫ N)
    | sub-sub {N} {rename→subst (ext ρ)} {⟪ rename→subst ρ ⟫ M • ⇑ 0}
    | sub-sub {N} {M • ⇑ 0} {rename→subst ρ}
    | drop-0 (rename→subst ρ)
    | sym (exts-rename-ext ρ)
    | exts-cons-shift (rename→subst ρ)
    | sub-assoc {rename→subst ρ} {⇑ 1} {⟪ rename→subst ρ ⟫ M • ⇑ 0}
    | sub-idR (rename→subst ρ) = refl

_〔_〕 : ABT → ABT → ABT
_〔_〕 N M = ⟪ exts (subst-zero M) ⟫ N

substitution : ∀{M : ABT}{N : ABT}{L : ABT}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution {M}{N}{L} =
   sym (subst-commute{N = M}{M = N}{σ = subst-zero L})

exts-sub-cons : ∀ σ N V → ⟪ exts σ ⟫ N [ V ] ≡ ⟪ V • σ ⟫ N
exts-sub-cons σ N V
    rewrite sub-sub {N}{exts σ}{subst-zero V}
    | exts-cons-shift σ
    | sub-assoc {σ} {⇑ 1} {V • ⇑ 0}
    | sub-idR σ = refl

{-------------------------------------------------------------------------------
 Extra Things
-------------------------------------------------------------------------------}

exts-ext : ∀ σ τ → ((x : ℕ) → ∣ σ ∣ x ≡ ∣ τ ∣ x)
         → ((x : ℕ) → ∣ exts σ ∣ x ≡ ∣ exts τ ∣ x)
exts-ext σ τ eq 0
    rewrite exts-cons-shift σ | exts-cons-shift τ = refl
exts-ext σ τ eq (suc x)
    rewrite exts-cons-shift σ | exts-cons-shift τ
          | seq-subst σ (⇑ 1) x | seq-subst τ (⇑ 1) x | eq x = refl

subst-extensionality : ∀{M : ABT}{σ τ : Subst}
    → (∀ x → ∣ σ ∣ x ≡ ∣ τ ∣ x)
    → ⟪ σ ⟫ M ≡ ⟪ τ ⟫ M
sub-arg-ext : ∀{n} {A : Arg n} {σ τ : Subst}
         → (∀ x → ∣ σ ∣ x ≡ ∣ τ ∣ x)
         → subst-arg σ A ≡ subst-arg τ A
sub-args-ext : ∀{S} {Ms : Args S} {σ τ : Subst}
         → (∀ x → ∣ σ ∣ x ≡ ∣ τ ∣ x)
         → subst-args σ Ms ≡ subst-args τ Ms

subst-extensionality {` x} {σ} {τ} eq = eq x
subst-extensionality {op ⦅ As ⦆} {σ} {τ} eq = cong (λ □ → op ⦅ □ ⦆) (sub-args-ext eq)

sub-arg-ext {A = ast M} eq = cong ast (subst-extensionality {M} eq)
sub-arg-ext {A = bind A}{σ}{τ} eq = cong bind (sub-arg-ext (exts-ext σ τ eq))

sub-args-ext {Ms = nil} eq = refl
sub-args-ext {Ms = cons A Ms} eq = cong₂ cons (sub-arg-ext eq) (sub-args-ext eq)

