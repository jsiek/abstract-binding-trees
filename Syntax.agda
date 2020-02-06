{-
open import Variables
-}

open import Data.Bool
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Nat.Properties
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (¬_)
{-
import Relation.Binary.HeterogeneousEquality as HEq
open HEq using (_≅_; ≅-to-≡; reflexive)
  renaming (refl to hrefl; cong to hcong)
open HEq.≅-Reasoning renaming (begin_ to hbegin_; _∎ to _□)
-}

module Syntax (Op : Set) (sig : Op → List ℕ) where

Var : Set
Var = ℕ

data Args : (sig : List ℕ) → Set

data AST : Set where

  `_ : ∀ (x : Var) → AST

  _⦅_⦆ : (op : Op) → Args (sig op) → AST


data Arg : (sig : ℕ) → Set where
  ast : AST → Arg 0
  bind : ∀{n} → Arg n → Arg (suc n)

data Args where
  nil : Args []
  cons : ∀{n bs} → Arg n → Args bs → Args (n ∷ bs)

bind-arg : ∀{m} → (n : ℕ) → Arg m → Arg (n + m)
bind-arg  zero A = A
bind-arg {m} (suc n) A
    with bind-arg {suc m} n (bind A)
... | ih rewrite +-suc n m = ih

bind-ast : ∀(n : ℕ) → AST → Arg n
bind-ast n M
    with bind-arg n (ast M)
... | A rewrite +-identityʳ n = A

shift : (k : ℕ) → Var → Var
shift k x = k + x

infixr 6 _·_

data Rename : Set where
  ↑ : ∀ (k : ℕ) → Rename
  _·_ : Var → Rename → Rename

⟦_⟧ :  Rename → Var → Var
⟦ ↑ k ⟧ x = shift k x
⟦ y · ρ ⟧ 0 = y
⟦ y · ρ ⟧ (suc x) = ⟦ ρ ⟧ x

inc : Rename → Rename
inc (↑ k) = ↑ (suc k)
inc (x · ρ) = suc x · inc ρ

ext : Rename → Rename
ext (↑ k) = 0 · ↑ (suc k)
ext (x · ρ) = 0 · suc x · inc ρ

rename : Rename → AST → AST
ren-arg : ∀ {n}→ Rename → Arg n → Arg n
ren-args : ∀ {S} → Rename → Args S → Args S

rename ρ (` x) = ` ⟦ ρ ⟧ x
rename ρ (o ⦅ As ⦆) = o ⦅ ren-args ρ As ⦆

ren-arg ρ (ast M) = ast (rename ρ M)
ren-arg ρ (bind A) = bind (ren-arg (ext ρ) A)

ren-args ρ nil = nil
ren-args ρ (cons A As) = cons (ren-arg ρ A) (ren-args ρ As)

{-

 Substitutions in normal form.

-}

infixr 6 _•_

data Subst : Set  where
  ⇑ : (k : ℕ) → Subst
  _•_ : AST → Subst → Subst

∣_∣ : Subst → Var → AST
∣ ⇑ k ∣ x = ` shift k x
∣ M • σ ∣ 0 = M
∣ M • σ ∣ (suc x) = ∣ σ ∣ x

incs : Subst → Subst
incs (⇑ k) = ⇑ (suc k)
incs (M • σ) =  rename (↑ 1) M • incs σ

exts : Subst → Subst
exts (⇑ k) = ` 0 • ⇑ (suc k)
exts (M • σ) = ` 0 • incs (M • σ)

⟪_⟫ : Subst → AST → AST
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

subst-zero : AST → Subst
subst-zero M = M • ids

_ : ∀{x : Var} → ∣ subst-zero (` x) ∣ 0 ≡ (` x)
_ = refl

_ : ∀{x : Var} → ∣ subst-zero (` x) ∣ 1 ≡ ` 0
_ = refl

_[_] : AST → AST → AST
_[_] N M =  ⟪ subst-zero M ⟫ N

drop : (k : ℕ) → Subst → Subst
drop k (⇑ k') = ⇑ (k + k')
drop zero (M • σ) = M • σ
drop (suc k) (M • σ) = drop k σ

infixr 5 _⨟_

_⨟_ : Subst → Subst → Subst
⇑ k ⨟ τ = drop k τ
(M • σ) ⨟ τ = ⟪ τ ⟫ M • (σ ⨟ τ)

sub-head : ∀{M : AST}{σ : Subst}
         → ⟪ M • σ ⟫ (` 0) ≡ M
sub-head = refl

sub-tail : ∀{M : AST} {σ : Subst}
         → (⇑ 1 ⨟ M • σ) ≡ σ
sub-tail {σ = ⇑ k} = refl
sub-tail {σ = M • σ} = refl

shift-shift : ∀(k k' : ℕ){x : Var}
            → shift (k + k') x ≡ shift k (shift k' x)
shift-shift zero k' = refl
shift-shift (suc k) k' = cong suc (shift-shift k k')

drop-add : ∀{x : Var} (k : ℕ) (σ : Subst)
         → ∣ drop k σ ∣ x ≡ ∣ σ ∣ (shift k x)
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

sub-dist :  ∀ {σ : Subst} {τ : Subst} {M : AST}
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

dropr : (k : ℕ) → Rename → Rename
dropr k (↑ k') = ↑ (k + k')
dropr zero (x · ρ) = x · ρ
dropr (suc k) (x · ρ) = dropr k ρ

_>>=_ : Rename → Rename → Rename
↑ k >>= ρ = dropr k ρ
(x · ρ₁) >>= ρ₂ = ⟦ ρ₂ ⟧ x · (ρ₁ >>= ρ₂)

inc=>>=↑ : ∀ ρ → inc ρ ≡ ρ >>= ↑ 1
inc=>>=↑ (↑ k) rewrite +-comm k 1 = refl
inc=>>=↑ (x · ρ) = cong (_·_ (suc x)) (inc=>>=↑ ρ)

ext-cons-shift : ∀ ρ → ext ρ ≡ (0 · (ρ >>= ↑ 1))
ext-cons-shift (↑ k) rewrite +-comm k 1 = refl
ext-cons-shift (x · ρ) rewrite inc=>>=↑ ρ = refl

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

sub-id' : ∀ {M : AST} {σ : Subst}
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

sub-id : ∀ {M : AST} 
         → ⟪ ids ⟫ M ≡ M
sub-id = sub-id' λ x → refl

rename-id : {M : AST} → rename (↑ 0) M ≡ M
rename-id {M} =
  begin
    rename (↑ 0) M         ≡⟨ rename-subst (↑ 0) M ⟩
    ⟪ ⇑ 0 ⟫ M              ≡⟨ sub-id' (λ x → refl) ⟩
    M                      ∎

sub-idR : ∀ {σ : Subst} {x : Var}
       → ∣ (σ ⨟ ids) ∣ x ≡ ∣ σ ∣ x
sub-idR {σ}{x} =
  begin
    ∣ (σ ⨟ ids) ∣ x        ≡⟨ seq-subst σ ids x ⟩
    ⟪ ids ⟫ (∣ σ ∣ x)      ≡⟨ sub-id ⟩
    ∣ σ ∣ x
  ∎

exts-ext : ∀ σ τ → ((x : ℕ) → ∣ σ ∣ x ≡ ∣ τ ∣ x)
         → ((x : ℕ) → ∣ exts σ ∣ x ≡ ∣ exts τ ∣ x)
exts-ext σ τ eq 0
    rewrite exts-cons-shift σ | exts-cons-shift τ = refl
exts-ext σ τ eq (suc x)
    rewrite exts-cons-shift σ | exts-cons-shift τ
          | seq-subst σ (⇑ 1) x | seq-subst τ (⇑ 1) x | eq x = refl

subst-extensionality : ∀{M : AST}{σ τ : Subst}
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

ext-0 : ∀ ρ → ⟦ ext ρ ⟧ 0 ≡ 0
ext-0 (↑ k) = refl
ext-0 (x · ρ) = refl

inc-suc : ∀ ρ x → ⟦ inc ρ ⟧ x ≡ suc (⟦ ρ ⟧ x)
inc-suc (↑ k) x = refl
inc-suc (x₁ · ρ) zero = refl
inc-suc (x₁ · ρ) (suc x) = inc-suc ρ x

ext-s : ∀ ρ x → ⟦ ext ρ ⟧ (suc x) ≡ suc (⟦ ρ ⟧ x)
ext-s (↑ k) x = refl
ext-s (x₁ · ρ) zero = refl
ext-s (x₁ · ρ) (suc x) = inc-suc ρ x

exts-s : ∀ σ x → ∣ exts σ ∣ (suc x) ≡ rename (↑ 1) (∣ σ ∣ x)
exts-s σ x rewrite exts-cons-shift σ | rename-subst (↑ 1) (∣ σ ∣ x) | seq-subst σ (⇑ 1) x = refl

dropr-add : ∀{x : Var} (k : ℕ) (σ : Rename)
         → ⟦ dropr k σ ⟧ x ≡ ⟦ σ ⟧ (k + x)
dropr-add {x} k (↑ k') rewrite +-comm k k' | +-assoc k' k x = refl
dropr-add {x} zero (y · σ) = refl
dropr-add {x} (suc k) (y · σ) = dropr-add k σ

seq-rename : ∀ ρ₁ ρ₂ x → ⟦ ρ₁ >>= ρ₂ ⟧ x ≡ ⟦ ρ₂ ⟧ (⟦ ρ₁ ⟧ x)
seq-rename (↑ k) ρ₂ x = dropr-add k ρ₂
seq-rename (x₁ · ρ₁) ρ₂ zero = refl
seq-rename (x₁ · ρ₁) ρ₂ (suc x) = seq-rename ρ₁ ρ₂ x

dropr-seq : ∀ k ρ → dropr k (ρ >>= ↑ 1) ≡ (dropr k ρ >>= ↑ 1)
dropr-seq k (↑ k₁) rewrite +-assoc k k₁ 1 = refl
dropr-seq zero (x · ρ) = refl
dropr-seq (suc k) (x · ρ) = dropr-seq k ρ

dropr-0 : ∀ ρ → dropr 0 ρ ≡ ρ
dropr-0 (↑ k) = refl
dropr-0 (x · ρ) = refl

dropr-inc : ∀ k ρ → dropr k (inc ρ) ≡ inc (dropr k ρ)
dropr-inc k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
dropr-inc zero (x · ρ) = refl
dropr-inc (suc k) (x · ρ) = dropr-inc k ρ

dropr-ext : ∀ k ρ → dropr (suc k) (ext ρ) ≡ inc (dropr k ρ)
dropr-ext k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
dropr-ext zero (x · ρ) = refl
dropr-ext (suc k) (x · ρ) = dropr-inc k ρ

inc-seq : ∀ ρ₁ ρ₂ → (inc ρ₁ >>= ext ρ₂) ≡ inc (ρ₁ >>= ρ₂)
inc-seq (↑ k) ρ₂ = dropr-ext k ρ₂
inc-seq (x · ρ₁) ρ₂ rewrite inc-seq ρ₁ ρ₂ | ext-s ρ₂ x = refl

compose-ext : ∀{ρ₁ ρ₂ : Rename}
            → ((ext ρ₁) >>= (ext ρ₂)) ≡ ext (ρ₁ >>= ρ₂)
compose-ext {↑ k} {ρ₂}
    rewrite ext-0 ρ₂ | ext-cons-shift (dropr k ρ₂) | ext-cons-shift ρ₂ =
    cong (λ □ → 0 · □) (dropr-seq k ρ₂)
compose-ext {x · ρ₁} {ρ₂} rewrite ext-0 ρ₂ | ext-s ρ₂ x | inc-seq ρ₁ ρ₂ = refl

compose-rename : ∀{M : AST}{ρ₁ ρ₂ : Rename}
  → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ >>= ρ₂) M
compose-rename-arg : ∀{n}{A : Arg n}{ρ₁ ρ₂ : Rename}
  → ren-arg ρ₂ (ren-arg ρ₁ A) ≡ ren-arg (ρ₁ >>= ρ₂) A
compose-rename-args : ∀{S}{As : Args S}{ρ₁ ρ₂ : Rename}
  → ren-args ρ₂ (ren-args ρ₁ As) ≡ ren-args (ρ₁ >>= ρ₂) As
compose-rename {` x} {ρ₁} {ρ₂} = cong `_ (sym (seq-rename ρ₁ ρ₂ x))
compose-rename {op ⦅ As ⦆} {ρ₁} {ρ₂} = cong (λ □ → op ⦅ □ ⦆) compose-rename-args
compose-rename-arg {.0} {ast M} {ρ₁} {ρ₂} = cong ast compose-rename
compose-rename-arg {.(suc _)} {bind A} {ρ₁} {ρ₂} rewrite sym (compose-ext {ρ₁}{ρ₂}) = cong bind compose-rename-arg
compose-rename-args {.[]} {nil} {ρ₁} {ρ₂} = refl
compose-rename-args {.(_ ∷ _)} {cons x As} {ρ₁} {ρ₂} = cong₂ cons compose-rename-arg compose-rename-args

commute-subst-rename : ∀{M : AST}{σ : Subst}
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
commute-subst-rename {op ⦅ As ⦆} r = cong (λ □ → op ⦅ □ ⦆) (commute-subst-renames r)
commute-subst-rename-arg {.0} {ast M} r = cong ast (commute-subst-rename {M} r)
commute-subst-rename-arg {.(suc _)} {bind A}{σ}{ρ} r = cong bind (commute-subst-rename-arg G)
   where
   G : {x : Var} → ∣ exts (exts σ) ∣ (⟦ ext ρ ⟧ x) ≡ rename (ext ρ) (∣ exts σ ∣ x)
   G {zero} rewrite ext-0 ρ | exts-cons-shift σ | ext-0 ρ = refl
   G {suc x} rewrite ext-s ρ x | exts-cons-shift (exts σ) | seq-subst (exts σ) (⇑ 1) (⟦ ρ ⟧ x) | r {x}
      | exts-cons-shift σ | seq-subst σ (⇑ 1) x | sym (rename-subst (↑ 1) (rename ρ (∣ σ ∣ x)))
      | sym (rename-subst (↑ 1) (∣ σ ∣ x)) | compose-rename {∣ σ ∣ x} {ρ} {↑ 1}
      | compose-rename {∣ σ ∣ x} {↑ 1} {ext ρ} | dropr-ext 0 ρ | sym (dropr-inc 0 ρ) | dropr-0 (inc ρ)
      | inc=>>=↑ ρ = refl

commute-subst-renames {.[]} {nil} r = refl
commute-subst-renames {.(_ ∷ _)} {cons A As} r = cong₂ cons (commute-subst-rename-arg r) (commute-subst-renames r)

exts-seq-x : ∀ {σ₁ : Subst} {σ₂ : Subst}
         → ∀ x → ∣ exts σ₁ ⨟ exts σ₂ ∣ x ≡ ∣ exts (σ₁ ⨟ σ₂) ∣ x
exts-seq-x {σ₁} {σ₂} zero rewrite exts-cons-shift σ₁ | exts-cons-shift σ₂ | exts-cons-shift (σ₁ ⨟ σ₂) = refl
exts-seq-x {σ₁} {σ₂} (suc x) rewrite seq-subst (exts σ₁) (exts σ₂) (suc x) | exts-s σ₁ x
    | exts-s (σ₁ ⨟ σ₂) x | commute-subst-rename {(∣ σ₁ ∣ x)} {σ₂} {↑ 1} (λ {x} → exts-s σ₂ x)
    | seq-subst σ₁ σ₂ x = refl

sub-sub : ∀{M : AST} {σ₁ : Subst}{σ₂ : Subst} 
            → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-sub {M}{σ₁}{σ₂} = begin
    ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M)     ≡⟨ {!!} ⟩
    ⟪ σ₁ ⨟ σ₂ ⟫ M
  ∎

{-

exts : ∀ {Γ Δ}
   → Subst Γ Δ
     ----------------------
   → Subst (suc Γ) (suc Δ)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

⟪_⟫ : ∀ {Γ Δ}
  → Subst Γ Δ
    -------------
  → AST Γ → AST Δ
subst-arg : ∀ {Γ Δ n}
  → Subst Γ Δ
    -----------------
  → Arg Γ n → Arg Δ n
substs : ∀ {Γ Δ S}
  → Subst Γ Δ
    -------------------
  → Args Γ S → Args Δ S

⟪ σ ⟫ (` x)          =  σ x
⟪ σ ⟫ (o ⦅ Ms ⦆)     =  o ⦅ substs σ Ms ⦆
subst-arg σ (ast M)  = ast (⟪ σ ⟫ M)
subst-arg σ (bind M) = bind (subst-arg (exts σ) M)
substs σ nil         = nil
substs σ (cons M Ms) = cons (subst-arg σ M) (substs σ Ms)

subst-zero : ∀ {Γ} → (AST Γ) → Var (suc Γ) → (AST Γ)
subst-zero M Z      = M
subst-zero M (S x)  = ` x

_[_] : ∀ {Γ}
   → AST (suc Γ)
   → AST Γ
     ---------
   → AST Γ
_[_] N M =  ⟪ subst-zero M ⟫ N

ids : ∀{Γ} → Subst Γ Γ
ids {Γ} x = ` x

↑ : ∀{Γ} → Subst Γ (suc Γ)
↑ x = ` (S x)

infixr 6 _•_
_•_ : ∀{Γ Δ} → (AST Δ) → Subst Γ Δ → Subst (suc Γ) Δ
(M • σ) Z = M
(M • σ) (S x) = σ x


infixr 5 _⨟_
_⨟_ : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
σ ⨟ τ = ⟪ τ ⟫ ∘ σ


ren : ∀{Γ Δ} → Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ


sub-head : ∀ {Γ Δ} {M : AST Δ}{σ : Subst Γ Δ}
         → ⟪ M • σ ⟫ (` Z) ≡ M
sub-head = refl


sub-tail : ∀{Γ Δ} {M : AST Δ} {σ : Subst Γ Δ}
         → (↑ ⨟ M • σ) ≡ σ
sub-tail = extensionality λ x → refl

sub-η : ∀{Γ Δ} {σ : Subst (suc Γ) Δ} 
      → (⟪ σ ⟫ (` Z) • (↑ ⨟ σ)) ≡ σ
sub-η {Γ}{Δ}{σ} = extensionality λ x → lemma
   where 
   lemma : ∀ {x} → ((⟪ σ ⟫ (` Z)) • (↑ ⨟ σ)) x ≡ σ x
   lemma {x = Z} = refl
   lemma {x = S x} = refl


Z-shift : ∀{Γ}
        → ((` Z) • ↑) ≡ ids
Z-shift {Γ} = extensionality lemma 
   where
   lemma : (x : Var (suc Γ)) → ((` Z) • ↑) x ≡ ids x
   lemma Z = refl
   lemma (S y) = refl

sub-idL : ∀{Γ Δ} {σ : Subst Γ Δ}
       → ids ⨟ σ ≡ σ
sub-idL = extensionality λ x → refl

sub-dist :  ∀{Γ Δ Σ} {σ : Subst Γ Δ} {τ : Subst Δ Σ} {M : AST Δ}
         → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
sub-dist {Γ}{Δ}{Σ}{σ}{τ}{M} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Var (suc Γ)} → ((M • σ) ⨟ τ) x ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ)) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

sub-op : ∀{Γ Δ} {σ : Subst Γ Δ} {o : Op}{Ms : Args Γ (sig o)}
        → ⟪ σ ⟫ (o ⦅ Ms ⦆)  ≡ o ⦅ substs σ Ms ⦆
sub-op = refl        


ren-ext : ∀ {Γ Δ} {ρ : Rename Γ Δ}
        → ren (ext ρ) ≡ exts (ren ρ)
ren-ext {Γ}{Δ}{ρ} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Var (suc Γ)} → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

rename-subst-ren : ∀ {Γ Δ} {ρ : Rename Γ Δ}{M : AST Γ}
                 → rename ρ M ≡ ⟪ ren ρ ⟫ M
renames-subst-ren : ∀ {Γ Δ} {ρ : Rename Γ Δ}{S}{Ms : Args Γ S}
                 → renames ρ Ms ≡ substs (ren ρ) Ms
rename-arg-subst-ren : ∀ {Γ Δ} {ρ : Rename Γ Δ}{n}{A : Arg Γ n}
                 → rename-arg ρ A ≡ subst-arg (ren ρ) A
                 
rename-subst-ren {M = ` x} = refl
rename-subst-ren{Γ}{Δ}{ρ}{o ⦅ Ms ⦆} =
  cong (_⦅_⦆ o) (renames-subst-ren {Ms = Ms})
  
renames-subst-ren {Ms = nil} = refl
renames-subst-ren {ρ = ρ}{Ms = cons M Ms} =
  cong₂ cons (rename-arg-subst-ren{A = M}) (renames-subst-ren{Ms = Ms})

rename-arg-subst-ren {ρ = ρ} {0} {ast M} = cong ast (rename-subst-ren{ρ = ρ}{M})
rename-arg-subst-ren {Γ}{Δ}{ρ} {suc n} {bind A} =
  let ih = rename-arg-subst-ren {ρ = ext ρ}{n}{A} in
  begin
      bind (rename-arg (ext ρ) A)
    ≡⟨ cong bind ih ⟩
      bind (subst-arg (ren (ext ρ)) A)
    ≡⟨ cong bind (cong₂ subst-arg ren-ext refl) ⟩
      bind (subst-arg (exts (ren ρ)) A)
  ∎

ren-shift : ∀{Γ}
          → ren S_ ≡ ↑ 
ren-shift {Γ} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Var Γ} → ren (S_) x ≡ ↑ x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

rename-shift : ∀{Γ} {M : AST Γ}
             → rename (S_) M ≡ ⟪ ↑ ⟫ M
rename-shift{Γ}{M} =
  begin
    rename S_ M
  ≡⟨ rename-subst-ren ⟩
    ⟪ ren S_ ⟫ M
  ≡⟨ cong-app (cong ⟪_⟫ ren-shift) M ⟩
    ⟪ ↑ ⟫ M
  ∎

exts-cons-shift : ∀{Γ Δ} {σ : Subst Γ Δ}
                → exts σ ≡ (` Z • (σ ⨟ ↑))
exts-cons-shift = extensionality λ x → lemma{x = x}
  where
  lemma : ∀{Γ Δ} {σ : Subst Γ Δ} {x : Var (suc Γ)}
                  → exts σ x ≡ (` Z • (σ ⨟ ↑)) x
  lemma {x = Z} = refl
  lemma {x = S y} = rename-subst-ren

ext-cons-Z-shift : ∀{Γ Δ} {ρ : Rename Γ Δ}
                 → ren (ext ρ) ≡ (` Z • (ren ρ ⨟ ↑))
ext-cons-Z-shift {Γ}{Δ}{ρ} =
  begin
    ren (ext ρ)
  ≡⟨ ren-ext ⟩
    exts (ren ρ)
  ≡⟨ exts-cons-shift{σ = ren ρ} ⟩
   ((` Z) • (ren ρ ⨟ ↑))
  ∎

subst-Z-cons-ids : ∀{Γ}{M : AST Γ}
                 → subst-zero M ≡ (M • ids)
subst-Z-cons-ids = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ}{M : AST Γ}{x : Var (suc Γ)}
                      → subst-zero M x ≡ (M • ids) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

exts-ids : ∀{Γ}
         → exts ids ≡ ids
exts-ids {Γ} = extensionality lemma
  where lemma : (x : Var (suc Γ)) → exts ids x ≡ ids x
        lemma Z = refl
        lemma (S x) = refl

sub-id : ∀{Γ} {M : AST Γ}
         → ⟪ ids ⟫ M ≡ M
sub-arg-id : ∀{Γ}{n} {A : Arg Γ n}
         → subst-arg ids A ≡ A
subs-id : ∀{Γ}{S} {Ms : Args Γ S}
         → substs ids Ms ≡ Ms
sub-id {M = ` x} = refl
sub-id {M = o ⦅ Ms ⦆} = cong (_⦅_⦆ o) (subs-id {Ms = Ms})

subs-id {Ms = nil} = refl
subs-id {Ms = cons M Ms} = cong₂ cons sub-arg-id subs-id

sub-arg-id {A = ast M} = cong ast (sub-id{M = M})
sub-arg-id {A = bind A } =
   begin
     bind (subst-arg (exts ids) A)
   ≡⟨ cong bind (cong-app (cong subst-arg exts-ids) A) ⟩
     bind (subst-arg ids A)
   ≡⟨ cong bind sub-arg-id ⟩
     bind A
   ∎

rename-id : ∀ {Γ} {M : AST Γ} 
  → rename (λ x → x) M ≡ M
rename-id {M = M} =
   begin
     rename (λ x → x) M
   ≡⟨ rename-subst-ren  ⟩
     ⟪ ren (λ x → x) ⟫ M
   ≡⟨⟩
     ⟪ ids ⟫ M
   ≡⟨ sub-id  ⟩
     M
   ∎

sub-idR : ∀{Γ Δ} {σ : Subst Γ Δ}
       → (σ ⨟ ids) ≡ σ
sub-idR {Γ}{σ = σ} =
          begin
            σ ⨟ ids
          ≡⟨⟩
            ⟪ ids ⟫ ∘ σ
          ≡⟨ extensionality (λ x → sub-id) ⟩
            σ
          ∎

compose-ext : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ}
            → ((ext ρ) ∘ (ext ρ′)) ≡ ext (ρ ∘ ρ′)
compose-ext = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {x : Var (suc Γ)}
              → ((ext ρ) ∘ (ext ρ′)) x ≡ ext (ρ ∘ ρ′) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

compose-rename : ∀{Γ Δ Σ}{M : AST Γ}{ρ : Rename Δ Σ}{ρ′ : Rename Γ Δ} 
  → rename ρ (rename ρ′ M) ≡ rename (ρ ∘ ρ′) M
compose-renames : ∀{Γ Δ Σ}{S}{Ms : Args Γ S}{ρ : Rename Δ Σ}{ρ′ : Rename Γ Δ} 
  → renames ρ (renames ρ′ Ms) ≡ renames (ρ ∘ ρ′) Ms
compose-rename-arg : ∀{Γ Δ Σ}{n}{A : Arg Γ n}{ρ : Rename Δ Σ}{ρ′ : Rename Γ Δ} 
  → rename-arg ρ (rename-arg ρ′ A) ≡ rename-arg (ρ ∘ ρ′) A
compose-rename {M = ` x} = refl
compose-rename {M = o ⦅ Ms ⦆} = cong (_⦅_⦆ o) (compose-renames {Ms = Ms})

compose-renames {Ms = nil} = refl
compose-renames {Ms = cons M Ms}{ρ}{ρ′} =
   cong₂ cons compose-rename-arg compose-renames

compose-rename-arg {A = ast M} = cong ast compose-rename
compose-rename-arg {A = bind A}{ρ}{ρ′} =
  let ih = compose-rename-arg {A = A}{ext ρ}{ext ρ′} in
  begin
      bind (rename-arg (ext ρ) (rename-arg (ext ρ′) A))
    ≡⟨ cong bind ih ⟩ 
      bind (rename-arg ((ext ρ) ∘ (ext ρ′)) A) 
    ≡⟨ cong bind (cong₂ rename-arg (compose-ext{ρ = ρ}) refl) ⟩ 
      bind (rename-arg (ext (ρ ∘ ρ′)) A)
    ∎

commute-subst-rename : ∀{Γ Δ}{M : AST Γ}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (suc Γ)}
     → (∀{x : Var Γ} → exts σ (ρ x) ≡ rename ρ (σ x))
     → ⟪ exts σ ⟫ (rename ρ M) ≡ rename ρ (⟪ σ ⟫ M)
commute-subst-rename-arg : ∀{Γ Δ}{n}{A : Arg Γ n}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (suc Γ)}
     → (∀{x : Var Γ} → exts σ (ρ x) ≡ rename ρ (σ x))
     → subst-arg (exts σ) (rename-arg ρ A) ≡ rename-arg ρ (subst-arg σ A)
commute-subst-renames : ∀{Γ Δ}{S}{Ms : Args Γ S}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (suc Γ)}
     → (∀{x : Var Γ} → exts σ (ρ x) ≡ rename ρ (σ x))
     → substs (exts σ) (renames ρ Ms) ≡ renames ρ (substs σ Ms)

commute-subst-rename {M = ` x} r = r
commute-subst-rename {M = o ⦅ Ms ⦆} r =
  cong (_⦅_⦆ o) (commute-subst-renames {Ms = Ms} r)

commute-subst-rename-arg {A = ast M} r =
  cong ast (commute-subst-rename {M = M} r)
commute-subst-rename-arg {Γ}{A = bind A}{σ}{ρ} r =
  let ih = commute-subst-rename-arg {A = A}{exts σ}{ρ′} (λ {x} → H{x}) in
  begin
    bind (subst-arg (exts (exts σ)) (rename-arg (ext ρ) A))
  ≡⟨ cong bind ih ⟩ 
    bind (rename-arg (ext ρ) (subst-arg (exts σ) A))
  ∎
  where
  ρ′ : ∀ {Γ} → Rename Γ (suc Γ)
  ρ′ {zero} = λ ()
  ρ′ {suc Γ} = ext ρ
   
  H : ∀ {x} → exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)
  H {Z} = refl
  H {S y} =
     begin
       exts (exts σ) (ext ρ (S y))
     ≡⟨⟩
       rename S_ (exts σ (ρ y)) 
     ≡⟨ cong (rename S_) r ⟩
       rename S_ (rename ρ (σ y))
     ≡⟨ compose-rename ⟩
       rename (S_ ∘ ρ) (σ y)
     ≡⟨⟩
       rename ((ext ρ) ∘ S_) (σ y)
     ≡⟨ sym compose-rename ⟩
       rename (ext ρ) (rename S_ (σ y))
     ≡⟨⟩
       rename (ext ρ) (exts σ (S y))
     ∎

commute-subst-renames {Ms = nil} r = refl
commute-subst-renames {Γ}{Δ}{_}{cons M Ms}{σ}{ρ} r =
  cong₂ cons (commute-subst-rename-arg{A = M} r)
             (commute-subst-renames{Ms = Ms} r)

exts-seq : ∀{Γ Δ Δ′} {σ₁ : Subst Γ Δ} {σ₂ : Subst Δ Δ′}
         → (exts σ₁ ⨟ exts σ₂) ≡ exts (σ₁ ⨟ σ₂)
exts-seq = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ Δ Δ′}{x : Var (suc Γ)} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Δ′}
     → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
  lemma {x = Z} = refl
  lemma {x = S x}{σ₁}{σ₂} =
     begin
       (exts σ₁ ⨟ exts σ₂) (S x)
     ≡⟨⟩
       ⟪ exts σ₂ ⟫ (rename S_ (σ₁ x))
     ≡⟨ commute-subst-rename{M = σ₁ x}{σ = σ₂}{ρ = S_} refl ⟩
       rename S_ (⟪ σ₂ ⟫ (σ₁ x))
     ≡⟨⟩
       rename S_ ((σ₁ ⨟ σ₂) x)
     ∎

sub-sub : ∀{Γ Δ Σ}{M : AST Γ} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ} 
            → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-sub-arg : ∀{Γ Δ Σ}{n}{A : Arg Γ n} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ} 
            → subst-arg σ₂ (subst-arg σ₁ A) ≡ subst-arg (σ₁ ⨟ σ₂) A
sub-subs : ∀{Γ Δ Σ}{S}{Ms : Args Γ S} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ} 
            → substs σ₂ (substs σ₁ Ms) ≡ substs (σ₁ ⨟ σ₂) Ms
sub-sub {M = ` x} = refl
sub-sub {M = op ⦅ Ms ⦆} = cong (op ⦅_⦆) (sub-subs{Ms = Ms})

sub-sub-arg {A = ast M} = cong ast (sub-sub {M = M})
sub-sub-arg {A = bind A}{σ₁}{σ₂} =
  let ih = sub-sub-arg {A = A}{exts σ₁}{exts σ₂} in
  begin
    subst-arg σ₂ (subst-arg σ₁ (bind A))
  ≡⟨⟩
    bind (subst-arg (exts σ₂) (subst-arg (exts σ₁) A))
  ≡⟨ cong bind ih ⟩
    bind (subst-arg (exts σ₁ ⨟ exts σ₂) A)
  ≡⟨ cong bind (cong-app (cong subst-arg exts-seq) A) ⟩
    bind (subst-arg (exts (σ₁ ⨟ σ₂)) A)
  ≡⟨⟩
    subst-arg (σ₁ ⨟ σ₂) (bind A)
  ∎

sub-subs {Ms = nil} = refl
sub-subs {Ms = cons M Ms} = cong₂ cons (sub-sub-arg{A = M}) (sub-subs{Ms = Ms})

rename-subst : ∀{Γ Δ Δ′}{M : AST Γ}{ρ : Rename Γ Δ}{σ : Subst Δ Δ′}
             → ⟪ σ ⟫ (rename ρ M) ≡ ⟪ σ ∘ ρ ⟫ M
rename-subst {Γ}{Δ}{Δ′}{M}{ρ}{σ} =
   begin
     ⟪ σ ⟫ (rename ρ M)
   ≡⟨ cong ⟪ σ ⟫ (rename-subst-ren{M = M}) ⟩
     ⟪ σ ⟫ (⟪ ren ρ ⟫ M)
   ≡⟨ sub-sub{M = M} ⟩
     ⟪ ren ρ ⨟ σ ⟫ M
   ≡⟨⟩
     ⟪ σ ∘ ρ ⟫ M
   ∎

sub-assoc : ∀{Γ Δ Σ Ψ} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
             {θ : Subst Σ Ψ}
          → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
sub-assoc {Γ}{Δ}{Σ}{Ψ}{σ}{τ}{θ} = extensionality λ x → lemma{x = x}
  where
  lemma : ∀ {x : Var Γ} → ((σ ⨟ τ) ⨟ θ) x ≡ (σ ⨟ τ ⨟ θ) x
  lemma {x} =
      begin
        ((σ ⨟ τ) ⨟ θ) x
      ≡⟨⟩
        ⟪ θ ⟫ (⟪ τ ⟫ (σ x))
      ≡⟨ sub-sub{M = σ x} ⟩
        ⟪ τ ⨟ θ ⟫ (σ x)
      ≡⟨⟩
        (σ ⨟ τ ⨟ θ) x
      ∎

subst-zero-exts-cons : ∀{Γ Δ}{σ : Subst Γ Δ}{M : AST Δ}
                     → exts σ ⨟ subst-zero M ≡ M • σ
subst-zero-exts-cons {Γ}{Δ}{σ}{M} =
    begin
      exts σ ⨟ subst-zero M
    ≡⟨ cong₂ _⨟_ exts-cons-shift subst-Z-cons-ids ⟩
      (` Z • (σ ⨟ ↑)) ⨟ (M • ids)
    ≡⟨ sub-dist ⟩
      (⟪ M • ids ⟫ (` Z)) • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong₂ _•_ (sub-head{σ = ids}) refl ⟩
      M • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong₂ _•_ refl (sub-assoc{σ = σ}) ⟩
      M • (σ ⨟ (↑ ⨟ (M • ids)))
    ≡⟨ cong₂ _•_ refl (cong₂ _⨟_ {x = σ} refl (sub-tail{M = M}{σ = ids})) ⟩
      M • (σ ⨟ ids)
    ≡⟨ cong₂ _•_ refl (sub-idR{σ = σ}) ⟩
      M • σ
    ∎

subst-commute : ∀{Γ Δ : ℕ}{N : AST (suc Γ)}{M : AST Γ}{σ : Subst Γ Δ }
    → (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {Γ}{Δ}{N}{M}{σ} =
     begin
       ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ]
     ≡⟨⟩
       ⟪ subst-zero (⟪ σ ⟫ M) ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ cong-app (cong ⟪_⟫ subst-Z-cons-ids) (⟪ exts σ ⟫ N) ⟩
       ⟪ ⟪ σ ⟫ M • ids ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ sub-sub {M = N} ⟩
       ⟪ (exts σ) ⨟ ((⟪ σ ⟫ M) • ids) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (cong₂ _⨟_ exts-cons-shift refl)) N ⟩
       ⟪ (` Z • (σ ⨟ ↑)) ⨟ (⟪ σ ⟫ M • ids) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (sub-dist {M = ` Z})) N ⟩
       ⟪ ⟪ ⟪ σ ⟫ M • ids ⟫ (` Z) • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
     ≡⟨⟩
       ⟪ ⟪ σ ⟫ M • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (cong₂ _•_ refl (sub-assoc{σ = σ}))) N ⟩
       ⟪ ⟪ σ ⟫ M • (σ ⨟ ↑ ⨟ ⟪ σ ⟫ M • ids) ⟫ N
     ≡⟨ refl ⟩
       ⟪ ⟪ σ ⟫ M • (σ ⨟ ids) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (cong₂ _•_ refl (sub-idR{σ = σ}))) N ⟩
       ⟪ ⟪ σ ⟫ M • σ ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (cong₂ _•_ refl (sub-idL{σ = σ}))) N ⟩
       ⟪ ⟪ σ ⟫ M • (ids ⨟ σ) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (sym sub-dist)) N ⟩
       ⟪ M • ids ⨟ σ ⟫ N
     ≡⟨ sym (sub-sub{M = N}) ⟩
       ⟪ σ ⟫ (⟪ M • ids ⟫ N)
     ≡⟨ cong ⟪ σ ⟫ (sym (cong-app (cong ⟪_⟫ subst-Z-cons-ids) N)) ⟩
       ⟪ σ ⟫ (N [ M ])
     ∎

rename-subst-commute : ∀{Γ Δ}{N : AST (suc Γ)}{M : AST Γ}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ}{Δ}{N}{M}{ρ} =
     begin
       (rename (ext ρ) N) [ rename ρ M ]
     ≡⟨ cong-app (cong ⟪_⟫ (cong subst-zero rename-subst-ren)) (rename (ext ρ) N) ⟩
       (rename (ext ρ) N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨ cong ⟪ subst-zero (⟪ ren ρ ⟫ M) ⟫ (rename-subst-ren{M = N}) ⟩
       (⟪ ren (ext ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨  cong ⟪ subst-zero (⟪ ren ρ ⟫ M) ⟫ ( cong-app (cong ⟪_⟫ ren-ext) N) ⟩
       (⟪ exts (ren ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨ subst-commute{N = N} ⟩
       ⟪ ren ρ ⟫ (N [ M ])
     ≡⟨ sym rename-subst-ren ⟩
       rename ρ (N [ M ])
     ∎

_〔_〕 : ∀ {Γ}
        → AST (suc (suc Γ))
        → AST Γ
          ------------
        → AST (suc Γ)
_〔_〕 {Γ} N M = ⟪ exts (subst-zero M) ⟫ N

substitution : ∀{Γ}{M : AST (suc (suc Γ))}{N : AST (suc Γ)}{L : AST Γ}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution{M = M}{N = N}{L = L} =
   sym (subst-commute{N = M}{M = N}{σ = subst-zero L})


data CArgs : (Γ : ℕ) → (Δ : ℕ) → (sig : List ℕ) → Set

data Ctx : ℕ → ℕ → Set where
  CHole : ∀ {Γ} → Ctx Γ Γ
  COp : ∀ {Γ Δ} → (op : Op) → CArgs Γ Δ (sig op) → Ctx Γ Δ

data CArg : (Γ : ℕ) → (Δ : ℕ) → (n : ℕ) → Set where
  CAst : ∀{Γ Δ} → Ctx Γ Δ → CArg Γ Δ 0
  CBind : ∀{Γ Δ}{n} → CArg (suc Γ) (suc Δ) n → CArg (suc Γ) Δ (suc n)

data CArgs where
  tcons : ∀{Γ Δ}{n}{bs bs'} → Arg Δ n → CArgs Γ Δ bs → bs' ≡ (n ∷ bs)
        → CArgs Γ Δ bs'
  ccons : ∀{Γ Δ}{n}{bs bs'} → CArg Γ Δ n → Args Δ bs → bs' ≡ (n ∷ bs)
        → CArgs Γ Δ bs'  

cargs-not-empty : ∀ {Γ Δ} → ¬ CArgs Γ Δ []
cargs-not-empty {Γ} {Δ} (tcons (ast x) Cs ())
cargs-not-empty {Γ} {Δ} (tcons (bind x) Cs ())
cargs-not-empty {Γ} {Δ} (ccons (CAst x) x₁ ())
cargs-not-empty {.(suc _)} {Δ} (ccons (CBind x) x₁ ())

plug : ∀ {Γ Δ} → Ctx Γ Δ → AST Γ → AST Δ
plug-arg : ∀ {Γ Δ n} → CArg Γ Δ n → AST Γ → Arg Δ n
plug-args : ∀ {Γ Δ bs} → CArgs Γ Δ bs → AST Γ → Args Δ bs

plug CHole M = M
plug (COp op args) M = op ⦅ plug-args args M ⦆

plug-arg (CAst C) M = ast (plug C M)
plug-arg (CBind C) M = bind (plug-arg C M)

plug-args (tcons L Cs eq) M rewrite eq =
   cons L (plug-args Cs M)
plug-args (ccons C Ls eq) M rewrite eq =
   cons (plug-arg C M) Ls

-}
