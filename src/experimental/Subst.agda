{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import experimental.ScopedTuple
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Binary.HeterogeneousEquality
    using (_≅_; ≅-to-≡; reflexive)
    renaming (cong to hcong)
open import Size using (Size)
open import Syntax using (Substitution; ↑; _•_; id)
open import Var

module experimental.Subst (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig
open import experimental.Map Op sig
open import experimental.Rename Op sig

Subst : Set
Subst = Substitution ABT

SubstIsMap : Map ABT
SubstIsMap = record { “_” = λ M → M ; var→val = `_ ; shift = rename (↑ 1)
                    ; var→val-suc-shift = refl
                    ; “_”-0 = refl }
open Map SubstIsMap renaming (map-abt to ⟪_⟫; map-arg to ⟪_⟫ₐ) public
⟪_⟫₊ : ∀{s : Size} → Substitution ABT →(bs : Sig)→ Tuple bs (λ _ → Term s)
     → Tuple bs (λ _ → ABT)
⟪_⟫₊ = λ σ bs → map (λ {b} → ⟪ σ ⟫ₐ b) {bs}
open Map.S SubstIsMap renaming (⧼_⧽ to ⟦_⟧; g-ext to exts) public
open Map.S SubstIsMap renaming (g-inc to incs;
    g-drop to drops; g-drop-inc to drops-incs; g-drop-add to drop-add)
open ComposeMaps SubstIsMap SubstIsMap ⟪_⟫ using (_⨟_) public

subst-zero : ABT → Subst
subst-zero M = M • id

private {- making sure the following equations are all refl's -}
  sub-head : ∀ M σ → ⟦ M • σ ⟧ 0 ≡ M
  sub-head M σ = refl

  sub-tail : ∀ M σ → (↑ 1 ⨟ M • σ) ≡ σ
  sub-tail M σ = refl

  sub-suc : ∀ M σ x → ⟪ M • σ ⟫ (` suc x) ≡ ⟪ σ ⟫ (` x)
  sub-suc M σ x = refl

  shift-eq : ∀ x k → ⟪ ↑ k ⟫ (` x) ≡ ` (k + x)
  shift-eq x k = refl

  sub-idL : (σ : Subst) → id ⨟ σ ≡ σ
  sub-idL σ = refl

  sub-dist :  ∀ {σ : Subst} {τ : Subst} {M : ABT}
           → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
  sub-dist = refl

  sub-op : ∀ {s : Size}{σ}{op}{args}
     → ⟪ σ ⟫ (op ⦅ args ⦆) ≡ op ⦅ ⟪ σ ⟫₊ (sig op) args  ⦆
  sub-op = refl

  sub-nil : ∀ {σ} → ⟪ σ ⟫₊ [] tt ≡ tt
  sub-nil = refl

  sub-cons : ∀{σ b bs arg args}
    → ⟪ σ ⟫₊ (b ∷ bs) ⟨ arg , args ⟩ ≡ ⟨ ⟪ σ ⟫ₐ b arg , ⟪ σ ⟫₊ bs args ⟩
  sub-cons = refl


sub-η : ∀ (σ : Subst) (x : Var)  →  ⟦ ⟪ σ ⟫ (` 0) • (↑ 1 ⨟ σ) ⟧ x ≡ ⟦ σ ⟧ x
sub-η σ 0 = refl
sub-η σ (suc x) = drop-add 1 σ
{-# REWRITE sub-η #-}

rename→subst : Rename → Subst
rename→subst (↑ k) = ↑ k 
rename→subst (x • ρ) = ` x • rename→subst ρ

private
  incs-rename-inc : ∀ ρ → incs (rename→subst ρ) ≡ rename→subst (inc ρ)
  incs-rename-inc (↑ k) = refl
  incs-rename-inc (x • ρ) = cong (_•_ (` suc x)) (incs-rename-inc ρ)

exts-rename-ext : ∀ ρ → exts (rename→subst ρ) ≡ rename→subst (ext ρ)
exts-rename-ext (↑ k) = refl
exts-rename-ext (x • ρ) =
    cong (λ □ → (` 0) • (` suc x) • □) (incs-rename-inc ρ)

rename-subst-interp : ∀ ρ x → (` ⦉ ρ ⦊ x) ≡ ⟦ rename→subst ρ ⟧ x
rename-subst-interp (↑ k) x = refl
rename-subst-interp (y • ρ) zero = refl
rename-subst-interp (y • ρ) (suc x) = rename-subst-interp ρ x

rename-subst : ∀ {s : Size} ρ (M : Term s)
   → rename ρ M ≡ ⟪ rename→subst ρ ⟫ M
rename-subst {s} ρ M = MapCong.map-cong-abt MRS refl M
  where
  MRS : MapCong RenameIsMap SubstIsMap
  MRS = record { _≈_ = λ ρ σ → σ ≡ rename→subst ρ
              ; var = λ { {ρ} x refl → rename-subst-interp ρ x }
              ; ext≈ = λ { {ρ} refl → exts-rename-ext ρ } }

incs=⨟↑ : ∀ σ → incs σ ≡ σ ⨟ ↑ 1
incs=⨟↑ (↑ k) rewrite +-comm k 1 = refl
incs=⨟↑ (M • σ) = cong₂ _•_ (rename-subst (↑ 1) M) (incs=⨟↑ σ)

exts-cons-shift : ∀ σ → exts σ ≡ (` 0 • (σ ⨟ ↑ 1))
exts-cons-shift σ rewrite incs=⨟↑ σ = refl

seq-subst : ∀ σ τ x → ⟦ σ ⨟ τ ⟧ x ≡ ⟪ τ ⟫ (⟦ σ ⟧ x)
seq-subst (↑ k) τ x = drop-add k τ
seq-subst (M • σ) τ zero = refl
seq-subst (M • σ) τ (suc x) = seq-subst σ τ x


data _⩭_ : {s : Size} → Term s → {t : Size} → Term t → Set
⟨_⟩_⩭_ : ∀{s t : Size} → (bs : Sig) → Tuple bs (λ _ → Term s)
    → Tuple bs (λ _ → Term t) → Set

data _⩭_ where
  var⩭ : ∀{i j : Size}{k l : Var} → k ≡ l → `_ {s = i} k ⩭ `_ {s = j} l
  node⩭ : ∀{i j : Size}{op}{args args'}
         → ⟨ sig op ⟩ args ⩭ args'
         → _⦅_⦆ {s = i} op args ⩭ _⦅_⦆ {s = j} op args'

⟨ bs ⟩ xs ⩭ ys = zip (λ M N → M ⩭ N) {bs} xs ys

⩭→≡ : ∀ {s : Size}{M N : Term s} → M ⩭ N → M ≡ N
⟨_⟩⩭→≡ : ∀{s : Size} → (bs : Sig) → {xs ys : Tuple bs (λ _ → Term s)}
    → ⟨ bs ⟩ xs ⩭ ys → xs ≡ ys

⩭→≡ {.(Size.↑ _)} {.(` _)} {.(` _)} (var⩭ refl) = refl
⩭→≡ {.(Size.↑ _)} {.(_ ⦅ _ ⦆)} {.(_ ⦅ _ ⦆)} (node⩭ {op = op} args⩭) =
  cong (_⦅_⦆ op) (⟨ sig op ⟩⩭→≡ args⩭)

⟨_⟩⩭→≡ {s} [] {tt} {tt} tt = refl
⟨_⟩⩭→≡ {s} (b ∷ bs) {⟨ x , xs ⟩} {⟨ y , ys ⟩} ⟨ x=y , xs=ys ⟩
    rewrite ⩭→≡ x=y | ⟨ bs ⟩⩭→≡ xs=ys = refl

data Shift : ℕ → Subst → Set where
  shift-up : ∀{k} → Shift k (↑ k)
  shift-• : ∀{k σ} → Shift (suc k) σ → Shift k ((` k) • σ)

incs-shift : ∀ {k σ} → Shift k σ → Shift (suc k) (incs σ)
incs-shift shift-up = shift-up
incs-shift (shift-• kσ) = shift-• (incs-shift kσ)

exts-pres-shift-0 : ∀ σ → Shift 0 σ → Shift 0 (exts σ)
exts-pres-shift-0 (↑ .0) shift-up = shift-• shift-up
exts-pres-shift-0 (.(` 0) • σ) (shift-• σ0) =
    shift-• (shift-• (incs-shift σ0))

sub-shift-var : ∀ {σ}{k} (x : Var) → Shift k σ → ⟦ σ ⟧ x ≡ ` (k + x)
sub-shift-var {.(↑ k)}{k} x shift-up = refl
sub-shift-var {.((` k) • _)}{k} zero (shift-• σk)
    rewrite +-comm k 0 = refl
sub-shift-var {(` k) • σ}{k} (suc x) (shift-• σk) rewrite +-suc k x =
    sub-shift-var {σ}{suc k} x σk

sub-shift0 : ∀ {s}{σ} (M : Term s) → Shift 0 σ → ⟪ σ ⟫ M ⩭ M
sub-shift0-arg  : ∀{s}{σ} → (b : ℕ) → (arg : Term s) → Shift 0 σ
   → ⟪ σ ⟫ₐ b arg ⩭ arg
sub-shift0-args  : ∀{s}{σ} → (bs : Sig) → (args : Tuple bs (λ _ → Term s))
   → Shift 0 σ → ⟨ bs ⟩ map (λ {b} → ⟪ σ ⟫ₐ b) args ⩭ args

sub-shift0 {s}{σ}(` x) σ0 rewrite sub-shift-var {σ}{0} x σ0 = var⩭ refl
sub-shift0 (_⦅_⦆ op args) σ0 = node⩭ (sub-shift0-args (sig op) args σ0)
sub-shift0-arg {s} zero arg σ0 = sub-shift0 arg σ0
sub-shift0-arg {s} (suc b) arg σ0 =
    sub-shift0-arg b arg (shift-• (incs-shift σ0))
sub-shift0-args {s} [] tt σ0 = tt
sub-shift0-args {s} (b ∷ bs) ⟨ arg , args ⟩ σ0 =
  ⟨ sub-shift0-arg b arg σ0 , (sub-shift0-args bs args σ0) ⟩

sub-id : ∀ (M : ABT) → ⟪ id ⟫ M ≡ M
sub-id M = ⩭→≡ (sub-shift0 M (shift-up {0}))
