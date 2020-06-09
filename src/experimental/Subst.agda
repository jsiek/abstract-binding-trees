{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import experimental.ScopedTuple using (Sig; Tuple; map; tuple-pred)
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
open Map.S SubstIsMap using () renaming (⧼_⧽ to ⟦_⟧; g-ext to exts) public
open Map.S SubstIsMap using (Shift; shift-up; shift-•) renaming (g-inc to incs;
    g-drop to drops; g-drop-inc to drops-incs; g-drop-add to drop-add;
    g-Shift-var to sub-shift-var; g-inc-shift to incs-rename;
    g-inc-Shift to incs-Shift)
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

private
  sub-shift0 : ∀ {s}{σ} (M : Term s) → Shift 0 σ → ⟪ σ ⟫ M ⩭ M
  ss0-arg  : ∀{s}{σ} → Shift 0 σ → (b : ℕ) → (arg : Term s) 
     → ⟪ σ ⟫ₐ b arg ⩭ arg
  sub-shift0 {s}{σ}(` x) σ0 rewrite sub-shift-var {σ}{0} x σ0 = var⩭ refl
  sub-shift0 {_}{σ}(_⦅_⦆ {s} op args) σ0 =
      node⩭ (tuple-pred P× (ss0-arg σ0) args tt ⟨_,_⟩)
      where P× = (λ bs args → ⟨ bs ⟩ map (λ {b} → ⟪ σ ⟫ₐ b) args ⩭ args)
  ss0-arg {s} σ0 zero arg = sub-shift0 arg σ0
  ss0-arg {s} σ0 (suc b) arg = ss0-arg (shift-• (incs-Shift σ0) refl) b arg

sub-id : ∀ (M : ABT) → ⟪ id ⟫ M ≡ M
sub-id M = ⩭→≡ (sub-shift0 M (shift-up {0}))
{-# REWRITE sub-id #-}

rename-id : {M : ABT} → rename (↑ 0) M ≡ M
rename-id {M} = rename-subst (↑ 0) M
{-# REWRITE rename-id #-}

sub-idR : ∀ σ → σ ⨟ id ≡ σ 
sub-idR (↑ k) rewrite +-comm k 0 = refl
sub-idR (M • σ) rewrite sub-idR σ = refl
{-# REWRITE sub-idR #-}

private
  exts-0 : ∀ σ → ⟦ exts σ ⟧ 0 ≡ ` 0
  exts-0 σ = refl

exts-suc' : ∀ σ x → ⟦ exts σ ⟧ (suc x) ≡ rename (↑ 1) (⟦ σ ⟧ x)
exts-suc' σ x rewrite incs-rename σ x = refl

exts-suc-rename : ∀ σ x → ⟦ exts σ ⟧ (suc x) ≡ rename (↑ 1) (⟪ σ ⟫ (` x))
exts-suc-rename σ x rewrite incs-rename σ x = refl


