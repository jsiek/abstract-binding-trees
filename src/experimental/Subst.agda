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
open import GenericSubstitution renaming (g-drop to drop)
open import Var

module experimental.Subst (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig
open import experimental.Map Op sig
open import experimental.Rename Op sig

Subst : Set
Subst = Substitution ABT

SubstIsSubstable : Substable ABT
SubstIsSubstable = record { var→val = `_ ; shift = rename (↑ 1)
    ; var→val-suc-shift = λ {x} → refl }

SubstIsMap : Map ABT
SubstIsMap = record { “_” = λ M → M ; S = SubstIsSubstable }
open Map SubstIsMap renaming (map-abt to ⟪_⟫; map-arg to ⟪_⟫ₐ) public
⟪_⟫₊ : ∀{s : Size} → Substitution ABT →(bs : Sig)→ Tuple bs (λ _ → Term s)
     → Tuple bs (λ _ → ABT)
⟪_⟫₊ = λ σ bs → map (λ {b} → ⟪ σ ⟫ₐ b) {bs}
open GenericSubst (Map.S SubstIsMap) using ()
    renaming (⧼_⧽ to ⟦_⟧; g-ext to exts) public
open GenericSubst (Map.S SubstIsMap) using (Shift; shift-up; shift-•)
    renaming (g-inc to incs; g-inc-shift to incs-rename;
    g-drop-inc to drops-incs; g-drop-add to drop-add;
    g-Shift-var to sub-shift-var; 
    g-inc-Shift to incs-Shift; g-ext-cong to exts-cong)
open ComposeMaps SubstIsMap SubstIsMap ⟪_⟫ (λ x → x)
    using (_⨟_) public

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

rename-subst : ∀ {s : Size} ρ (M : Term s)
   → rename ρ M ≡ ⟪ rename→subst ρ ⟫ M
rename-subst {s} ρ M = MapCong≊.map-cong-abt MRS (ρ≊ ρ) M
  where
  MRS = record { var→val-quote = λ x → refl ; shift-quote = λ { refl → refl } }
  open MapCong≊.R MRS
  ρ≊ : ∀ ρ → ρ ≊ rename→subst ρ
  ρ≊ (↑ k) = r-up
  ρ≊ (x • ρ) = r-cons refl (ρ≊ ρ)

{- the following two may not be necessary -}
private
  incs-rename-inc : ∀ ρ → incs (rename→subst ρ) ≡ rename→subst (inc ρ)
  incs-rename-inc (↑ k) = refl
  incs-rename-inc (x • ρ) = cong (_•_ (` suc x)) (incs-rename-inc ρ)

exts-rename-ext : ∀ ρ → exts (rename→subst ρ) ≡ rename→subst (ext ρ)
exts-rename-ext (↑ k) = refl
exts-rename-ext (x • ρ) =
    cong (λ □ → (` 0) • (` suc x) • □) (incs-rename-inc ρ)

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

open ComposeMaps SubstIsMap RenameIsMap rename `_
   renaming (_⨟_ to _⨟ˢᵣ_)

QSR : Quotable SubstIsMap RenameIsMap SubstIsMap
QSR = record { ⌈_⌉ = rename ; val₂₃ = `_ ; quote-map = λ σ₂ v₁ → refl
        ; var→val₂₃ = λ x₁ → refl ; quote-val₂₃ = λ v₂ → refl
        ; map₂-var→val₁ = λ x₁ σ₂ → refl ; val₂₃-shift = λ v₂ → refl }
          
seq-sub-ren : ∀ x σ ρ  →  rename ρ (⟦ σ ⟧ x) ≡ ⟦ σ ⨟ˢᵣ ρ ⟧ x
seq-sub-ren x σ ρ = sym (Quotable.compose-sub QSR σ ρ x)

compose-incs-ext : ∀ σ ρ → (incs σ ⨟ˢᵣ ext ρ) ≡ incs (σ ⨟ˢᵣ ρ)
compose-incs-ext (↑ k) ρ
    rewrite dropr-inc k ρ | Quotable.g-map-sub-inc QSR (drop k ρ) = refl
compose-incs-ext (M • σ) ρ = cong₂ _•_ (commute-↑1 ρ M) (compose-incs-ext σ ρ)

compose-exts-ext : ∀ σ ρ → (exts σ) ⨟ˢᵣ (ext ρ) ≡ exts (σ ⨟ˢᵣ ρ)
compose-exts-ext σ ρ rewrite compose-incs-ext σ ρ = refl

compose-ren-sub : ∀ ρ σ M → rename ρ (⟪ σ ⟫ M) ≡ ⟪ σ ⨟ˢᵣ ρ ⟫ M
compose-ren-sub ρ σ M = FusableMap.fusion FSR {_}{σ}{ρ} M
  where
  FSR : FusableMap SubstIsMap RenameIsMap SubstIsMap
  FSR = record { Q = QSR ; var = seq-sub-ren ; compose-ext = compose-exts-ext }

{-
commute-subst-shift : ∀{s}{σ : Subst} (M : Term s)
   → ⟪ exts σ ⟫ (rename (↑ 1) M) ≡ rename (↑ 1) (⟪ σ ⟫ M)
commute-subst-shift {s}{σ} M = comm-sub-ren {s}{M}{σ}{↑ 1} (exts-suc-rename σ)
  where
  comm-sub-ren : ∀{s}{M : Term s}{σ}{ρ}
       → (∀ x → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
       → ⟪ exts σ ⟫ (rename ρ M) ≡ rename ρ (⟪ σ ⟫ M)
  comm-sub-ren-arg : ∀{s}{b}{A : Term s}{σ}{ρ}
       → (∀ x → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
       → ⟪ exts σ ⟫ₐ b (ren-arg ρ b A) ≡ ren-arg ρ b (⟪ σ ⟫ₐ b A)
  comm-sub-ren {_} {` x} {σ} {ρ} var = var x
  comm-sub-ren {_} {_⦅_⦆ {s} op args} {σ} {ρ} var = {!!}
  comm-sub-ren-arg {s} {zero} {A} {σ} {ρ} var = comm-sub-ren {s}{A} var
  comm-sub-ren-arg {s} {suc b} {A} {σ} {ρ} var =
    comm-sub-ren-arg {s}{b} ext²
    where
    ext² : ∀ x → ⟦ exts (exts σ) ⟧ (⦉ ext ρ ⦊ x) ≡ rename (ext ρ) (⟦ exts σ ⟧ x)
    ext² zero = refl
    ext² (suc x) = {!!}
-}
