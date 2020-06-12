open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n; _≤?_)
open import Data.Nat.Properties using (+-comm; +-suc; ≤-pred)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)

module Syntax where

open GenericSubstitution
    using (GSubst; ↑; _•_; Substable; id; drop; map-sub; map-sub-id; drop-0)
    public
open import Var public

{----------------------------------------------------------------------------
                             Renaming
 ---------------------------------------------------------------------------}

Rename : Set
Rename = GSubst Var

RenameIsSubstable : Substable Var
RenameIsSubstable = record { var→val = λ x → x ; shift = suc
    ; var→val-suc-shift = λ {x} → refl }

open GenericSubstitution.GenericSubst RenameIsSubstable
    using () renaming (⧼_⧽ to ⦉_⦊; g-ext to ext; g-Z-shift to Z-shiftr) public
open GenericSubstitution.GenericSubst RenameIsSubstable
    using ()
    renaming (g-inc to inc; g-ext-cong to ext-cong; g-inc-shift to inc-suc;
              g-drop-add to dropr-add; g-drop-inc to dropr-inc;
              g-drop-ext to dropr-ext; g-ext-def to ext-def)

ext-0 : ∀ ρ → ⦉ ext ρ ⦊ 0 ≡ 0
ext-0 ρ rewrite ext-def ρ = refl

ext-suc : ∀ ρ x → ⦉ ext ρ ⦊ (suc x) ≡ suc (⦉ ρ ⦊ x)
ext-suc ρ x rewrite ext-def ρ | inc-suc ρ x = refl

module OpSig (Op : Set) (sig : Op → List ℕ)  where

  open import AbstractBindingTree Op sig public

  open import Map Op sig
  RenameIsMap : Map Var 
  RenameIsMap = record { “_” = `_ ; S = RenameIsSubstable }
  open Map RenameIsMap renaming (map-abt to rename; map-arg to ren-arg;
     map-args to ren-args) public
  open ComposeMaps RenameIsMap RenameIsMap ⦉_⦊ (λ x → x)
      using () renaming (_⨟_ to _⨟ᵣ_; up-seq to up-seqᵣ;
      cons-seq to cons-seqᵣ) public

  ren-up-seq : ∀ k ρ → ↑ k ⨟ᵣ ρ ≡ drop k ρ
  ren-up-seq k ρ rewrite up-seqᵣ k ρ | map-sub-id (drop k ρ) = refl

  ren-cons-seq : ∀ x ρ₁ ρ₂ → (x • ρ₁) ⨟ᵣ ρ₂ ≡ ⦉ ρ₂ ⦊ x • (ρ₁ ⨟ᵣ ρ₂)
  ren-cons-seq x ρ₁ ρ₂ rewrite cons-seqᵣ x ρ₁ ρ₂ = refl

  ren-head : ∀ ρ x → rename (x • ρ) (` 0) ≡ ` x
  ren-head ρ x = refl

  ren-tail : ∀ ρ x → (↑ 1 ⨟ᵣ x • ρ) ≡ ρ
  ren-tail ρ x rewrite ren-up-seq 1 (x • ρ) | drop-0 ρ = refl

  inc=⨟ᵣ↑ : ∀ ρ → inc ρ ≡ ρ ⨟ᵣ ↑ 1
  inc=⨟ᵣ↑ (↑ k) rewrite ren-up-seq k (↑ 1) | +-comm k 1 = refl
  inc=⨟ᵣ↑ (x • ρ) rewrite ren-cons-seq x ρ (↑ 1) | inc=⨟ᵣ↑ ρ = refl

  ext-cons-shift : ∀ ρ → ext ρ ≡ (0 • (ρ ⨟ᵣ ↑ 1))
  ext-cons-shift ρ rewrite ext-def ρ | inc=⨟ᵣ↑ ρ = refl

  ren-η : ∀ ρ x → ⦉ ⦉ ρ ⦊ 0 • (↑ 1 ⨟ᵣ ρ) ⦊ x ≡ ⦉ ρ ⦊ x
  ren-η ρ 0 = refl
  ren-η ρ (suc x) rewrite ren-up-seq 1 ρ | dropr-add 1 ρ x = refl

  ren-idL : ∀ ρ → id ⨟ᵣ ρ ≡ ρ
  ren-idL ρ rewrite ren-up-seq 0 ρ | drop-0 ρ = refl

  ren-dist :  ∀ x ρ τ → ((x • ρ) ⨟ᵣ τ) ≡ ((⦉ τ ⦊ x) • (ρ ⨟ᵣ τ))
  ren-dist x ρ τ rewrite ren-cons-seq x ρ τ = refl

  ren-op : ∀ ρ o (args : Args (sig o))
         → rename ρ (o ⦅ args ⦆)  ≡ o ⦅ ren-args ρ args ⦆
  ren-op ρ o args = refl        

  QRR : Quotable RenameIsMap RenameIsMap RenameIsMap
  QRR = record
          { ⌈_⌉ = ⦉_⦊ ; val₂₃ = λ x → x ; quote-map = λ σ₂ v₁ → refl
          ; var→val₂₃ = λ x → refl ; quote-val₂₃ = λ v₂ → refl
          ; map₂-var→val₁ = λ x σ₂ → refl ; val₂₃-shift = λ v₂ → refl }
  open Quotable QRR renaming (g-drop-seq to dropr-seq)

  {------ Composing renamings -------}
  
  seq-rename : ∀ ρ₁ ρ₂ x → ⦉ ρ₁ ⨟ᵣ ρ₂ ⦊ x ≡ ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x)
  seq-rename ρ₁ ρ₂ x = var-injective (Quotable.compose-sub QRR ρ₁ ρ₂ x)

  ren-assoc : ∀ σ τ θ → (σ ⨟ᵣ τ) ⨟ᵣ θ ≡ σ ⨟ᵣ τ ⨟ᵣ θ
  ren-assoc (↑ k) τ θ rewrite ren-up-seq k τ
      | ren-up-seq k (τ ⨟ᵣ θ) | dropr-seq k τ θ = refl
  ren-assoc (x • σ) τ θ = begin
    (x • σ ⨟ᵣ τ) ⨟ᵣ θ               ≡⟨ cong (λ □ → □ ⨟ᵣ θ) (ren-cons-seq _ _ _) ⟩
    (⦉ τ ⦊ x • (σ ⨟ᵣ τ)) ⨟ᵣ θ          ≡⟨  ren-cons-seq _ _ _ ⟩
    (⦉ θ ⦊ (⦉ τ ⦊ x)) • ((σ ⨟ᵣ τ) ⨟ᵣ θ) ≡⟨ cong₂ _•_ (sym (seq-rename _ _ _)) (ren-assoc _ _ _) ⟩
    ⦉ τ ⨟ᵣ θ ⦊ x • (σ ⨟ᵣ (τ ⨟ᵣ θ))     ≡⟨ sym (ren-cons-seq _ _ _) ⟩
    (x • σ) ⨟ᵣ (τ ⨟ᵣ θ)               ∎

  {- not currently used -}
  {-
  inc-seq : ∀ ρ₁ ρ₂ → (inc ρ₁ ⨟ᵣ ext ρ₂) ≡ inc (ρ₁ ⨟ᵣ ρ₂)
  inc-seq (↑ k) ρ₂ rewrite ren-up-seq k ρ₂ | ren-up-seq (suc k) (0 • inc ρ₂)
      | dropr-ext k ρ₂ = refl
  inc-seq (x • ρ₁) ρ₂ = begin
      inc (x • ρ₁) ⨟ᵣ ext ρ₂           ≡⟨ ren-cons-seq _ _ _ ⟩
      ⦉ inc ρ₂ ⦊ x • (inc ρ₁ ⨟ᵣ ext ρ₂) ≡⟨ cong (λ □ → □ • (inc ρ₁ ⨟ᵣ ext ρ₂)) (inc-suc ρ₂ x) ⟩
      suc (⦉ ρ₂ ⦊ x) • (inc ρ₁ ⨟ᵣ ext ρ₂) ≡⟨ cong (λ □ → suc (⦉ ρ₂ ⦊ x) • □) (inc-seq _ _) ⟩
      inc (⦉ ρ₂ ⦊ x • (ρ₁ ⨟ᵣ ρ₂))      ≡⟨ cong inc (sym (ren-cons-seq x ρ₁ ρ₂)) ⟩
      inc ((x • ρ₁) ⨟ᵣ ρ₂)            ∎
-}

  compose-ext : ∀(ρ₁ ρ₂ : Rename) → (ext ρ₁ ⨟ᵣ ext ρ₂) ≡ ext (ρ₁ ⨟ᵣ ρ₂)
  compose-ext ρ₁ ρ₂ = begin
      ext ρ₁ ⨟ᵣ ext ρ₂             ≡⟨ cong (λ □ → □ ⨟ᵣ ext ρ₂) (ext-cons-shift _) ⟩
      0 • (ρ₁ ⨟ᵣ ↑ 1) ⨟ᵣ ext ρ₂    ≡⟨ ren-cons-seq _ _ _ ⟩
      ⦉ ext ρ₂ ⦊ 0 • ((ρ₁ ⨟ᵣ ↑ 1) ⨟ᵣ ext ρ₂) ≡⟨ cong (λ □ → □ • ((ρ₁ ⨟ᵣ ↑ 1) ⨟ᵣ ext ρ₂)) (ext-0 _)  ⟩
      0 • ((ρ₁ ⨟ᵣ ↑ 1) ⨟ᵣ ext ρ₂)  ≡⟨ cong (_•_ 0) (ren-assoc _ _ _) ⟩
      0 • (ρ₁ ⨟ᵣ (↑ 1 ⨟ᵣ ext ρ₂))  ≡⟨ cong (λ □ → 0 • (ρ₁ ⨟ᵣ (↑ 1 ⨟ᵣ □))) (ext-cons-shift ρ₂) ⟩
      0 • (ρ₁ ⨟ᵣ (↑ 1 ⨟ᵣ (0 • (ρ₂ ⨟ᵣ ↑ 1)))) ≡⟨ cong (λ □ → 0 • (ρ₁ ⨟ᵣ □)) (ren-tail (ρ₂ ⨟ᵣ ↑ 1) _) ⟩
      0 • (ρ₁ ⨟ᵣ (ρ₂ ⨟ᵣ ↑ 1))      ≡⟨ cong (_•_ 0) (sym (ren-assoc _ _ _)) ⟩
      0 • ((ρ₁ ⨟ᵣ ρ₂) ⨟ᵣ ↑ 1)      ≡⟨ sym (ext-cons-shift _) ⟩
      ext (ρ₁ ⨟ᵣ ρ₂)               ∎

  FRR : FusableMap RenameIsMap RenameIsMap RenameIsMap
  FRR = record { Q = QRR ; var = λ x ρ₁ ρ₂ → sym (seq-rename ρ₁ ρ₂ x)
               ; compose-ext = compose-ext }

  compose-rename : ∀ ρ₁ ρ₂ M
     → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ ⨟ᵣ ρ₂) M
  compose-rename ρ₁ ρ₂ M = FusableMap.fusion FRR M


  commute-↑1 : ∀ ρ M
     → rename (ext ρ) (rename (↑ 1) M) ≡ rename (↑ 1) (rename ρ M)
  commute-↑1 ρ M = begin
      rename (ext ρ) (rename (↑ 1) M)  ≡⟨ compose-rename (↑ 1) (ext ρ) M ⟩
      rename (↑ 1 ⨟ᵣ (ext ρ)) M          ≡⟨ cong (λ □ → rename (↑ 1 ⨟ᵣ □) M) (ext-cons-shift _) ⟩
      rename (↑ 1 ⨟ᵣ (0 • (ρ ⨟ᵣ ↑ 1))) M  ≡⟨ cong (λ □ → rename □ M) (ren-tail _ _) ⟩
      rename (ρ ⨟ᵣ ↑ 1) M              ≡⟨ sym (compose-rename ρ (↑ 1) M) ⟩
      rename (↑ 1) (rename ρ M)        ∎

  rename-ext : ∀ ρ₁ ρ₂ M
     → (∀ x → ⦉ ρ₁ ⦊ x ≡ ⦉ ρ₂ ⦊ x)
     → rename ρ₁ M ≡ rename ρ₂ M
  rename-ext ρ₁ ρ₂ M f = MapCong.map-cong-abt MC {ρ₁}{ρ₂} f M
    where
    MC : MapCong RenameIsMap RenameIsMap
    MC = record { _≈_ = λ ρ₁ ρ₂ → ∀ x → ⦉ ρ₁ ⦊ x ≡ ⦉ ρ₂ ⦊ x
                ; var = λ x f → cong `_ (f x) ; ext≈ = ext-cong }

  {----------------------------------------------------------------------------
                             Substitution
   ---------------------------------------------------------------------------}

  Subst : Set
  Subst = GSubst ABT

  SubstIsSubstable : Substable ABT
  SubstIsSubstable = record { var→val = `_ ; shift = rename (↑ 1)
      ; var→val-suc-shift = λ {x} → refl }

  open GenericSubstitution.GenericSubst SubstIsSubstable using ()
      renaming (⧼_⧽ to ⟦_⟧; g-ext to exts; g-Z-shift to Z-shift) public
  open GenericSubstitution.GenericSubst SubstIsSubstable
      using (Shift; shift-up; shift-•)
      renaming (g-inc to incs; g-inc-shift to incs-rename;
      g-drop-inc to drop-incs; g-drop-add to drop-add; g-drop-ext to drop-exts;
      g-Shift-var to sub-shift-var; g-ext-def to exts-def;
      g-inc-Shift to incs-Shift; g-ext-cong to exts-cong)

  SubstIsMap : Map ABT
  SubstIsMap = record { “_” = λ M → M ; S = SubstIsSubstable }
  open Map SubstIsMap
      renaming (map-abt to ⟪_⟫; map-arg to ⟪_⟫ₐ; map-args to ⟪_⟫₊) public
  
  open ComposeMaps SubstIsMap SubstIsMap ⟪_⟫ (λ x → x)
      using (_⨟_; up-seq; cons-seq) public

  sub-up-seq : ∀ k σ → ↑ k ⨟ σ ≡ drop k σ
  sub-up-seq k σ rewrite up-seq k σ | map-sub-id (drop k σ) = refl

  sub-cons-seq : ∀ x σ₁ σ₂ → (x • σ₁) ⨟ σ₂ ≡ ⟪ σ₂ ⟫ x • (σ₁ ⨟ σ₂)
  sub-cons-seq x σ₁ σ₂ rewrite cons-seq x σ₁ σ₂ = refl

  sub-head : ∀ M σ → ⟦ M • σ ⟧ 0 ≡ M
  sub-head M σ = refl

  sub-tail : ∀ (M : ABT) σ → (↑ 1 ⨟ M • σ) ≡ σ
  sub-tail M σ rewrite sub-up-seq 1 (M • σ) | drop-0 σ = refl

  sub-suc : ∀ M σ x → ⟪ M • σ ⟫ (` suc x) ≡ ⟪ σ ⟫ (` x)
  sub-suc M σ x = refl

  shift-eq : ∀ x k → ⟪ ↑ k ⟫ (` x) ≡ ` (k + x)
  shift-eq x k = refl

  sub-idL : (σ : Subst) → id ⨟ σ ≡ σ
  sub-idL σ rewrite sub-up-seq 0 σ | drop-0 σ = refl

  sub-dist :  ∀ σ τ M → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
  sub-dist σ τ M rewrite sub-cons-seq M σ τ = refl

  sub-op : ∀ σ op args → ⟪ σ ⟫ (op ⦅ args ⦆) ≡ op ⦅ ⟪ σ ⟫₊ args  ⦆
  sub-op σ op args = refl

  sub-nil : ∀ σ → ⟪ σ ⟫₊ nil ≡ nil
  sub-nil σ = refl

  sub-cons : ∀ σ b bs (arg : Arg b) (args : Args bs)
    → ⟪ σ ⟫₊ (cons arg args) ≡ cons (⟪ σ ⟫ₐ arg) (⟪ σ ⟫₊ args)
  sub-cons σ b bs arg args = refl

  sub-η : ∀ σ x → ⟦ ⟪ σ ⟫ (` 0) • (↑ 1 ⨟ σ) ⟧ x ≡ ⟦ σ ⟧ x
  sub-η σ 0 = refl
  sub-η σ (suc x) rewrite sub-up-seq 1 σ | drop-add 1 σ x = refl

  rename→subst : Rename → Subst
  rename→subst (↑ k) = ↑ k 
  rename→subst (x • ρ) = ` x • rename→subst ρ

  rename-subst : ∀ ρ M → rename ρ M ≡ ⟪ rename→subst ρ ⟫ M
  rename-subst ρ M = MapCong≊.map-cong-abt MRS (ρ≊ ρ) M
    where
    MRS = record { var→val-quote = λ x → refl ; shift-quote = λ { refl → refl }}
    open MapCong≊.R MRS
    ρ≊ : ∀ ρ → ρ ≊ rename→subst ρ
    ρ≊ (↑ k) = r-up
    ρ≊ (x • ρ) = r-cons refl (ρ≊ ρ)

  incs=⨟↑ : ∀ σ → incs σ ≡ σ ⨟ ↑ 1
  incs=⨟↑ (↑ k) rewrite sub-up-seq k (↑ 1) | +-comm k 1 = refl
  incs=⨟↑ (M • σ) = begin
      incs (M • σ)              ≡⟨⟩
      (rename (↑ 1) M • incs σ) ≡⟨ cong₂ _•_ (rename-subst (↑ 1) M)(incs=⨟↑ σ) ⟩
      ⟪ ↑ 1 ⟫ M • (σ ⨟ ↑ 1)     ≡⟨ sym (sub-cons-seq M σ (↑ 1)) ⟩
      M • σ ⨟ ↑ 1  ∎
    
  exts-cons-shift : ∀ σ → exts σ ≡ (` 0 • (σ ⨟ ↑ 1))
  exts-cons-shift σ rewrite exts-def σ | incs=⨟↑ σ = refl 

  exts-suc : ∀ σ x → ⟦ exts σ ⟧ (suc x) ≡ ⟦ σ ⨟ ↑ 1 ⟧ x
  exts-suc σ x rewrite exts-cons-shift σ = refl

  seq-subst : ∀ σ τ x → ⟦ σ ⨟ τ ⟧ x ≡ ⟪ τ ⟫ (⟦ σ ⟧ x)
  seq-subst (↑ k) τ x rewrite sub-up-seq k τ | drop-add k τ x = refl
  seq-subst (M • σ) τ zero rewrite sub-cons-seq M σ τ = refl
  seq-subst (M • σ) τ (suc x) rewrite sub-cons-seq M σ τ
      | seq-subst σ τ x = refl

  private
    sub-shift0 : ∀{σ} (M : ABT) → Shift 0 σ → ⟪ σ ⟫ M ≡ M
    ss0-arg  : ∀{σ} → Shift 0 σ → (b : ℕ) → (arg : Arg b) 
       → ⟪ σ ⟫ₐ {b} arg ≡ arg
    ss0-args  : ∀{σ} → Shift 0 σ → (bs : List ℕ) → (args : Args bs) 
       → ⟪ σ ⟫₊ {bs} args ≡ args
    sub-shift0 {σ}(` x) σ0 rewrite sub-shift-var {σ}{0} x σ0 = cong `_ refl
    sub-shift0 {σ}(op ⦅ args ⦆) σ0 = cong (_⦅_⦆ op) (ss0-args σ0 (sig op) args)
    ss0-arg σ0 zero (ast arg) = cong ast (sub-shift0 arg σ0)
    ss0-arg {σ} σ0 (suc b) (bind arg) rewrite exts-def σ =
        cong bind (ss0-arg (shift-• (incs-Shift σ0) refl) b arg)
    ss0-args σ0 [] nil = refl
    ss0-args σ0 (b ∷ bs) (cons arg args) =
        cong₂ cons (ss0-arg σ0 b arg) (ss0-args σ0 bs args)

  sub-id : ∀ {M : ABT} → ⟪ id ⟫ M ≡ M
  sub-id {M} = (sub-shift0 M (shift-up {0}))

  rename-id : {M : ABT} → rename (↑ 0) M ≡ M
  rename-id {M} rewrite rename-subst (↑ 0) M | sub-id {M} = refl

  sub-idR : ∀ σ → σ ⨟ id ≡ σ 
  sub-idR (↑ k) rewrite sub-up-seq k id | +-comm k 0 = refl
  sub-idR (M • σ) rewrite sub-cons-seq M σ id | sub-idR σ | sub-id {M} = refl

  exts-0 : ∀ σ → ⟦ exts σ ⟧ 0 ≡ ` 0
  exts-0 σ rewrite exts-def σ = refl

  exts-suc' : ∀ σ x → ⟦ exts σ ⟧ (suc x) ≡ rename (↑ 1) (⟦ σ ⟧ x)
  exts-suc' σ x rewrite exts-def σ | incs-rename σ x = refl

  exts-suc-rename : ∀ σ x → ⟦ exts σ ⟧ (suc x) ≡ rename (↑ 1) (⟪ σ ⟫ (` x))
  exts-suc-rename σ x rewrite exts-def σ | incs-rename σ x = refl

  {------ Composing substitution and renaming -------}

  open ComposeMaps SubstIsMap RenameIsMap rename `_
     renaming (_⨟_ to _⨟ˢᵣ_; up-seq to up-seqˢᵣ; cons-seq to cons-seqˢᵣ)

  sr-up-seq : ∀ k ρ → ↑ k ⨟ˢᵣ ρ ≡ map-sub `_ (drop k ρ)
  sr-up-seq k ρ rewrite up-seqˢᵣ k ρ = refl
  
  sr-cons-seq : ∀ M σ ρ → (M • σ) ⨟ˢᵣ ρ ≡ (rename ρ M) • (σ ⨟ˢᵣ ρ)
  sr-cons-seq M σ ρ rewrite cons-seqˢᵣ M σ ρ = refl  

  QSR : Quotable SubstIsMap RenameIsMap SubstIsMap
  QSR = record { ⌈_⌉ = rename ; val₂₃ = `_ ; quote-map = λ σ₂ v₁ → refl
          ; var→val₂₃ = λ x₁ → refl ; quote-val₂₃ = λ v₂ → refl
          ; map₂-var→val₁ = λ x₁ σ₂ → refl ; val₂₃-shift = λ v₂ → refl }

  seq-sub-ren : ∀ x σ ρ  →  rename ρ (⟦ σ ⟧ x) ≡ ⟦ σ ⨟ˢᵣ ρ ⟧ x
  seq-sub-ren x σ ρ = sym (Quotable.compose-sub QSR σ ρ x)

  compose-incs-ext : ∀ σ ρ → (incs σ ⨟ˢᵣ ext ρ) ≡ incs (σ ⨟ˢᵣ ρ)
  compose-incs-ext (↑ k) ρ rewrite sr-up-seq (suc k) (ext ρ) | ext-def ρ | dropr-inc k ρ
      | Quotable.g-map-sub-inc QSR (drop k ρ) | sr-up-seq k ρ = refl
  compose-incs-ext (M • σ) ρ =
      begin
      incs (M • σ) ⨟ˢᵣ ext ρ                               ≡⟨ sr-cons-seq _ _ _ ⟩
      rename (ext ρ) (rename (↑ 1) M) • (incs σ ⨟ˢᵣ ext ρ) ≡⟨ cong (λ □ → □ • (incs σ ⨟ˢᵣ ext ρ)) (commute-↑1 ρ M) ⟩
      rename (↑ 1) (rename ρ M) • (incs σ ⨟ˢᵣ ext ρ)       ≡⟨ cong (λ □ → rename (↑ 1) (rename ρ M) • □) (compose-incs-ext _ _) ⟩
      rename (↑ 1) (rename ρ M) • incs (σ ⨟ˢᵣ ρ)           ≡⟨⟩
      incs (rename ρ M • (σ ⨟ˢᵣ ρ))                        ≡⟨ cong incs (sym (sr-cons-seq M σ ρ)) ⟩
      incs (M • σ ⨟ˢᵣ ρ)                                   ∎

  compose-exts-ext : ∀ σ ρ → (exts σ) ⨟ˢᵣ (ext ρ) ≡ exts (σ ⨟ˢᵣ ρ)
  compose-exts-ext σ ρ rewrite exts-def σ | ext-def ρ = begin
      (` 0 • incs σ) ⨟ˢᵣ (0 • inc ρ)  ≡⟨ sr-cons-seq _ _ _ ⟩
      ` 0 • (incs σ ⨟ˢᵣ (0 • inc ρ))  ≡⟨ cong (λ □ → ` 0 • (incs σ ⨟ˢᵣ □)) (sym (ext-def _)) ⟩
      ` 0 • (incs σ ⨟ˢᵣ (ext ρ))      ≡⟨ cong (_•_ (` 0)) (compose-incs-ext _ _) ⟩
      ` 0 • incs (σ ⨟ˢᵣ ρ)            ≡⟨ sym (exts-def _) ⟩
      exts (σ ⨟ˢᵣ ρ)
      ∎

  FSR : FusableMap SubstIsMap RenameIsMap SubstIsMap
  FSR = record { Q = QSR ; var = seq-sub-ren ; compose-ext = compose-exts-ext }

  compose-ren-sub : ∀ ρ σ M → rename ρ (⟪ σ ⟫ M) ≡ ⟪ σ ⨟ˢᵣ ρ ⟫ M
  compose-ren-sub ρ σ M = FusableMap.fusion FSR {σ}{ρ} M

  incs=⨟ˢᵣ↑ : ∀ σ → incs σ ≡ σ ⨟ˢᵣ ↑ 1
  incs=⨟ˢᵣ↑ (↑ k) rewrite sr-up-seq k (↑ 1) |  +-comm k 1 = refl
  incs=⨟ˢᵣ↑ (M • σ) rewrite sr-cons-seq M σ (↑ 1) | incs=⨟ˢᵣ↑ σ = refl

  {------ Composing renaming and substitution -------}

  open ComposeMaps {Var}{ABT}{ABT} RenameIsMap SubstIsMap ⟦_⟧ (λ M → M)
     renaming (_⨟_ to _⨟ᵣˢ_; up-seq to up-seqᵣˢ; cons-seq to cons-seqᵣˢ)

  rs-up-seq : ∀ k σ → ↑ k ⨟ᵣˢ σ ≡ drop k σ
  rs-up-seq k σ rewrite up-seqᵣˢ k σ | map-sub-id (drop k σ) = refl

  rs-cons-seq : ∀ x ρ σ → (x • ρ) ⨟ᵣˢ σ ≡ (⟦ σ ⟧ x) • (ρ ⨟ᵣˢ σ)
  rs-cons-seq x ρ σ rewrite cons-seqᵣˢ x ρ σ = refl

  QRS : Quotable RenameIsMap SubstIsMap SubstIsMap
  QRS = record { ⌈_⌉ = ⟦_⟧ ; val₂₃ = λ M → M ; quote-map = λ σ₂ v₁ → refl
          ; var→val₂₃ = λ x → refl ; quote-val₂₃ = λ v₂ → refl
          ; map₂-var→val₁ = λ x σ₂ → refl ; val₂₃-shift = λ v₂ → refl }

  seq-ren-sub : ∀ x ρ σ  →  ⟦ σ ⟧ (⦉ ρ ⦊ x) ≡ ⟦ ρ ⨟ᵣˢ σ ⟧ x
  seq-ren-sub x ρ σ = sym (Quotable.compose-sub QRS ρ σ x)

  compose-inc-exts : ∀ ρ σ → (inc ρ ⨟ᵣˢ exts σ) ≡ incs (ρ ⨟ᵣˢ σ)
  compose-inc-exts (↑ k) σ rewrite rs-up-seq (suc k) (exts σ) | exts-def σ 
      | rs-up-seq k σ | drop-incs k σ = refl
  compose-inc-exts (x • ρ) σ = begin
      inc (x • ρ) ⨟ᵣˢ exts σ                 ≡⟨ rs-cons-seq _ _ _ ⟩
      ⟦ exts σ ⟧ (suc x) • (inc ρ ⨟ᵣˢ exts σ)    ≡⟨ cong (λ □ → □ • (inc ρ ⨟ᵣˢ exts σ)) (exts-suc-rename σ x) ⟩
      rename (↑ 1) (⟦ σ ⟧ x) • (inc ρ ⨟ᵣˢ exts σ) ≡⟨ cong₂ _•_ refl (compose-inc-exts ρ σ) ⟩
      rename (↑ 1) (⟦ σ ⟧ x) • incs (ρ ⨟ᵣˢ σ) ≡⟨ cong incs (sym (rs-cons-seq _ _ _)) ⟩ 
      incs (x • ρ ⨟ᵣˢ σ)    ∎
  
  compose-ext-exts : ∀ ρ σ → (ext ρ) ⨟ᵣˢ (exts σ) ≡ exts (ρ ⨟ᵣˢ σ)
  compose-ext-exts ρ σ {- rewrite ext-def ρ | rs-cons-seq 0 (inc ρ) (exts σ) | exts-def σ | exts-def (ρ ⨟ᵣˢ σ) | compose-inc-exts ρ σ -} = begin
    ext ρ ⨟ᵣˢ exts σ   ≡⟨ cong₂ _⨟ᵣˢ_ (ext-def ρ) refl ⟩
    0 • inc ρ ⨟ᵣˢ exts σ ≡⟨ rs-cons-seq _ _ _ ⟩
    ⟦ exts σ ⟧ 0 • (inc ρ ⨟ᵣˢ exts σ) ≡⟨ cong₂ _•_ (exts-0 σ) refl ⟩
    ` 0 • (inc ρ ⨟ᵣˢ exts σ) ≡⟨ cong (_•_ (` 0)) (compose-inc-exts _ _) ⟩
    ` 0 • incs (ρ ⨟ᵣˢ σ) ≡⟨ sym (exts-def _) ⟩
    exts (ρ ⨟ᵣˢ σ)     ∎

  FRS : FusableMap RenameIsMap SubstIsMap SubstIsMap
  FRS = record { Q = QRS ; var = seq-ren-sub ; compose-ext = compose-ext-exts }

  compose-sub-ren : ∀ σ ρ M → ⟪ σ ⟫ (rename ρ M) ≡ ⟪ ρ ⨟ᵣˢ σ ⟫ M
  compose-sub-ren σ ρ M = FusableMap.fusion FRS {ρ}{σ} M

  {------ Composing substitutions -------}

  commute-subst-shift : ∀{σ : Subst} (M : ABT)
     → ⟪ exts σ ⟫ (rename (↑ 1) M) ≡ rename (↑ 1) (⟪ σ ⟫ M)
  commute-subst-shift {σ} M =  begin
    ⟪ exts σ ⟫ (rename (↑ 1) M)    ≡⟨ compose-sub-ren (exts σ) (↑ 1) M ⟩
    ⟪ ↑ 1 ⨟ᵣˢ exts σ ⟫ M           ≡⟨  cong (λ □ → ⟪ □ ⟫ M) (rs-up-seq 1 (exts σ)) ⟩
    ⟪ drop 1 (exts σ) ⟫ M         ≡⟨ cong (λ □ → ⟪ drop 1 □ ⟫ M) (exts-def _) ⟩
    ⟪ drop 0 (incs σ) ⟫ M         ≡⟨ cong (λ □ → ⟪ □ ⟫ M) (drop-0 (incs σ)) ⟩    
    ⟪ incs σ ⟫ M                  ≡⟨ cong (λ □ → ⟪ □ ⟫ M) (incs=⨟ˢᵣ↑ σ) ⟩
    ⟪ σ ⨟ˢᵣ ↑ 1 ⟫ M                ≡⟨ sym (compose-ren-sub (↑ 1) σ M)  ⟩
    rename (↑ 1) (⟪ σ ⟫ M)         ∎
    
  QSS : Quotable SubstIsMap SubstIsMap SubstIsMap
  QSS = record { ⌈_⌉ = ⟪_⟫ ; val₂₃ = λ M → M ; quote-map = λ σ₂ v₁ → refl
          ; var→val₂₃ = λ x → refl ; quote-val₂₃ = λ v₂ → refl
          ; map₂-var→val₁ = λ x σ₂ → refl ; val₂₃-shift = λ v₂ → refl }
  open Quotable QSS renaming (g-drop-seq to drop-seq)

  incs-seq : ∀ σ₁ σ₂ → (incs σ₁ ⨟ exts σ₂) ≡ incs (σ₁ ⨟ σ₂)
  incs-seq (↑ k) σ₂ = begin
    incs (↑ k) ⨟ exts σ₂    ≡⟨ sub-up-seq _ _ ⟩
    drop (suc k) (exts σ₂)  ≡⟨ drop-exts k σ₂ ⟩
    incs (drop k σ₂)        ≡⟨ cong incs (sym (sub-up-seq k σ₂))⟩
    incs (↑ k ⨟ σ₂)         ∎
  incs-seq (M • σ₁) σ₂ = begin
    incs (M • σ₁) ⨟ exts σ₂                            ≡⟨⟩
    (rename (↑ 1) M • incs σ₁) ⨟ exts σ₂               ≡⟨ sub-cons-seq _ _ _ ⟩
    ⟪ exts σ₂ ⟫ (rename (↑ 1) M) • (incs σ₁ ⨟ exts σ₂) ≡⟨ cong (λ □ → ⟪ exts σ₂ ⟫ (rename (↑ 1) M) • □) (incs-seq _ _)  ⟩
    ⟪ exts σ₂ ⟫ (rename (↑ 1) M) • incs (σ₁ ⨟ σ₂)      ≡⟨ cong (λ □ → □ • incs (σ₁ ⨟ σ₂)) (commute-subst-shift M) ⟩
    rename (↑ 1) (⟪ σ₂ ⟫ M) • incs (σ₁ ⨟ σ₂)           ≡⟨⟩
    incs (⟪ σ₂ ⟫ M • (σ₁ ⨟ σ₂))                        ≡⟨ cong incs (sym (sub-cons-seq M σ₁ σ₂)) ⟩
    incs (M • σ₁ ⨟ σ₂)      ∎

  exts-seq : ∀ σ₁ σ₂ → exts σ₁ ⨟ exts σ₂ ≡ exts (σ₁ ⨟ σ₂)
  exts-seq (↑ k) σ₂ = begin
    exts (↑ k) ⨟ exts σ₂                      ≡⟨ cong₂ _⨟_ (exts-def _) refl ⟩
    ((` 0) • ↑ (suc k)) ⨟ exts σ₂             ≡⟨ sub-cons-seq _ _ _ ⟩
    ⟪ exts σ₂ ⟫ (` 0) • (↑ (suc k) ⨟ exts σ₂) ≡⟨ cong₂ _•_ (exts-0 _) refl ⟩
    ` 0 • (↑ (suc k) ⨟ exts σ₂)               ≡⟨ cong (_•_ (` 0)) (sub-up-seq _ _) ⟩
    (` 0) • (drop (suc k) (exts σ₂))          ≡⟨ cong (λ □ → (` 0) • (drop (suc k) □)) (exts-def σ₂) ⟩
    (` 0) • (drop (suc k) (` 0 • incs σ₂))    ≡⟨⟩
    (` 0) • (drop k (incs σ₂))                ≡⟨⟩
    (` 0) • (drop (suc k) (` 0 • incs σ₂))    ≡⟨ cong (λ □ → (` 0) • (drop (suc k) □)) (sym (exts-def σ₂)) ⟩
    (` 0) • (drop (suc k) (exts σ₂))          ≡⟨ cong (_•_ (` 0)) (sym (sub-up-seq (suc k) (exts σ₂))) ⟩
    (` 0) • (↑ (suc k) ⨟ exts σ₂)             ≡⟨ cong (_•_ (` 0)) (incs-seq _ _) ⟩
    (` 0) • incs (↑ k ⨟ σ₂)                   ≡⟨ sym (exts-def _) ⟩
    exts (↑ k ⨟ σ₂)
    ∎
  exts-seq (M • σ₁) σ₂ = begin
    exts (M • σ₁) ⨟ exts σ₂                                       ≡⟨ cong₂ _⨟_ (exts-def _) refl ⟩
    ((` 0) • incs (M • σ₁)) ⨟ exts σ₂                             ≡⟨⟩
    ((` 0) • (rename (↑ 1) M • incs σ₁)) ⨟ exts σ₂                ≡⟨ sub-cons-seq _ _ _ ⟩
    ⟪ exts σ₂ ⟫ (` 0) • ((rename (↑ 1) M • incs σ₁) ⨟ exts σ₂)    ≡⟨ cong₂ _•_ (exts-0 σ₂) refl ⟩
    (` 0) • ((rename (↑ 1) M • incs σ₁) ⨟ exts σ₂)                ≡⟨ cong (_•_ (` 0)) (sub-cons-seq _ _ _) ⟩
    (` 0) • (⟪ exts σ₂ ⟫ (rename (↑ 1) M) • (incs σ₁ ⨟ exts σ₂))  ≡⟨ cong (λ □ → (` 0) • (⟪ exts σ₂ ⟫ (rename (↑ 1) M) • □)) (incs-seq _ _)  ⟩
    (` 0) • (⟪ exts σ₂ ⟫ (rename (↑ 1) M) • incs (σ₁ ⨟ σ₂))       ≡⟨ cong (λ □ → (` 0) • (□ • incs (σ₁ ⨟ σ₂))) (commute-subst-shift M) ⟩
    (` 0) • (rename (↑ 1) (⟪ σ₂ ⟫ M) • incs (σ₁ ⨟ σ₂))            ≡⟨ refl ⟩
    (` 0) • incs (⟪ σ₂ ⟫ M • (σ₁ ⨟ σ₂))                   ≡⟨ sym (exts-def _) ⟩
    exts (⟪ σ₂ ⟫ M • (σ₁ ⨟ σ₂))                           ≡⟨ cong exts (sym (sub-cons-seq _ _ _)) ⟩
    exts (M • σ₁ ⨟ σ₂)       ∎

  FSS : FusableMap SubstIsMap SubstIsMap SubstIsMap
  FSS = record { Q = QSS ; var = λ x σ₁ σ₂ → sym (seq-subst σ₁ σ₂ x)
               ; compose-ext = exts-seq }

  sub-sub : ∀ {M σ₁ σ₂} → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
  sub-sub {M}{σ₁}{σ₂} = FusableMap.fusion FSS {σ₁}{σ₂} M

  sub-assoc : ∀ {σ τ θ} → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  sub-assoc {↑ k} {τ} {θ}= begin
    (↑ k ⨟ τ) ⨟ θ     ≡⟨ cong (λ □ → □ ⨟ θ) (sub-up-seq _ _) ⟩
    (drop k τ) ⨟ θ    ≡⟨ sym (drop-seq _ _ _) ⟩
    drop k (τ ⨟ θ)    ≡⟨ sym (sub-up-seq _ _) ⟩
    ↑ k ⨟ (τ ⨟ θ)      ∎
  sub-assoc {M • σ} {τ} {θ} {- rewrite sub-assoc {σ}{τ}{θ}-} = begin
    (M • σ ⨟ τ) ⨟ θ                   ≡⟨ cong (λ □ → □ ⨟ θ) (sub-cons-seq _ _ _) ⟩
    (⟪ τ ⟫ M • (σ ⨟ τ)) ⨟ θ           ≡⟨ sub-cons-seq _ _ _ ⟩
    ⟪ θ ⟫ (⟪ τ ⟫ M) • ((σ ⨟ τ) ⨟ θ)   ≡⟨ cong (λ □ → ⟪ θ ⟫ (⟪ τ ⟫ M) • □) sub-assoc ⟩
    ⟪ θ ⟫ (⟪ τ ⟫ M) • (σ ⨟ (τ ⨟ θ))   ≡⟨ cong (λ □ → □ • (σ ⨟ (τ ⨟ θ))) (sub-sub {M}{τ}{θ}) ⟩
    ⟪ τ ⨟ θ ⟫ M • (σ ⨟ (τ ⨟ θ))       ≡⟨ sym (sub-cons-seq _ _ _) ⟩ 
    (M • σ) ⨟ (τ ⨟ θ)                 ∎

  subst-zero : ABT → Subst
  subst-zero M = M • id

  _[_] : ABT → ABT → ABT
  N [ M ] =  ⟪ subst-zero M ⟫ N

  subst-zero-exts-cons : ∀{σ M} → exts σ ⨟ subst-zero M ≡ M • σ
  subst-zero-exts-cons {σ}{M} = begin
     exts σ ⨟ subst-zero M      ≡⟨ cong (λ □ → □  ⨟ subst-zero M) (exts-cons-shift _) ⟩
     (` 0 • (σ ⨟ ↑ 1)) ⨟ (M • id) ≡⟨ sub-cons-seq _ _ _ ⟩
     M • ((σ ⨟ ↑ 1) ⨟ (M • id))   ≡⟨ cong (_•_ M) sub-assoc ⟩
     M • (σ ⨟ (↑ 1 ⨟ (M • id)))   ≡⟨ cong (λ □ → M • (σ ⨟ □)) (sub-tail _ _) ⟩
     M • (σ ⨟ id)                 ≡⟨ cong (_•_ M) (sub-idR _) ⟩
     M • σ                        ∎

  subst-commute : ∀{N M σ} → (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
  subst-commute {N}{M}{σ} =  begin
    (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ]           ≡⟨ sub-sub {N}{exts σ} ⟩
    ⟪ exts σ ⨟ subst-zero (⟪ σ ⟫ M) ⟫ N  ≡⟨ cong (λ □ → ⟪ □ ⟫ N) subst-zero-exts-cons ⟩
    ⟪ (⟪ σ ⟫ M) • σ ⟫ N                  ≡⟨ cong (λ □ → ⟪ ⟪ σ ⟫ M • □ ⟫ N) (sym (sub-idL _)) ⟩
    ⟪ ⟪ σ ⟫ M • (id ⨟ σ) ⟫ N             ≡⟨ cong (λ □ → ⟪ □ ⟫ N) (sym (sub-cons-seq _ _ _)) ⟩
    ⟪ M • id ⨟ σ ⟫ N                     ≡⟨⟩
    ⟪ subst-zero M ⨟ σ ⟫ N               ≡⟨ sym (sub-sub {N}{subst-zero M}{σ}) ⟩
    ⟪ σ ⟫ (⟪ subst-zero M ⟫ N)           ≡⟨⟩
    ⟪ σ ⟫ (N [ M ])      ∎

  commute-subst : ∀{N M σ} → ⟪ σ ⟫ (N [ M ]) ≡ (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ]
  commute-subst {N}{M}{σ} = sym (subst-commute {N}{M}{σ})

  _〔_〕 : ABT → ABT → ABT
  _〔_〕 N M = ⟪ exts (subst-zero M) ⟫ N

  substitution : ∀{M N L} → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
  substitution {M}{N}{L} = commute-subst{N = M}{M = N}{σ = subst-zero L}

  exts-sub-cons : ∀ σ N V → (⟪ exts σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
  exts-sub-cons σ N V {-rewrite exts-cons-shift σ -} = begin
     (⟪ exts σ ⟫ N) [ V ]                 ≡⟨⟩
     ⟪ subst-zero V ⟫ (⟪ exts σ ⟫ N)      ≡⟨ sub-sub {N}{exts σ}{subst-zero V} ⟩
     ⟪ exts σ ⨟ subst-zero V ⟫ N           ≡⟨ cong (λ □ → ⟪ □ ⨟ subst-zero V ⟫ N) (exts-cons-shift σ) ⟩
     ⟪ (` 0 • (σ ⨟ ↑ 1)) ⨟ (V • id) ⟫ N     ≡⟨ cong (λ □ → ⟪ □ ⟫ N) (sub-cons-seq _ _ _) ⟩
     ⟪ V • ((σ ⨟ ↑ 1) ⨟ (V • id)) ⟫ N      ≡⟨ cong (λ □ → ⟪ V • □ ⟫ N) sub-assoc ⟩
     ⟪ V • (σ ⨟ (↑ 1 ⨟ (V • id))) ⟫ N      ≡⟨ cong (λ □ → ⟪ V • (σ ⨟ □) ⟫ N) (sub-tail _ _) ⟩
     ⟪ V • (σ ⨟ id) ⟫ N                    ≡⟨ cong (λ □ → ⟪ V • □ ⟫ N) (sub-idR _)  ⟩
     ⟪ V • σ ⟫ N
     ∎

{-

  _ : ∀{x : Var} → ⟦ subst-zero (` x) ⟧ 0 ≡ (` x)
  _ = refl

  _ : ∀{x : Var} → ⟦ subst-zero (` x) ⟧ 1 ≡ ` 0
  _ = refl


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
    exts-cons-shift σ rewrite incs=⨟↑ σ = refl

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
         ≡⟨ {!!} {- cong (λ □ → rename □ (⟦ σ ⟧ x)) (ren-tail {inc ρ}{x}) -} ⟩
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

      incs-seq : ∀ σ₁ σ₂ → (incs σ₁ ⨟ exts σ₂) ≡ incs (σ₁ ⨟ σ₂)
      incs-seq (↑ k) σ₂ = drop-exts k σ₂
      incs-seq (M • σ₁) σ₂ rewrite incs-seq σ₁ σ₂
          | commute-subst-rename {M}{σ₂}{↑ 1} (λ {x} → exts-suc' σ₂ x) = refl

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
    subst-commute {N}{M}{σ}
      rewrite exts-cons-shift σ | drop-0 {ABT} σ = {!!}

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
        = {!!}

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
-}

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
  WF-exts {σ = σ} wfσ (s≤s z≤n) rewrite exts-0 σ = WF-var zero (s≤s z≤n)
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
            | seq-subst σ (↑ 1) x | seq-subst τ (↑ 1) x
            | incs-rename σ x | incs-rename τ x | eq x = refl

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

