open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n; _≤?_)
open import Data.Nat.Properties using (+-comm; +-suc; ≤-pred)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var 

module Substitution where

open GenericSubstitution
    using (GSubst; ↑; _•_; Substable; id; drop; map-sub; map-sub-id; drop-0)
    public
    
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

module ABTOps (Op : Set) (sig : Op → List ℕ)  where

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
