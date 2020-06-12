{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning 
open import Var

module experimental.Substitution (Op : Set) (sig : Op → List ℕ) where

open import GenericSubstitution public
open import experimental.ABT Op sig
open import experimental.Map Op sig

Rename : Set
Rename = GSubst Var

RenameIsSubstable : Substable Var
RenameIsSubstable = record { var→val = λ x → x ; shift = suc
    ; var→val-suc-shift = λ {x} → refl }

RenameIsMap : Map Var 
RenameIsMap = record { “_” = `_ ; S = RenameIsSubstable }
open Map RenameIsMap renaming (map-abt to rename; map-arg to ren-arg) public
open GenericSubst RenameIsSubstable using ()
    renaming (⧼_⧽ to ⦉_⦊; g-ext to ext; g-inc to inc;
    g-ext-cong to ext-cong; g-inc-shift to inc-suc;
    g-drop-add to dropr-add; g-drop-inc to dropr-inc;
    g-drop-ext to dropr-ext; Shift to RenShift; g-Shift-var to ren-shift-var;
    ShftAbv to RenShftAbv; g-ext-ShftAbv to ext-ShftAbv;
    g-ShftAbv→Shift to ShftAbv→Shift)
    public
open ComposeMaps RenameIsMap RenameIsMap ⦉_⦊ (λ x → x)
    using () renaming (_⨟_ to _⨟ᵣ_) public

private
  ext-0 : ∀ ρ → ⦉ ext ρ ⦊ 0 ≡ 0
  ext-0 ρ = refl

ext-suc : ∀ ρ x → ⦉ ext ρ ⦊ (suc x) ≡ suc (⦉ ρ ⦊ x)
ext-suc ρ x rewrite inc-suc ρ x = refl

ren-tail : ∀ x ρ → (↑ 1 ⨟ᵣ x • ρ) ≡ ρ
ren-tail x ρ rewrite drop-0 ρ | map-sub-id ρ = refl

inc=⨟ᵣ↑ : ∀ ρ → inc ρ ≡ ρ ⨟ᵣ ↑ 1
inc=⨟ᵣ↑ (↑ k) rewrite +-comm k 1 = refl
inc=⨟ᵣ↑ (x • ρ) = cong (_•_ (suc x)) (inc=⨟ᵣ↑ ρ)

QRR : Quotable RenameIsMap RenameIsMap RenameIsMap
QRR = record
        { ⌈_⌉ = ⦉_⦊ ; val₂₃ = λ x → x ; quote-map = λ σ₂ v₁ → refl
        ; var→val₂₃ = λ x → refl ; quote-val₂₃ = λ v₂ → refl
        ; map₂-var→val₁ = λ x σ₂ → refl ; val₂₃-shift = λ v₂ → refl }
open Quotable QRR renaming (g-drop-seq to dropr-seq)
{-# REWRITE dropr-seq #-}

seq-rename : ∀ ρ₁ ρ₂ x → ⦉ ρ₁ ⨟ᵣ ρ₂ ⦊ x ≡ ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x)
seq-rename ρ₁ ρ₂ x = var-injective (Quotable.compose-sub QRR ρ₁ ρ₂ x)
{-# REWRITE seq-rename #-}

ren-assoc : ∀ {σ τ θ} → (σ ⨟ᵣ τ) ⨟ᵣ θ ≡ σ ⨟ᵣ τ ⨟ᵣ θ
ren-assoc {↑ k} {τ} {θ} rewrite map-sub-id (drop k τ)
    | sym (map-sub-id ((drop k τ) ⨟ᵣ θ)) = refl
ren-assoc {x • σ} {τ} {θ} rewrite ren-assoc {σ}{τ}{θ} = refl
{-# REWRITE ren-assoc #-}

{- why not other direction? -}
inc-seq : ∀ ρ₁ ρ₂ → (inc ρ₁ ⨟ᵣ ext ρ₂) ≡ inc (ρ₁ ⨟ᵣ ρ₂)
inc-seq (↑ k) ρ₂ rewrite dropr-ext k ρ₂ | map-sub-id (drop k ρ₂)
  | map-sub-id (inc (drop k ρ₂)) = refl
inc-seq (x • ρ₁) ρ₂ rewrite inc-seq ρ₁ ρ₂ | inc-suc ρ₂ x = refl

compose-ext : ∀(ρ₁ ρ₂ : Rename) → (ext ρ₁ ⨟ᵣ ext ρ₂) ≡ ext (ρ₁ ⨟ᵣ ρ₂)
compose-ext ρ₁ ρ₂ rewrite inc-seq ρ₁ ρ₂ = refl

FRR : FusableMap RenameIsMap RenameIsMap RenameIsMap
FRR = record { Q = QRR ; var = λ x ρ₁ ρ₂ → sym (seq-rename ρ₁ ρ₂ x)
             ; compose-ext = compose-ext }
             
compose-rename : ∀(ρ₁ ρ₂ : Rename)(M : ABT)
   → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ ⨟ᵣ ρ₂) M
compose-rename ρ₁ ρ₂ M = FusableMap.fusion FRR M

commute-↑1 : ∀ ρ M → rename (ext ρ) (rename (↑ 1) M) ≡ rename (↑ 1) (rename ρ M)
commute-↑1 ρ M =
    begin
        rename (ext ρ) (rename (↑ 1) M)
    ≡⟨ compose-rename (↑ 1) (ext ρ) M ⟩
        rename (↑ 1 ⨟ᵣ 0 • inc ρ) M
    ≡⟨ cong (λ □ → rename □ M) (ren-tail 0 (inc ρ)) ⟩
        rename (inc ρ) M
    ≡⟨ cong (λ □ → rename □ M) (inc=⨟ᵣ↑ ρ)  ⟩
        rename (ρ ⨟ᵣ ↑ 1) M
    ≡⟨ sym (compose-rename ρ (↑ 1) M) ⟩
        rename (↑ 1) (rename ρ M)
    ∎

rename-ext : ∀{ρ₁ ρ₂}{M : ABT}
   → (∀ x → ⦉ ρ₁ ⦊ x ≡ ⦉ ρ₂ ⦊ x)
   → rename ρ₁ M ≡ rename ρ₂ M
rename-ext {ρ₁}{ρ₂}{M} f = MapCong.map-cong-abt MC {_}{ρ₁}{ρ₂} f M
  where
  MC : MapCong RenameIsMap RenameIsMap
  MC = record { _≈_ = λ ρ₁ ρ₂ → ∀ x → ⦉ ρ₁ ⦊ x ≡ ⦉ ρ₂ ⦊ x
              ; var = λ x f → cong `_ (f x) ; ext≈ = ext-cong }



{- Experimenting with putting GSubst stuff here -}

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import experimental.ScopedTuple using (Sig; Tuple; map; tuple-pred)
open import Size using (Size)

Subst : Set
Subst = GSubst ABT

SubstIsSubstable : Substable ABT
SubstIsSubstable = record { var→val = `_ ; shift = rename (↑ 1)
    ; var→val-suc-shift = λ {x} → refl }

SubstIsMap : Map ABT
SubstIsMap = record { “_” = λ M → M ; S = SubstIsSubstable }
open Map SubstIsMap renaming (map-abt to ⟪_⟫; map-arg to ⟪_⟫ₐ) public
⟪_⟫₊ : ∀{s : Size} → GSubst ABT →(bs : Sig)→ Tuple bs (λ _ → Term s)
     → Tuple bs (λ _ → ABT)
⟪_⟫₊ = λ σ bs → map (λ {b} → ⟪ σ ⟫ₐ b) {bs}

open GenericSubst (Map.S SubstIsMap) using ()
    renaming (⧼_⧽ to ⟦_⟧; g-ext to exts) public
open GenericSubst (Map.S SubstIsMap) using (Shift; shift-up; shift-•)
    renaming (g-inc to incs; g-inc-shift to incs-rename;
    g-drop-inc to drop-incs; g-drop-add to drop-add; g-drop-ext to drop-exts;
    g-Shift-var to sub-shift-var;
    g-inc-Shift to incs-Shift; g-ext-cong to exts-cong)

open ComposeMaps SubstIsMap SubstIsMap ⟪_⟫ (λ x → x)
    using (_⨟_) public


sub-head : ∀ M σ → ⟦ M • σ ⟧ 0 ≡ M
sub-head M σ = refl

sub-tail : ∀ (M : ABT) σ → (↑ 1 ⨟ M • σ) ≡ σ
sub-tail M σ rewrite drop-0 σ | map-sub-id σ = refl

sub-suc : ∀ M σ x → ⟪ M • σ ⟫ (` suc x) ≡ ⟪ σ ⟫ (` x)
sub-suc M σ x = refl

shift-eq : ∀ x k → ⟪ ↑ k ⟫ (` x) ≡ ` (k + x)
shift-eq x k = refl

sub-idL : (σ : Subst) → id ⨟ σ ≡ σ
sub-idL σ rewrite drop-0 σ | map-sub-id σ = refl

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
sub-η σ (suc x) rewrite map-sub-id (drop 1 σ) | drop-add {x} 1 σ = refl

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

incs=⨟↑ : ∀ σ → incs σ ≡ σ ⨟ ↑ 1
incs=⨟↑ (↑ k) rewrite +-comm k 1 = refl
incs=⨟↑ (M • σ) = cong₂ _•_ (rename-subst (↑ 1) M) (incs=⨟↑ σ)

exts-cons-shift : ∀ σ → exts σ ≡ (` 0 • (σ ⨟ ↑ 1))
exts-cons-shift σ rewrite incs=⨟↑ σ = refl

seq-subst : ∀ σ τ x → ⟦ σ ⨟ τ ⟧ x ≡ ⟪ τ ⟫ (⟦ σ ⟧ x)
seq-subst (↑ k) τ x rewrite map-sub-id (drop k τ) | drop-add{x} k τ = refl
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
rename-id {M} rewrite rename-subst (↑ 0) M | sub-id M = refl
{-# REWRITE rename-id #-}

sub-idR : ∀ σ → σ ⨟ id ≡ σ 
sub-idR (↑ k) rewrite +-comm k 0 = refl
sub-idR (M • σ) rewrite sub-idR σ | sub-id M = refl
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

FSR : FusableMap SubstIsMap RenameIsMap SubstIsMap
FSR = record { Q = QSR ; var = seq-sub-ren ; compose-ext = compose-exts-ext }

compose-ren-sub : ∀ ρ σ M → rename ρ (⟪ σ ⟫ M) ≡ ⟪ σ ⨟ˢᵣ ρ ⟫ M
compose-ren-sub ρ σ M = FusableMap.fusion FSR {_}{σ}{ρ} M

open ComposeMaps {Var}{ABT}{ABT} RenameIsMap SubstIsMap ⟦_⟧ (λ M → M)
   renaming (_⨟_ to _⨟ᵣˢ_)

QRS : Quotable RenameIsMap SubstIsMap SubstIsMap
QRS = record { ⌈_⌉ = ⟦_⟧ ; val₂₃ = λ M → M ; quote-map = λ σ₂ v₁ → refl
        ; var→val₂₃ = λ x → refl ; quote-val₂₃ = λ v₂ → refl
        ; map₂-var→val₁ = λ x σ₂ → refl ; val₂₃-shift = λ v₂ → refl }

seq-ren-sub : ∀ x ρ σ  →  ⟦ σ ⟧ (⦉ ρ ⦊ x) ≡ ⟦ ρ ⨟ᵣˢ σ ⟧ x
seq-ren-sub x ρ σ = sym (Quotable.compose-sub QRS ρ σ x)

compose-inc-exts : ∀ ρ σ → (inc ρ ⨟ᵣˢ exts σ) ≡ incs (ρ ⨟ᵣˢ σ)
compose-inc-exts (↑ k) σ rewrite drop-incs k σ
    | map-sub-id (drop k σ) | map-sub-id (incs (drop k σ)) = refl
compose-inc-exts (x • ρ) σ = cong₂ _•_ (incs-rename σ x) (compose-inc-exts ρ σ)

compose-ext-exts : ∀ ρ σ → (ext ρ) ⨟ᵣˢ (exts σ) ≡ exts (ρ ⨟ᵣˢ σ)
compose-ext-exts ρ σ rewrite compose-inc-exts ρ σ = refl

FRS : FusableMap RenameIsMap SubstIsMap SubstIsMap
FRS = record { Q = QRS ; var = seq-ren-sub ; compose-ext = compose-ext-exts }

compose-sub-ren : ∀ σ ρ M → ⟪ σ ⟫ (rename ρ M) ≡ ⟪ ρ ⨟ᵣˢ σ ⟫ M
compose-sub-ren σ ρ M = FusableMap.fusion FRS {_}{ρ}{σ} M

incs≡=⨟ˢᵣ↑ : ∀ σ → incs σ ≡ σ ⨟ˢᵣ ↑ 1
incs≡=⨟ˢᵣ↑ (↑ k) rewrite +-comm k 1 = refl
incs≡=⨟ˢᵣ↑ (M • σ) = cong₂ _•_ refl (incs≡=⨟ˢᵣ↑ σ)

msd : ∀ (σ : Subst) → map-sub (λ x → x) (drop 0 σ) ≡ σ
msd σ rewrite drop-0 σ | map-sub-id σ = refl

commute-subst-shift : ∀{σ : Subst} (M : ABT)
   → ⟪ exts σ ⟫ (rename (↑ 1) M) ≡ rename (↑ 1) (⟪ σ ⟫ M)
commute-subst-shift {σ} M =
  begin
      ⟪ exts σ ⟫ (rename (↑ 1) M)
  ≡⟨ compose-sub-ren (exts σ) (↑ 1) M ⟩
      ⟪ (↑ 1) ⨟ᵣˢ exts σ ⟫ M
  ≡⟨⟩
      ⟪ map-sub (λ x → x) (drop 0 (incs σ)) ⟫ M
  ≡⟨  cong (λ □ → ⟪ □ ⟫ M) (msd (incs σ)) ⟩
      ⟪ incs σ ⟫ M
  ≡⟨ cong (λ □ → ⟪ □ ⟫ M) (incs≡=⨟ˢᵣ↑ σ) ⟩
      ⟪ σ ⨟ˢᵣ ↑ 1 ⟫ M
  ≡⟨ sym (compose-ren-sub (↑ 1) σ M)  ⟩
      rename (↑ 1) (⟪ σ ⟫ M)
  ∎
  
QSS : Quotable SubstIsMap SubstIsMap SubstIsMap
QSS = record { ⌈_⌉ = ⟪_⟫ ; val₂₃ = λ M → M ; quote-map = λ σ₂ v₁ → refl
        ; var→val₂₃ = λ x → refl ; quote-val₂₃ = λ v₂ → refl
        ; map₂-var→val₁ = λ x σ₂ → refl ; val₂₃-shift = λ v₂ → refl }
open Quotable QSS renaming (g-drop-seq to drop-seq)


incs-seq : ∀ σ₁ σ₂ → (incs σ₁ ⨟ exts σ₂) ≡ incs (σ₁ ⨟ σ₂)
incs-seq (↑ k) σ₂ rewrite drop-exts k σ₂ = {!!}
incs-seq (M • σ₁) σ₂ rewrite incs-seq σ₁ σ₂
    | commute-subst-shift {σ₂} M = refl

exts-seq : ∀ σ₁ σ₂ → exts σ₁ ⨟ exts σ₂ ≡ exts (σ₁ ⨟ σ₂)
exts-seq (↑ k) σ₂ rewrite drop-incs k σ₂ = {!!}
exts-seq (M • σ₁) σ₂ rewrite exts-0 σ₂
    | commute-subst-shift {σ₂} M | incs-seq σ₁ σ₂ = refl

FSS : FusableMap SubstIsMap SubstIsMap SubstIsMap
FSS = record { Q = QSS ; var = λ x σ₁ σ₂ → sym (seq-subst σ₁ σ₂ x)
             ; compose-ext = exts-seq }

sub-sub : ∀ σ₁ σ₂ M → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-sub σ₁ σ₂ M = FusableMap.fusion FSS {_}{σ₁}{σ₂} M
{-# REWRITE sub-sub #-}

sub-assoc : ∀ {σ τ θ} → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
sub-assoc {↑ k} {τ} {θ} rewrite sym (drop-seq k τ θ) = {!!}
sub-assoc {M • σ} {τ} {θ} rewrite sub-assoc {σ}{τ}{θ} = refl
{-# REWRITE sub-assoc #-}

subst-zero : ABT → Subst
subst-zero M = M • id

_[_] : ABT → ABT → ABT
_[_] N M =  ⟪ subst-zero M ⟫ N

subst-zero-exts-cons : ∀{σ M} → exts σ ⨟ subst-zero M ≡ M • σ
subst-zero-exts-cons {σ}{M} rewrite incs=⨟↑ σ = refl

subst-commute : ∀{N M σ} → (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {N}{M}{σ} =
    begin
        (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ]
    ≡⟨⟩
        ⟪ exts σ ⨟ subst-zero (⟪ σ ⟫ M) ⟫ N
    ≡⟨ {!!} {- cong (λ □ → ⟪ □ ⟫ N) subst-zero-exts-cons -} ⟩
        ⟪ subst-zero M ⨟ σ ⟫ N
    ≡⟨⟩
        ⟪ σ ⟫ (N [ M ])
    ∎

commute-subst : ∀{N M σ} → ⟪ σ ⟫ (N [ M ]) ≡ (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ]
commute-subst {N}{M}{σ} = sym (subst-commute {N}{M}{σ})

_〔_〕 : ABT → ABT → ABT
_〔_〕 N M = ⟪ exts (subst-zero M) ⟫ N

substitution : ∀{M N L} → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution {M}{N}{L} = commute-subst{N = M}{M = N}{σ = subst-zero L}

exts-sub-cons : ∀ σ N V → (⟪ exts σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
exts-sub-cons σ N V rewrite exts-cons-shift σ = refl



