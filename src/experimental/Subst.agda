{-# OPTIONS --rewriting #-} 

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.List using (List; []; _∷_)
open import GenericSubstitution
open import experimental.ScopedTuple using (Sig; Tuple; map; tuple-pred)
open import Size using (Size)

module experimental.Subst (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig

Subst : Set
Subst = Substitution ABT

subst-zero : ABT → Subst
subst-zero M = M • id

open import experimental.Rename Op sig using (rename)

SubstIsSubstable : Substable ABT
SubstIsSubstable = record { var→val = `_ ; shift = rename (↑ 1)
    ; var→val-suc-shift = λ {x} → refl }
    
open import experimental.Map Op sig

SubstIsMap : Map ABT
SubstIsMap = record { “_” = λ M → M ; S = SubstIsSubstable }
open Map SubstIsMap renaming (map-abt to ⟪_⟫; map-arg to ⟪_⟫ₐ) public
⟪_⟫₊ : ∀{s : Size} → Substitution ABT →(bs : Sig)→ Tuple bs (λ _ → Term s)
     → Tuple bs (λ _ → ABT)
⟪_⟫₊ = λ σ bs → map (λ {b} → ⟪ σ ⟫ₐ b) {bs}
open ComposeMaps SubstIsMap SubstIsMap ⟪_⟫ (λ x → x)
    using (_⨟_) public

{-
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Binary.HeterogeneousEquality
    using (_≅_; ≅-to-≡; reflexive)
    renaming (cong to hcong)
open import Var


open GenericSubst (Map.S SubstIsMap) using ()
    renaming (⧼_⧽ to ⟦_⟧; g-ext to exts) public
open GenericSubst (Map.S SubstIsMap) using (Shift; shift-up; shift-•)
    renaming (g-inc to incs; g-inc-shift to incs-rename;
    g-drop-inc to drop-incs; g-drop-add to drop-add; g-drop-ext to drop-exts;
    g-Shift-var to sub-shift-var;
    g-inc-Shift to incs-Shift; g-ext-cong to exts-cong)
{- REWRITE map-sub-id -}

{-

private {- making sure the following equations are all refl's -}
  sub-head : ∀ M σ → ⟦ M • σ ⟧ 0 ≡ M
  sub-head M σ = refl
-}

private
  sub-tail : ∀ M σ → (↑ 1 ⨟ M • σ) ≡ σ
  sub-tail M σ rewrite g-drop-0 σ | compose-up 1 (M • σ) = {!!}
{-

  sub-suc : ∀ M σ x → ⟪ M • σ ⟫ (` suc x) ≡ ⟪ σ ⟫ (` x)
  sub-suc M σ x = refl

  shift-eq : ∀ x k → ⟪ ↑ k ⟫ (` x) ≡ ` (k + x)
  shift-eq x k = refl

  sub-idL : (σ : Subst) → id ⨟ σ ≡ σ
  sub-idL σ rewrite g-drop-0 σ | g-map-sub-id σ = refl

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

{- INTERNAL ERROR
g-map-sub-id (drop 1 σ)
-}
sub-η : ∀ (σ : Subst) (x : Var)  →  ⟦ ⟪ σ ⟫ (` 0) • (↑ 1 ⨟ σ) ⟧ x ≡ ⟦ σ ⟧ x
sub-η σ 0 = refl
sub-η σ (suc x) =
  begin
      ⟦ ⟪ σ ⟫ (` 0) • (↑ 1 ⨟ σ) ⟧ (suc x)
  {-
  ≡⟨ {!!} ⟩
      ⟦ g-map-sub (λ x → x) (drop 1 σ) ⟧ x
  -}
  ≡⟨ {!!} ⟩
      ⟦ drop 1 σ ⟧ x
  ≡⟨ drop-add 1 σ ⟩
      ⟦ σ ⟧ (suc x)
  ∎





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
seq-subst (↑ k) τ x rewrite compose-up k τ = drop-add k τ
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
{- REWRITE sub-id -}

rename-id : {M : ABT} → rename (↑ 0) M ≡ M
rename-id {M} rewrite rename-subst (↑ 0) M | sub-id M = refl
{- REWRITE rename-id -}

sub-idR : ∀ σ → σ ⨟ id ≡ σ 
sub-idR (↑ k) rewrite +-comm k 0 = refl
sub-idR (M • σ) rewrite sub-idR σ | sub-id M = refl
{- REWRITE sub-idR -}

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

postulate compose-incs-ext : ∀ σ ρ → (incs σ ⨟ˢᵣ ext ρ) ≡ incs (σ ⨟ˢᵣ ρ)
{- INTERNAL ERROR
compose-incs-ext (↑ k) ρ
    rewrite dropr-inc k ρ | Quotable.g-map-sub-inc QSR (drop k ρ) = refl
compose-incs-ext (M • σ) ρ = cong₂ _•_ (commute-↑1 ρ M) (compose-incs-ext σ ρ)
-}

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
compose-inc-exts (↑ k) σ {- drop-incs k σ -} = {!!}
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

commute-subst-shift : ∀{σ : Subst} (M : ABT)
   → ⟪ exts σ ⟫ (rename (↑ 1) M) ≡ rename (↑ 1) (⟪ σ ⟫ M)
commute-subst-shift {σ} M =
  begin
      ⟪ exts σ ⟫ (rename (↑ 1) M)
  ≡⟨ compose-sub-ren (exts σ) (↑ 1) M ⟩
      ⟪ (↑ 1) ⨟ᵣˢ exts σ ⟫ M
  ≡⟨ {!!} ⟩
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
incs-seq (↑ k) σ₂ rewrite
      drop-exts k σ₂ = {!!}
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
{- REWRITE sub-sub -}

postulate sub-assoc : ∀ {σ τ θ} → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
{-
sub-assoc {↑ k} {τ} {θ} rewrite compose-up k (τ ⨟ θ)
  | g-map-sub-id (dropr k τ) = sym (drop-seq k τ θ)
sub-assoc {M • σ} {τ} {θ} rewrite sub-assoc {σ}{τ}{θ} = ?
-}
{- REWRITE sub-assoc -}

_[_] : ABT → ABT → ABT
_[_] N M =  ⟪ subst-zero M ⟫ N

subst-zero-exts-cons : ∀{σ M} → exts σ ⨟ subst-zero M ≡ M • σ
subst-zero-exts-cons {σ}{M} rewrite incs=⨟↑ σ = {!!}

subst-commute : ∀{N M σ} → (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {N}{M}{σ} =
    begin
        (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ]
    ≡⟨ {!!} ⟩
        ⟪ exts σ ⨟ subst-zero (⟪ σ ⟫ M) ⟫ N
    ≡⟨ {!!} {- cong (λ □ → ⟪ □ ⟫ N) subst-zero-exts-cons -}  ⟩
        ⟪ subst-zero M ⨟ σ ⟫ N
    ≡⟨ {!!} ⟩
        ⟪ σ ⟫ (N [ M ])
    ∎

commute-subst : ∀{N M σ} → ⟪ σ ⟫ (N [ M ]) ≡ (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ]
commute-subst {N}{M}{σ} = sym (subst-commute {N}{M}{σ})

_〔_〕 : ABT → ABT → ABT
_〔_〕 N M = ⟪ exts (subst-zero M) ⟫ N

substitution : ∀{M N L} → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution {M}{N}{L} = commute-subst{N = M}{M = N}{σ = subst-zero L}

exts-sub-cons : ∀ σ N V → (⟪ exts σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
exts-sub-cons σ N V rewrite exts-cons-shift σ = {!!} {- refl -}


-}
-}
