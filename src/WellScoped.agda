{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _+_; _≤?_)
open import Data.Nat.Properties using (≤-trans; ≤-step; +-comm; +-suc; ≤-pred)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Agda.Primitive using (Level; lzero; lsuc)
open import Sig
open import Substitution using (Rename; ↑; _•_)
open import Structures
open import Var

{----------------------------------------------------------------------------
                  Well-scoped Abstract Binding Trees
 ---------------------------------------------------------------------------}

module WellScoped (Op : Set) (sig : Op → List Sig) where

open Substitution.ABTOps Op sig
    using (rename; ⟪_⟫; Subst; ABT-is-Shiftable)

private
  𝑉 : ∀{ℓ} → List {ℓ} ⊤ → Var → ⊤ {ℓ} → ⊤ {ℓ} → Set
  𝑉 = λ Γ x A B → suc x ≤ length Γ

  𝑃 : ∀{ℓ}(op : Op) → Vec{ℓ} ⊤ (length (sig op))
    → BTypes {lzero} ⊤ (sig op) → ⊤ {ℓ}
    → Set
  𝑃 = λ op vs Bs A → ⊤

open import MapPreserve Op sig ⊤ 𝑉 𝑃

open import Map Op sig
open import Data.Vec using (Vec) renaming ([] to []̆; _∷_ to _∷̆_)
open import ABTPredicate {ℓ = lzero}{I = ⊤} Op sig
  (λ Γ x A B → x < length Γ) (λ op vs Bs A → ⊤)
  hiding (var-p; op-p; ast-p; bind-p; nil-p; cons-p)
open import ABTPredicate {ℓ = lzero} {I = ⊤} Op sig
  (λ Γ x A B → x < length Γ) (λ op vs Bs A → ⊤)
  using ()
  renaming (var-p to WF-var; op-p to WF-op; ast-p to WF-ast; bind-p to WF-bind;
            clear-p to WF-clear; nil-p to WF-nil; cons-p to WF-cons) public

open import AbstractBindingTree Op sig
  using (ABT; Arg; Args; `_; _⦅_⦆; ast; bind; clear; nil; cons; Quotable;
  Var-is-Quotable; ABT-is-Quotable)

mk-list : {ℓ : Level} → ℕ → List {ℓ} ⊤
mk-list 0 = []
mk-list (suc n) = tt ∷ mk-list n

WF : ℕ → ABT → Set
WF n M = mk-list n ⊢ M ⦂ tt

mk-btype : (b : Sig) → BType {lzero} ⊤ b
mk-btype ■ = tt
mk-btype (ν b) = ⟨ tt , (mk-btype b) ⟩
mk-btype (∁ b) = mk-btype b

mk-btypes : (bs : List Sig) → BTypes {lzero} ⊤ bs
mk-btypes [] = tt
mk-btypes (b ∷ bs) = ⟨ mk-btype b , mk-btypes bs ⟩

mk-vec : {ℓ : Level} → (n : ℕ) → Vec {ℓ} ⊤ n 
mk-vec zero = []̆
mk-vec (suc n) = tt ∷̆ (mk-vec n)

WF-arg : ℕ → {b : Sig} → Arg b → Set
WF-arg n {b} arg = b ∣ mk-list n ∣ mk-btype b ⊢ₐ arg ⦂ tt

WF-args : ℕ → {bs : List Sig} → Args bs → Set 
WF-args n {bs} args = bs ∣ mk-list n ∣ mk-btypes bs ⊢₊ args ⦂ mk-vec (length bs)

len-mk-list : ∀ {ℓ : Level} n → length {ℓ} (mk-list n) ≡ n
len-mk-list zero = refl
len-mk-list (suc n) = cong suc (len-mk-list n)

mk-btype-unique : ∀{b : Sig}{Bs : BType ⊤ b}
    → Bs ≡ mk-btype b
mk-btype-unique {■} {tt} = refl
mk-btype-unique {ν b} {⟨ fst , snd ⟩} = cong₂ ⟨_,_⟩ refl (mk-btype-unique {b})
mk-btype-unique {∁ b} {Bs} = mk-btype-unique {b}{Bs}

mk-btypes-unique : ∀{bs : List Sig}{Bss : BTypes ⊤ bs}
    → Bss ≡ mk-btypes bs
mk-btypes-unique {[]} {tt} = refl
mk-btypes-unique {b ∷ bs} {⟨ fst , snd ⟩} =
    cong₂ ⟨_,_⟩ (mk-btype-unique {b}) mk-btypes-unique

mk-vec-unique : ∀{ℓ : Level}{n : ℕ}{vs : Vec {ℓ} ⊤ n} → vs ≡ mk-vec n
mk-vec-unique {ℓ}{zero} {[]̆} = refl
mk-vec-unique {ℓ}{suc n} {v ∷̆ vs} = cong₂ _∷̆_ refl mk-vec-unique

module _ where
  instance
    RenPres : MapPreservable Var
    RenPres = record { _⊢v_⦂_ = λ Γ x A → Γ ∋ x ⦂ A
              ; ⊢v-var→val0 = refl
              ; shift-⊢v = λ z → z
              ; quote-⊢v = λ {Γ}{x}{tt} ∋x → WF-var ∋x (∋x→< {Γ = Γ} ∋x)
              ; 𝑉-⊢v = λ { {x}{_}{tt}{tt} le ∋x → ∋x } }

  ren-preserve : ∀ {Γ Δ : List ⊤}{σ : Rename}{A : ⊤}{M : ABT}
   → Γ ⊢ M ⦂ A  →  σ ⦂ Γ ⇒ Δ  →  Δ ⊢ map σ M ⦂ A
  ren-preserve {σ = σ}{M = M} ⊢M σ⦂ = preserve-map M ⊢M σ⦂

  WFRename : ℕ → Rename → ℕ → Set
  WFRename Γ ρ Δ = ∀ {x} → x < Γ → (ρ x) < Δ

  WFRename→ρ⦂ : ∀{Γ ρ Δ} → WFRename Γ ρ Δ  →  ρ ⦂ mk-list Γ ⇒ mk-list Δ
  WFRename→ρ⦂ {Γ}{ρ}{Δ} wfΓ {x}{tt} ∋x  
      with ∋x→< {Γ = mk-list Γ}{x} ∋x
  ... | x<Γ rewrite len-mk-list {lzero} Γ
      with wfΓ{x} x<Γ
  ... | x<Δ rewrite sym (len-mk-list {lzero} Δ)
      with <→∋x {Γ = mk-list Δ} x<Δ 
  ... | ∋x' rewrite len-mk-list {lzero} Δ = ∋x'

  WF-rename : ∀ {Γ Δ ρ M} → WFRename Γ ρ Δ → WF Γ M → WF Δ (rename ρ M)
  WF-rename {Γ}{Δ}{ρ}{M} wfΓ wfM = ren-preserve wfM (WFRename→ρ⦂ {ρ = ρ} wfΓ)

module _ where
  instance
    SubstPres : MapPreservable ABT
    SubstPres = record { _⊢v_⦂_ = λ Γ M A → Γ ⊢ M ⦂ A
                ; ⊢v-var→val0 = λ {tt} → WF-var refl (s≤s z≤n)
                ; quote-⊢v = λ x → x
                ; shift-⊢v = λ {A}{B}{Δ}{v} ⊢v →
                    ren-preserve ⊢v (λ {x}{tt} ∋x → ∋x)
                ; 𝑉-⊢v = λ {x}{M}{tt}{tt} Vx ⊢M → ⊢M }

  sub-preserve : ∀ {Γ Δ : List ⊤}{σ : Subst}{A : ⊤}{M : ABT}
   → Γ ⊢ M ⦂ A  →  σ ⦂ Γ ⇒ Δ  →  Δ ⊢ map σ M ⦂ A
  sub-preserve {M = M} ⊢M σ⦂ = preserve-map M ⊢M σ⦂ 

  WFSubst : ℕ → Subst → ℕ → Set
  WFSubst Γ σ Δ = ∀ {x} → x < Γ → WF Δ (σ x)

  WF-subst : ∀{Γ Δ σ M} → WFSubst Γ σ Δ → WF Γ M → WF Δ (⟪ σ ⟫ M)
  WF-subst {Γ}{Δ}{σ}{M} wfσ wfM = sub-preserve wfM σ⦂ 
      where
      σ⦂ : σ ⦂ mk-list Γ ⇒ mk-list Δ
      σ⦂ {x}{tt} ∋x 
          with ∋x→< {Γ = mk-list Γ} ∋x
      ... | x<Γ rewrite len-mk-list {lzero} Γ = wfσ{x} x<Γ

open import AbstractBindingTree Op sig
    using (Ctx; CArg; CArgs; CHole; COp; CAst; CBind; CClear; tcons; ccons; 
           plug; plug-arg; plug-args;
           ctx-depth; ctx-depth-arg; ctx-depth-args)

data WF-Ctx : ℕ → Ctx → Set
data WF-CArg : ℕ → ∀{b : Sig} → CArg b → Set
data WF-CArgs : ℕ → ∀{bs : List Sig} → CArgs bs → Set

data WF-Ctx where
  WF-hole : ∀{n} → WF-Ctx n CHole
  WF-c-op : ∀{n}{op}{cargs : CArgs (sig op)}
     → WF-CArgs n cargs
     → WF-Ctx n (COp op cargs)

data WF-CArg where
  WF-c-ast : ∀{n}{C : Ctx}
     → WF-Ctx n C
     → WF-CArg n (CAst C)
  WF-c-bind : ∀{n}{b}{CA : CArg b}
     → WF-CArg (suc n) {b} CA
     → WF-CArg n (CBind {b} CA)
  WF-c-clear : ∀{n}{b}{CA : CArg b}
     → WF-CArg 0 {b} CA
     → WF-CArg n (CClear {b} CA)

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
   → WF (ctx-depth C k) N
   → WF k (plug C N)
WF-plug-arg : ∀{b}{A : CArg b}{N : ABT}{k}
   → WF-CArg k A
   → WF (ctx-depth-arg A k) N
   → WF-arg k (plug-arg A N)
WF-plug-args : ∀{bs}{Cs : CArgs bs}{N : ABT}{k}
   → WF-CArgs k Cs
   → WF (ctx-depth-args Cs k) N
   → WF-args k (plug-args Cs N)

WF-plug {CHole} {N} {k} wfC wfN
    rewrite +-comm k 0 = wfN
WF-plug {COp op cargs} {N} {k} (WF-c-op wf-cargs) wfN =
    WF-op (WF-plug-args{Cs = cargs} wf-cargs wfN ) tt
WF-plug-arg {■} {CAst C} {N} {k} (WF-c-ast wfC) wfN =
    WF-ast (WF-plug wfC wfN)
WF-plug-arg {ν n} {CBind A} {N} {k} (WF-c-bind wfA) wfN =
    WF-bind (WF-plug-arg wfA wfN)
WF-plug-arg {∁ n} {CClear A} {N} {k} (WF-c-clear wfA) wfN = 
    WF-clear (WF-plug-arg wfA wfN)
WF-plug-args {b ∷ bs} {tcons A Cs refl} {N} {k} (WF-tcons wfA wfCs) wfN =
    WF-cons wfA (WF-plug-args {Cs = Cs} wfCs wfN)
WF-plug-args {b ∷ bs} {ccons C As refl} {N} {k} (WF-ccons wfC wfAs) wfN =
    WF-cons (WF-plug-arg wfC wfN) wfAs


WF? : (n : ℕ) → (M : ABT) → Dec (WF n M)
WF-arg? : (n : ℕ) → {b : Sig} → (A : Arg b) → Dec (WF-arg n A)
WF-args? : (n : ℕ) → {bs : List Sig} → (As : Args bs) → Dec (WF-args n As)
WF? n (` x)
    with suc x ≤? n
... | yes x<n =
      let x<ln = subst (λ □ → x < □) (sym (len-mk-list n)) x<n in
      yes (WF-var (<→∋x {Γ = mk-list n} x<ln) x<ln)
WF? n (` x) | no ¬x<n = no G
    where G : ¬ WF n (` x)
          G (WF-var ∋x lt) =
            ¬x<n (subst (λ □ → x < □) (len-mk-list n) lt)
WF? n (op ⦅ args ⦆)
    with WF-args? n args
... | yes wf = yes (WF-op wf _)
... | no ¬wf = no G
    where G : ¬ WF n (op ⦅ args ⦆)
          G (WF-op {Γ}{_}{_}{A}{As}{Bs} wf _)
            rewrite mk-btypes-unique {sig op}{Bs}
            | mk-vec-unique {_}{length (sig op)}{As} = ¬wf wf
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
WF-arg? n (clear arg)
    with WF-arg? 0 arg
... | yes wf = yes (WF-clear wf)
... | no ¬wf = no G
    where G : ¬ WF-arg n (clear arg)
          G (WF-clear wf) = ¬wf wf
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
