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

module Syntax where

open import Var public

open import Substitution public

module OpSig (Op : Set) (sig : Op → List ℕ)  where

  open ABTOps Op sig public

  {----------------------------------------------------------------------------
    Well-formed Abstract Binding Trees
   ---------------------------------------------------------------------------}

  {- TODO: add context stuff to WellScoped.agda, then remove this. -Jeremy -}

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

