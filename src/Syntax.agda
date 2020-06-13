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

module Extra (Op : Set) (sig : Op → List ℕ)  where

  open OpSig Op sig

  open import WellScoped Op sig

{- NEEDS TO BE UPDATED -Jeremy
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
-}

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

  {- NEEDS TO BE UPDATED to new defs in WellScoped -Jeremy
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
  -}
  
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

