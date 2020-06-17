open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _+_; _≤?_)
open import Data.Nat.Properties using (≤-trans; ≤-step; +-comm; +-suc)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Agda.Primitive using (Level; lzero; lsuc)


{----------------------------------------------------------------------------
                  Well-scoped Abstract Binding Trees
 ---------------------------------------------------------------------------}

module WellScoped (Op : Set) (sig : Op → List ℕ) where

open import Var
open import Substitution using (Shiftable; Rename; ⦉_⦊; ↑; _•_)
open Substitution.ABTOps Op sig
    using (ABT; Arg; Args; RenameIsMap; rename; SubstIsMap; ⟪_⟫; Subst; ⟦_⟧)
open import Preserve Op sig
open import Map Op sig
open import Data.Vec using (Vec) renaming ([] to []̆; _∷_ to _∷̆_)
open ABTPred {I = ⊤} (λ Γ x A → x < length Γ) (λ op vs Bs A → ⊤)
  hiding (var-p; op-p; ast-p; bind-p; nil-p; cons-p)
open ABTPred {I = ⊤} (λ Γ x A → x < length Γ) (λ op vs Bs A → ⊤)
  using ()
  renaming (var-p to WF-var; op-p to WF-op; ast-p to WF-ast; bind-p to WF-bind;
            nil-p to WF-nil; cons-p to WF-cons) public

mk-list : {ℓ : Level} → ℕ → List {ℓ} ⊤
mk-list 0 = []
mk-list (suc n) = tt ∷ mk-list n

WF : ℕ → ABT → Set
WF n M = mk-list n ⊢ M ⦂ tt

open import AbstractBindingTree Op sig using (`_; _⦅_⦆; ast; bind; nil; cons)

mk-btype : (b : ℕ) → BType ⊤ b
mk-btype zero = tt
mk-btype (suc b) = ⟨ tt , (mk-btype b) ⟩

mk-btypes : (bs : List ℕ) → BTypes ⊤ bs
mk-btypes [] = tt
mk-btypes (b ∷ bs) = ⟨ mk-btype b , mk-btypes bs ⟩

mk-vec : {ℓ : Level} → (n : ℕ) → Vec {ℓ} ⊤ n 
mk-vec zero = []̆
mk-vec (suc n) = tt ∷̆ (mk-vec n)

WF-arg : ℕ → {b : ℕ} → Arg b → Set
WF-arg n {b} arg = b ∣ mk-list n ∣ mk-btype b ⊢ₐ arg ⦂ tt

WF-args : ℕ → {bs : List ℕ} → Args bs → Set 
WF-args n {bs} args = bs ∣ mk-list n ∣ mk-btypes bs ⊢₊ args ⦂ mk-vec (length bs)

len-mk-list : ∀ {ℓ : Level} n → length {ℓ} (mk-list n) ≡ n
len-mk-list zero = refl
len-mk-list (suc n) = cong suc (len-mk-list n)

mk-btype-unique : ∀{b : ℕ}{Bs : BType ⊤ b}
    → Bs ≡ mk-btype b
mk-btype-unique {zero} {tt} = refl
mk-btype-unique {suc b} {⟨ fst , snd ⟩} = cong₂ ⟨_,_⟩ refl mk-btype-unique

mk-btypes-unique : ∀{bs : List ℕ}{Bss : BTypes ⊤ bs}
    → Bss ≡ mk-btypes bs
mk-btypes-unique {[]} {tt} = refl
mk-btypes-unique {b ∷ bs} {⟨ fst , snd ⟩} =
    cong₂ ⟨_,_⟩ (mk-btype-unique {b}) mk-btypes-unique

mk-vec-unique : ∀{ℓ : Level}{n : ℕ}{vs : Vec {ℓ} ⊤ n} → vs ≡ mk-vec n
mk-vec-unique {ℓ}{zero} {[]̆} = refl
mk-vec-unique {ℓ}{suc n} {v ∷̆ vs} = cong₂ _∷̆_ refl mk-vec-unique


module _ where
  private
    RenPres : PreserveMap RenameIsMap
    RenPres = record { 𝑃 = λ op vs Bs A → ⊤ ; _⊢v_⦂_ = λ Γ x A → Γ ∋ x ⦂ A
              ; 𝑉 = λ Γ x A → suc x ≤ length Γ
              ; shift-⊢v = λ ∋x → ∋x ; ⊢v0 = refl
              ; quote-⊢v = λ {Γ}{x}{tt} ∋x → WF-var ∋x (∋x→< {⊤}{Γ} ∋x) }
    open PreserveMap RenPres using (_⦂_⇒_)

  open PreserveMap RenPres using ()
      renaming (preserve-map to ren-preserve) public

  WFRename : ℕ → Rename → ℕ → Set
  WFRename Γ ρ Δ = ∀ {x} → x < Γ → (⦉ ρ ⦊ x) < Δ

  WFRename→ρ⦂ : ∀{Γ ρ Δ} → WFRename Γ ρ Δ  →  ρ ⦂ mk-list Γ ⇒ mk-list Δ
  WFRename→ρ⦂ {Γ}{ρ}{Δ} wfΓ {x}{A} ∋x 
      with ∋x→< {_}{mk-list Γ}{x} ∋x
  ... | x<Γ rewrite len-mk-list {lzero} Γ
      with wfΓ{x} x<Γ
  ... | x<Δ rewrite sym (len-mk-list {lzero} Δ)
      with <→∋x {⊤}{mk-list Δ} x<Δ 
  ... | ∋x' rewrite len-mk-list {lzero} Δ = ∋x' 

  WF-rename : ∀ {Γ Δ ρ M} → WFRename Γ ρ Δ → WF Γ M → WF Δ (rename ρ M)
  WF-rename {Γ}{Δ}{ρ}{M} wfΓ wfM = ren-preserve wfM (WFRename→ρ⦂ {ρ = ρ} wfΓ)

module _ where
  private
    SubstPres : PreserveMap SubstIsMap
    SubstPres = record { 𝑃 = λ op vs Bs A → ⊤ ; _⊢v_⦂_ = λ Γ M A → Γ ⊢ M ⦂ A
                  ; 𝑉 = λ Γ x A → suc x ≤ length Γ 
                  ; shift-⊢v = λ {A}{B}{Δ}{M} ⊢M → ren-preserve ⊢M λ x → x
                  ; quote-⊢v = λ x → x ; ⊢v0 = λ{ {tt} → WF-var refl (s≤s z≤n)}}
    open PreserveMap SubstPres using (_⦂_⇒_)

  open PreserveMap SubstPres using ()
      renaming (preserve-map to sub-preserve) public

  WFSubst : ℕ → Subst → ℕ → Set
  WFSubst Γ σ Δ = ∀ {x} → x < Γ → WF Δ (⟦ σ ⟧ x)

  WF-subst : ∀{Γ Δ σ M} → WFSubst Γ σ Δ → WF Γ M → WF Δ (⟪ σ ⟫ M)
  WF-subst {Γ}{Δ}{σ}{M} wfσ wfM = sub-preserve wfM σ⦂
      where
      σ⦂ : σ ⦂ mk-list Γ ⇒ mk-list Δ
      σ⦂ {x}{tt} ∋x
          with ∋x→< {⊤}{mk-list Γ} ∋x
      ... | x<Γ rewrite len-mk-list {lzero} Γ = wfσ{x} x<Γ

open import AbstractBindingTree Op sig
    using (Ctx; CArg; CArgs; CHole; COp; CAst; CBind; tcons; ccons; 
           plug; plug-arg; plug-args;
           ctx-depth; ctx-depth-arg; ctx-depth-args)

data WF-Ctx : ℕ → Ctx → Set
data WF-CArg : ℕ → ∀{b} → CArg b → Set
data WF-CArgs : ℕ → ∀{bs} → CArgs bs → Set

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
WF-plug {COp op cargs} {N} {k} (WF-c-op wf-cargs) wfN =
    WF-op (WF-plug-args{Cs = cargs} wf-cargs wfN ) tt
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


WF? : (n : ℕ) → (M : ABT) → Dec (WF n M)
WF-arg? : (n : ℕ) → {b : ℕ} → (A : Arg b) → Dec (WF-arg n A)
WF-args? : (n : ℕ) → {bs : List ℕ} → (As : Args bs) → Dec (WF-args n As)
WF? n (` x)
    with suc x ≤? n
... | yes x<n =
      let x<ln = subst (λ □ → x < □) (sym (len-mk-list n)) x<n in
      yes (WF-var (<→∋x {⊤}{mk-list n} x<ln) x<ln)
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
