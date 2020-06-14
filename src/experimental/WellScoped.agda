open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≤-trans; ≤-step; +-comm; +-suc)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app; subst)

module experimental.WellScoped (Op : Set) (sig : Op → List ℕ) where

open import Var
open import Substitution using (Substable; Rename; ⦉_⦊; ↑; _•_)
open Substitution.ABTOps Op sig
    using (ABT; Arg; Args; RenameIsMap; rename; SubstIsMap; ⟪_⟫; Subst; ⟦_⟧)
open import Preserve Op sig
open import Map Op sig
open import Data.Vec using (Vec) renaming ([] to []̆; _∷_ to _∷̆_)
open ABTPred {I = ⊤} (λ op vs Bs A → ⊤)

mk-list : ℕ → List ⊤
mk-list 0 = []
mk-list (suc n) = tt ∷ mk-list n

WF : ℕ → ABT → Set
WF n M = mk-list n ⊢ M ⦂ tt

mk-btype : (b : ℕ) → BType ⊤ b
mk-btype zero = tt
mk-btype (suc b) = ⟨ tt , (mk-btype b) ⟩

mk-btypes : (bs : List ℕ) → BTypes ⊤ bs
mk-btypes [] = tt
mk-btypes (b ∷ bs) = ⟨ mk-btype b , mk-btypes bs ⟩

mk-vec : (n : ℕ) → Vec ⊤ n
mk-vec zero = []̆
mk-vec (suc n) = tt ∷̆ (mk-vec n)

WF-arg : ℕ → {b : ℕ} → Arg b → Set
WF-arg n {b} arg = b ∣ mk-list n ∣ mk-btype b ⊢a arg ⦂ tt

WF-args : ℕ → {bs : List ℕ} → Args bs → Set 
WF-args n {bs} args = bs ∣ mk-list n ∣ mk-btypes bs ⊢as args ⦂ mk-vec (length bs)

len-mk-list : ∀ Γ → length (mk-list Γ) ≡ Γ
len-mk-list zero = refl
len-mk-list (suc Γ) = cong suc (len-mk-list Γ)

∋x→< : ∀{Γ : List ⊤}{x A} → Γ ∋ x ⦂ A → x < (length Γ)
∋x→< {A ∷ Γ} {zero} {A} ∋x = s≤s z≤n
∋x→< {A ∷ Γ} {suc x} {A} ∋x = s≤s (∋x→< {Γ} ∋x)

<→∋x : ∀{Γ : List ⊤}{x A} → x < (length Γ) → Γ ∋ x ⦂ A
<→∋x {A ∷ Γ} {zero} {A} x<Γ = refl
<→∋x {A ∷ Γ} {suc x} {A} (s≤s x<Γ) = <→∋x {Γ}{x}{A} x<Γ


module _ where
  private
    RenPres : PreserveMap RenameIsMap
    RenPres = record { 𝑃 = λ op vs Bs A → ⊤ ; _⊢v_⦂_ = λ Γ x A → Γ ∋ x ⦂ A
              ; ∋→⊢v-var→val = λ x → x ; ext-⊢v = λ ∋x → ∋x
                ; ⊢v→⊢ = var-p ; ⊢v0 = refl }
    open PreserveMap RenPres using (_⦂_⇒_)

  open PreserveMap RenPres using ()
      renaming (preserve-map to ren-preserve) public

  WFRename : ℕ → Rename → ℕ → Set
  WFRename Γ ρ Δ = ∀ {x} → x < Γ → (⦉ ρ ⦊ x) < Δ

  WFRename→ρ⦂ : ∀ {Γ ρ Δ} → WFRename Γ ρ Δ  →  ρ ⦂ mk-list Γ ⇒ mk-list Δ
  WFRename→ρ⦂ {Γ}{ρ}{Δ} wfΓ {x}{A} ∋x 
      with ∋x→<{mk-list Γ}{x} ∋x
  ... | x<Γ rewrite len-mk-list Γ 
      with wfΓ{x} x<Γ
  ... | x<Δ rewrite sym (len-mk-list Δ)
      with <→∋x{mk-list Δ} x<Δ 
  ... | ∋x' rewrite len-mk-list Δ = ∋x' 

  WF-rename : ∀ {Γ Δ ρ M} → WFRename Γ ρ Δ → WF Γ M → WF Δ (rename ρ M)
  WF-rename {Γ}{Δ}{ρ}{M} wfΓ wfM = ren-preserve wfM (WFRename→ρ⦂ {ρ = ρ} wfΓ)

module _ where
  private
    SubstPres : PreserveMap SubstIsMap
    SubstPres = record { 𝑃 = λ op vs Bs A → ⊤ ; _⊢v_⦂_ = λ Γ M A → Γ ⊢ M ⦂ A
                  ; ∋→⊢v-var→val = λ ∋x → var-p ∋x
                  ; ext-⊢v = λ {A}{B}{Δ}{M} ⊢M → ren-preserve ⊢M λ x → x
                  ; ⊢v→⊢ = λ x → x ; ⊢v0 = λ { {tt}{b} → var-p refl } }
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
          with ∋x→<{mk-list Γ} ∋x
      ... | x<Γ rewrite len-mk-list Γ = wfσ{x} x<Γ

open import AbstractBindingTree Op sig
    using (Ctx; CArg; CArgs; CHole; COp; CAst; CBind; tcons; ccons; 
           plug; plug-arg; plug-args;
           ctx-depth; ctx-depth-arg; ctx-depth-args)

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
    op-p (WF-plug-args{Cs = cargs} wf-cargs wfN ) tt
WF-plug-arg {zero} {CAst C} {N} {k} (WF-c-ast wfC) wfN =
    ast-a (WF-plug wfC wfN)
WF-plug-arg {suc n} {CBind A} {N} {k} (WF-c-bind wfA) wfN =
    bind-a (WF-plug-arg wfA wfN')
    where
    wfN' : WF (suc k + ctx-depth-arg A) N
    wfN' rewrite +-suc k (ctx-depth-arg A) = wfN
WF-plug-args {b ∷ bs} {tcons A Cs refl} {N} {k} (WF-tcons wfA wfCs) wfN =
    cons-a wfA (WF-plug-args {Cs = Cs} wfCs wfN)
WF-plug-args {b ∷ bs} {ccons C As refl} {N} {k} (WF-ccons wfC wfAs) wfN =
    cons-a (WF-plug-arg wfC wfN) wfAs

