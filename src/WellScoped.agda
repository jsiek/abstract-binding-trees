open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-step)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app; subst)

module WellScoped (Op : Set) (sig : Op → List ℕ) where

  open import Var
  open import Substitution using (Substable; Rename; ⦉_⦊; ↑; _•_)
  open Substitution.OpSig Op sig
      using (ABT; RenameIsMap; rename; SubstIsMap; ⟪_⟫; Subst; ⟦_⟧)
  open import Preserve Op sig
  open import Map Op sig
  open import Data.Vec using (Vec) renaming ([] to []̆; _∷_ to _∷̆_)
  open ABTPred {I = ⊤} (λ op vs Bs A → ⊤)

  mk-list : ℕ → List ⊤
  mk-list 0 = []
  mk-list (suc n) = tt ∷ mk-list n

  WF : ℕ → ABT → Set
  WF n M = mk-list n ⊢ M ⦂ tt

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

    WF-rename : ∀ {Γ Δ ρ M} → WFRename Γ ρ Δ → WF Γ M → WF Δ (rename ρ M)
    WF-rename {Γ}{Δ}{ρ}{M} wfΓ wfM = ren-preserve wfM wfρ
        where
        wfρ : ρ ⦂ mk-list Γ ⇒ mk-list Δ
        wfρ {x}{A} ∋x
            with ∋x→<{mk-list Γ}{x} ∋x
        ... | x<Γ rewrite len-mk-list Γ 
            with wfΓ{x} x<Γ
        ... | x<Δ rewrite sym (len-mk-list Δ)
            with <→∋x{mk-list Δ} x<Δ 
        ... | ∋x' rewrite len-mk-list Δ = ∋x' 

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
