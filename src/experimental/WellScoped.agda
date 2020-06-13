open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-step)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)

module experimental.WellScoped (Op : Set) (sig : Op → List ℕ) where

  open import Syntax using (Var; Substable; Rename; ⦉_⦊; ↑; _•_)
  open Syntax.OpSig Op sig using (ABT; RenameIsMap; rename; SubstIsMap; ⟪_⟫)
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
      open PreserveMap RenPres using (_⦂_⇒_; preserve-map)

    WFRename : ℕ → Rename → ℕ → Set
    WFRename Γ ρ Δ = ∀ {x} → x < Γ → (⦉ ρ ⦊ x) < Δ

    WF-rename : ∀ {Γ Δ ρ M} → WFRename Γ ρ Δ → WF Γ M → WF Δ (rename ρ M)
    WF-rename {Γ}{Δ}{ρ}{M} wfΓ wfM = preserve-map wfM wfρ
        where
        wfρ : ρ ⦂ mk-list Γ ⇒ mk-list Δ
        wfρ {x}{A} ∋x
            with ∋x→<{mk-list Γ}{x} ∋x
        ... | x<Γ rewrite len-mk-list Γ 
            with wfΓ{x} x<Γ
        ... | x<Δ rewrite sym (len-mk-list Δ)
            with <→∋x{mk-list Δ} x<Δ 
        ... | ∋x' rewrite len-mk-list Δ = ∋x' 

{-

  module _ where
    private
      V : Set
      V = ABT
      
      𝑃 : (op : Op) → Vec ⊤ (length (sig op)) → BTypes ⊤ (sig op) → ⊤ → Set
      𝑃 op vs Bs A = ⊤

      open import AbstractBindingTree Op sig
      open ABTPred 𝑃

      _⊢v_⦂_ : List ⊤ → V → ⊤ → Set
      Γ ⊢v M ⦂ A = Γ ⊢ M ⦂ A
      
      ∋→⊢v-var→val : ∀ {Γ x A} → Γ ∋ x ⦂ A → Γ ⊢v ` x ⦂ A
      ∋→⊢v-var→val ∋x = var-p ∋x

      open PreserveMap SubstIsMap 𝑃 _⊢v_⦂_ (λ {Γ}{x}{A} → ∋→⊢v-var→val{Γ}{x}{A})
      open Substable (Map.S SubstIsMap)
      open Map SubstIsMap
      
      ext-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
      ext-⊢v {v = x} ∋x = {!!}
-}
