
{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
  renaming (subst to eq-subst)

module Generic where

import AbstractBindingTree
open import Fold
open import Preserve
open import Simulate
open import Substitution
open import Var

{--------------------------------------------

 Example: Renaming, Substitution, and a Lemma

 --------------------------------------------}

module GenericSubstPres (V : Set) (var→val : Var → V) (shift : V → V)
  (Op : Set) (sig : Op → List ℕ) {I : Set}
  (𝒫 : Op → List I → I → Set)
  (_⊢v_⦂_ : List I → V → I → Set)
  (⊢var→val : ∀{Δ : List I}{x : Var}{A : I} → (Δ ∋ x ⦂ A) → Δ ⊢v var→val x ⦂ A)
  (val→abt : V → AbstractBindingTree.ABT Op sig)
  (⊢val→abt : ∀{Δ v A} → Δ ⊢v v ⦂ A → ABTPred._⊢_⦂_ Op sig 𝒫 Δ (Foldable.ret (GenericSubst.gen-subst-is-foldable V var→val shift Op sig val→abt) v) A)
  (⊢shift : ∀{Δ A B σ x} → Δ ⊢v GenericSub.⧼_⧽ V var→val shift σ x ⦂ B → (A ∷ Δ) ⊢v shift (GenericSub.⧼_⧽ V var→val shift σ x) ⦂ B)
  (var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x))
  where

  open AbstractBindingTree Op sig
  open GenericSub V var→val shift hiding (extend)
  open GenericSubst V var→val shift Op sig val→abt
  open ArgResult V ABT
  open ABTPred Op sig 𝒫
  open PresArgResult Op sig {V}{ABT} 𝒫 _⊢v_⦂_ _⊢_⦂_

  res→arg : ∀{Δ : List I}{b}{R : ArgRes b}{A : I}
     → b ∣ Δ ⊢r R ⦂ A
     → b ∣ Δ ⊢a s-arg R ⦂ A
  res→arg {Δ} {zero} {R} {A} (ast-r ⊢R) = ast-a ⊢R
  res→arg {Δ} {suc b} {R} {A} (bind-r f) =
      bind-a (res→arg (f (⊢var→val refl)))
  
  res→args : ∀{Δ}{bs}{Rs : ArgsRes bs}{As : List I}
     → bs ∣ Δ ⊢rs Rs ⦂ As
     → bs ∣ Δ ⊢as s-args Rs ⦂ As
  res→args {Δ} {[]} {.rnil} {.[]} nil-r = nil-a
  res→args {Δ} {b ∷ bs} {.(rcons _ _)} {.(_ ∷ _)} (cons-r ⊢R ⊢Rs) =
      cons-a (res→arg ⊢R) (res→args ⊢Rs)

  open Foldable gen-subst-is-foldable
  
  op-pres : ∀ {op : Op}{Rs : ArgsRes (sig op)}{Δ : List I}{A : I}{As : List I}
     → sig op ∣ Δ ⊢rs Rs ⦂ As
     → 𝒫 op As A
     → Δ ⊢ (fold-op op Rs) ⦂ A
  op-pres {op}{Rs}{Δ}{A}{As} ⊢Rs 𝒫op =
      let ⊢sargs = (eq-subst (λ □ → sig op ∣ □ ⊢as s-args Rs ⦂ As) refl
                            (res→args ⊢Rs)) in
      op-op ⊢sargs 𝒫op

  _⦂_⇒_ : Substitution V → List I → List I → Set
  _⦂_⇒_ ρ Γ Δ = ∀ {x}{A} → Γ ∋ x ⦂ A → Δ ⊢v ⧼ ρ ⧽ x ⦂ A
  
  extend-pres : ∀ {v : V}{σ}{Γ}{Δ}{A}
     → (A ∷ Δ) ⊢v v ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → (extend σ v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  extend-pres {v} {σ} {Γ} {Δ} {A} ∋v σΓΔ {zero} {B} refl = ∋v
  extend-pres {v} {σ} {Γ} {Δ} {A} ∋v σΓΔ {suc x} {B} ∋x
      rewrite inc-suc σ x =
      ⊢shift {σ = σ} (σΓΔ ∋x)

  gen-subst-is-preservable : Preservable I gen-subst-is-foldable
  gen-subst-is-preservable = record { 𝒫 = 𝒫 ; _⦂_⇒_ = _⦂_⇒_ ; _⊢v_⦂_ = _⊢v_⦂_
   ; _⊢c_↝_⦂_ = ? {- _⊢_⦂_ -}
   ; lookup-pres = λ σΓΔ Γ∋x → σΓΔ Γ∋x ; extend-pres = extend-pres
   ; ret-pres = ⊢val→abt ; var-pres = λ Γ∋x → ⊢var→val Γ∋x ; op-pres = op-pres }
  open Preservation gen-subst-is-foldable gen-subst-is-preservable public


module RenamePres (Op : Set) (sig : Op → List ℕ) {I : Set}
  (𝒫 : Op → List I → I → Set) where
  open AbstractBindingTree Op sig using (`_)
  open GenericSubstPres Var (λ x → x) suc Op sig 𝒫 _∋_⦂_ (λ {Δ} {x} {A} z → z)
       `_ ABTPred.var-p (λ {Δ} {A} {B} {σ} {x} z → z) (λ {x} → refl) public


module SubstPres (Op : Set) (sig : Op → List ℕ) {I : Set}
  (𝒫 : Op → List I → I → Set) where
  open AbstractBindingTree Op sig using (ABT; `_)
  open Rename Op sig using (rename)
  open ABTPred Op sig 𝒫
  open RenamePres Op sig 𝒫 renaming (preserve to rename-preserve)
  open GenericSubstPres ABT `_ (rename (↑ 1)) Op sig 𝒫 _⊢_⦂_ var-p (λ M → M)
          (λ {Δ} {v} {A} z → z)
          (λ ⊢M → (rename-preserve {σ = ↑ 1} ⊢M λ {x} {A} z → z))
          (λ {x} → refl) public

module TestRenameSubstOnLambda where

  data Op : Set where
    op-lam : Op
    op-app : Op

  sig : Op → List ℕ
  sig op-lam = 1 ∷ []
  sig op-app = 0 ∷ 0 ∷ []

  open AbstractBindingTree Op sig

  infix 6 ƛ_
  pattern ƛ_ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

  infixl 7  _·_
  pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
  
  M₀ : ABT
  M₀ = (` 0) · (` 1)

  M₁ : ABT
  M₁ = ƛ (` 0) · (` 1)

  open Rename Op sig

  _ : rename (↑ 1) M₀ ≡ (` 1) · (` 2)
  _ = refl

  _ : rename (↑ 1) M₁ ≡ ƛ (` 0) · (` 2)
  _ = refl

  open Subst Op sig

  σ₀ : Substitution ABT
  σ₀ = ` 3 • id

  _ : ⟪ σ₀ ⟫ M₀ ≡ (` 3) · (` 0)
  _ = refl

  _ : ⟪ σ₀ ⟫ M₁ ≡ ƛ (` 0) · (` 4)
  _ = refl

  _ : ⟪ σ₀ ⟫ M₁ ≡ ƛ (` 0) · (` 4)
  _ = refl


