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


module SubstPreserve (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Fold
open import Preserve Op sig
open import GenericSubstitution
open import Var

{-

  This version is more flexible the GenericSubstPres regarding the
  predicate on the output, _⊢c_↝_⦂_, but the price is the additional
  field op-pres.

-}
record SubstPreservableOut {V}{I} (S : Substable V)
  (𝒫 : Op → List I → I → Set) : Set₁ where
  𝒜 : List I → ABT → V → I → Set
  𝒜 _ M _ _ = (M ≡ ` 0)
  open Substable S
  open GenericSub V var→val shift using (⧼_⧽)
  open ABTPred 𝒫
  field _⊢v_↝_⦂_ : List I → ABT → V → I → Set
  field _⊢c_↝_⦂_ : List I → ABT → ABT → I → Set
  field ⊢var→val : ∀{Δ x A} → (Δ ∋ x ⦂ A) → Δ ⊢v (` x) ↝ var→val x ⦂ A
  field val→abt : V → ABT
  open GenericSubst V var→val shift Op sig val→abt using (gen-subst-is-foldable)
  open Foldable gen-subst-is-foldable using (ret; fold-op)
  field 𝒜-var→val : ∀{B Δ} → 𝒜 (B ∷ Δ) (` 0) (var→val 0) B
  field ⊢shift : ∀{Δ A B σ x} → Δ ⊢v ` x ↝ ⧼ σ ⧽ x ⦂ B → (A ∷ Δ) ⊢v ` suc x ↝ shift (⧼ σ ⧽ x) ⦂ B
  field ⊢val→abt : ∀{v Δ A M} → Δ ⊢v M ↝ v ⦂ A → Δ ⊢c M ↝ ret v ⦂ A
  open ArgResult V ABT
  open PresArgResult 𝒫 𝒜 _⊢v_↝_⦂_ _⊢c_↝_⦂_
  field op-pres : ∀ {op}{Rs : ArgsRes (sig op)}{Δ}{A}{As}{args} → sig op ∣ Δ ⊢rs args ↝ Rs ⦂ As → 𝒫 op As A → Δ ⊢c op ⦅ args ⦆ ↝ (fold-op op Rs) ⦂ A


module GenericSubstPresOut (V : Set){I : Set}
  (𝒫 : Op → List I → I → Set)
  (S : Substable V)
  (PS : SubstPreservableOut {V}{I} S 𝒫)
  where
  open Substable S
  open SubstPreservableOut PS
  open GenericSubstitution.SNF using (Substitution)
  open GenericSub V var→val shift hiding (extend)
  open GenericSubst V var→val shift Op sig val→abt
  open ArgResult V ABT
  open ABTPred 𝒫
  
  _⦂_⇒_ : Substitution V → List I → List I → Set
  _⦂_⇒_ ρ Γ Δ = ∀ {x}{A} → Γ ∋ x ⦂ A → Δ ⊢v ` x ↝ ⧼ ρ ⧽ x ⦂ A
  
  open PresArgResult {V}{ABT}{I} 𝒫 𝒜 _⊢v_↝_⦂_ _⊢c_↝_⦂_
  open SNF
  open import GenericSubProperties S
  open Foldable gen-subst-is-foldable

  extend-pres : ∀ {v : V}{σ}{Γ}{Δ}{A}{M}
     → (A ∷ Δ) ⊢v M ↝ v ⦂ A
     → M ≡ (` 0)
     → σ ⦂ Γ ⇒ Δ
     → (extend σ v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  extend-pres {v} {σ} {Γ} {Δ} {A} ∋v refl σΓΔ {zero} {B} refl = ∋v
  extend-pres {v} {σ} {Γ} {Δ} {A} ∋v refl σΓΔ {suc x} {B} ∋x
      rewrite inc-suc σ x =
      ⊢shift {σ = σ} (σΓΔ ∋x)

  gen-subst-is-preservable : Preservable I gen-subst-is-foldable
  gen-subst-is-preservable = record { 𝒫 = 𝒫 ; _⦂_⇒_ = _⦂_⇒_ ; _⊢v_↝_⦂_ = _⊢v_↝_⦂_
      ; _⊢c_↝_⦂_ = _⊢c_↝_⦂_
      ; lookup-pres = λ σΓΔ Γ∋x → σΓΔ Γ∋x ; extend-pres = extend-pres
      ; ret-pres = ⊢val→abt ; var-pres = λ Γ∋x → ⊢var→val Γ∋x
      ; op-pres = op-pres }
  open Preservation gen-subst-is-foldable gen-subst-is-preservable public

  gen-subst-preserve : ∀ {M : ABT} {σ : Substitution V} {Γ Δ : List I} {A : I}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ gen-subst σ M ⦂ A
  gen-subst-preserve = preserve


record SubstPreservable {V}{I} (S : Substable V)
  (𝒫 : Op → List I → I → Set) : Set₁ where
  𝒜 : List I → ABT → V → I → Set
  𝒜 _ M _ _ = (M ≡ ` 0)
  open Substable S
  open GenericSub V var→val shift using (⧼_⧽)
  open ABTPred 𝒫
  field _⊢v_↝_⦂_ : List I → ABT → V → I → Set
  field ⊢var→val : ∀{Δ x A} → (Δ ∋ x ⦂ A) → Δ ⊢v (` x) ↝ var→val x ⦂ A
  field val→abt : V → ABT
  open GenericSubst V var→val shift Op sig val→abt using (gen-subst-is-foldable)
  open Foldable gen-subst-is-foldable using (ret)
  field 𝒜-var→val : ∀{B Δ} → 𝒜 (B ∷ Δ) (` 0) (var→val 0) B
  field ⊢shift : ∀{Δ A B σ x} → Δ ⊢v ` x ↝ ⧼ σ ⧽ x ⦂ B → (A ∷ Δ) ⊢v ` suc x ↝ shift (⧼ σ ⧽ x) ⦂ B
  field ⊢val→abt : ∀{v Δ A M} → Δ ⊢v M ↝ v ⦂ A → Δ ⊢ ret v ⦂ A


module GenericSubstPres (V : Set){I : Set}
  (𝒫 : Op → List I → I → Set)
  (S : Substable V)
  (PS : SubstPreservable {V}{I} S 𝒫)
  where
  open Substable S
  open SubstPreservable PS
  open GenericSubstitution.SNF using (Substitution)
  open GenericSub V var→val shift hiding (extend)
  open GenericSubst V var→val shift Op sig val→abt
  open ArgResult V ABT
  open ABTPred 𝒫
  
  _⊢c_↝_⦂_ : List I → ABT → ABT → I → Set
  Γ ⊢c M ↝ M′ ⦂ A = Γ ⊢ M′ ⦂ A
  
  _⦂_⇒_ : Substitution V → List I → List I → Set
  _⦂_⇒_ ρ Γ Δ = ∀ {x}{A} → Γ ∋ x ⦂ A → Δ ⊢v ` x ↝ ⧼ ρ ⧽ x ⦂ A
  
  open PresArgResult {V}{ABT}{I} 𝒫 𝒜 _⊢v_↝_⦂_ _⊢c_↝_⦂_
  open SNF
  open import GenericSubProperties S

  res→arg : ∀{Δ : List I}{b}{R : ArgRes b}{A : I}{arg : Arg b}
     → b ∣ Δ ⊢r arg ↝ R ⦂ A
     → b ∣ Δ ⊢a s-arg R ⦂ A
  res→arg {Δ} {zero} {R} {A} (ast-r ⊢R) = ast-a ⊢R
  res→arg {Δ} {suc b} {R} {A} (bind-r {B = B} f) =
      bind-a (res→arg (f (⊢var→val refl) (𝒜-var→val{B}{Δ})))
  
  res→args : ∀{Δ}{bs}{Rs : ArgsRes bs}{As : List I}{args : Args bs}
     → bs ∣ Δ ⊢rs args ↝ Rs ⦂ As
     → bs ∣ Δ ⊢as s-args Rs ⦂ As
  res→args {Δ} {[]} {.rnil} {.[]} nil-r = nil-a
  res→args {Δ} {b ∷ bs} {.(rcons _ _)} {.(_ ∷ _)} (cons-r ⊢R ⊢Rs) =
      cons-a (res→arg ⊢R) (res→args ⊢Rs)

  open Foldable gen-subst-is-foldable
  
  op-pres : ∀ {op : Op}{Rs : ArgsRes (sig op)}{Δ : List I}{A : I}{As : List I}
       {args : Args (sig op)}
     → sig op ∣ Δ ⊢rs args ↝ Rs ⦂ As
     → 𝒫 op As A
     → Δ ⊢ (fold-op op Rs) ⦂ A
  op-pres {op}{Rs}{Δ}{A}{As} ⊢Rs 𝒫op =
      let ⊢sargs = (eq-subst (λ □ → sig op ∣ □ ⊢as s-args Rs ⦂ As) refl
                            (res→args ⊢Rs)) in
      op-op ⊢sargs 𝒫op

  gen-subst-is-pres-out : SubstPreservableOut S 𝒫
  gen-subst-is-pres-out = record { _⊢v_↝_⦂_ = _⊢v_↝_⦂_ ; _⊢c_↝_⦂_ = _⊢c_↝_⦂_
      ; ⊢var→val = ⊢var→val ; val→abt = val→abt
      ; 𝒜-var→val = λ {B}{Δ} → 𝒜-var→val{B}{Δ}
      ; ⊢shift = λ {Δ}{A}{B}{σ}{x} → ⊢shift {σ = σ}
      ; ⊢val→abt = ⊢val→abt ; op-pres = op-pres }
  
  open GenericSubstPresOut V 𝒫 S gen-subst-is-pres-out
      using () renaming (gen-subst-preserve to preserve)

  gen-subst-preserve : ∀ {M : ABT} {σ : Substitution V} {Γ Δ : List I} {A : I}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢ gen-subst σ M ⦂ A
  gen-subst-preserve = preserve


module RenamePres {I : Set}
  (𝒫 : Op → List I → I → Set) where
  open import AbstractBindingTree Op sig using ()
  open import Preserve Op sig using ()
  open GenericSubstitution.SNF using (Substitution)
  open ABTPred 𝒫 using (_⊢_⦂_; var-p)
  open import Rename Op sig using (Rename; rename; rename-is-substable)
  rename-is-subst-pres : SubstPreservable rename-is-substable 𝒫
  rename-is-subst-pres = record
                           { _⊢v_↝_⦂_ = λ Γ M x A → Γ ∋ x ⦂ A
                           ; ⊢var→val = λ {Δ} {x} {A} ∋x → ∋x
                           ; val→abt = `_
                           ; 𝒜-var→val = λ {B} {Δ} → refl
                           ; ⊢shift = λ { ∋x → ∋x }
                           ; ⊢val→abt = λ { ∋x → var-p ∋x }
                           }
  open GenericSubstPres Var 𝒫 rename-is-substable rename-is-subst-pres 

  rename-preserve : ∀ {M : ABT} {ρ : Rename} {Γ Δ : List I} {A : I}
     → Γ ⊢ M ⦂ A
     → ρ ⦂ Γ ⇒ Δ
     → Δ ⊢ rename ρ M ⦂ A
  rename-preserve = gen-subst-preserve

module SubstPres {I : Set}
  (𝒫 : Op → List I → I → Set) where
  open import AbstractBindingTree Op sig using (`_)
  open GenericSubstitution.SNF using (Substitution)
  open import Rename Op sig using (rename)
  open import Preserve Op sig using ()
  open ABTPred 𝒫 using (_⊢_⦂_; var-p)
  open RenamePres 𝒫 using (rename-preserve)
  open import Subst Op sig using (Subst; ↑; ⟪_⟫)
  open import SubstProperties Op sig using (subst-is-substable)
  subst-is-subst-pres : SubstPreservable subst-is-substable 𝒫
  subst-is-subst-pres = record
                { _⊢v_↝_⦂_ = λ Γ M M′ A → Γ ⊢ M′ ⦂ A
                ; ⊢var→val = λ ∋x → var-p ∋x
                ; val→abt = λ M → M
                ; 𝒜-var→val = λ {B} {Δ} → refl
                ; ⊢shift = λ ⊢M → rename-preserve {ρ = ↑ 1} ⊢M (λ {x} {A} z → z)
                ; ⊢val→abt = λ ⊢M → ⊢M
                }
  open GenericSubstPres ABT 𝒫 subst-is-substable subst-is-subst-pres
  
  subst-preserve : ∀ {M : ABT} {σ : Subst} {Γ Δ : List I} {A : I}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢ ⟪ σ ⟫ M ⦂ A
  subst-preserve = gen-subst-preserve

{-
where to put the following?

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

  open import Rename Op sig hiding (id)

  _ : rename (↑ 1) M₀ ≡ (` 1) · (` 2)
  _ = refl

  _ : rename (↑ 1) M₁ ≡ ƛ (` 0) · (` 2)
  _ = refl

  open import Subst Op sig

  σ₀ : Subst
  σ₀ = ` 3 • id

  _ : ⟪ σ₀ ⟫ M₀ ≡ (` 3) · (` 0)
  _ = refl

  _ : ⟪ σ₀ ⟫ M₁ ≡ ƛ (` 0) · (` 4)
  _ = refl

  _ : ⟪ σ₀ ⟫ M₁ ≡ ƛ (` 0) · (` 4)
  _ = refl



-}
