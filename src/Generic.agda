{-

  Experiments in generic functions and theorems over abstract binding trees.

  Trying to draw inspiration from "A Type and Scope Safe Universe of Syntaxes with Biding", ICFP 2018.

-}

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

module GenericSub2 (V : Set)
  (var→val : Var → V)
  (shift : V → V)
  (⟪_⟫ : Substitution V → V → V)
  (var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x))
  (sub-var→val : ∀ σ x → ⟪ σ ⟫ (var→val x) ≡ GenericSub.⧼_⧽ V var→val shift  σ x)
  (shift-⟪↑1⟫ : ∀ v → shift v ≡ ⟪ ↑ 1 ⟫ v)
  where

  open GenericSub V var→val shift
  open import Data.Nat.Properties using (+-comm; +-assoc)

  infixr 5 _⨟_

  _⨟_ : Substitution V → Substitution V → Substitution V
  ↑ k ⨟ σ = drop k σ
  (v • σ₁) ⨟ σ₂ = ⟪ σ₂ ⟫ v • (σ₁ ⨟ σ₂)

  sub-tail : (v : V) (σ : Substitution V)
     → (↑ 1 ⨟ v • σ) ≡ σ
  sub-tail v (↑ k) = refl
  sub-tail v (w • σ) = refl

  inc-suc : ∀ ρ x → ⧼ gen-inc ρ ⧽ x ≡ shift (⧼ ρ ⧽ x)
  inc-suc (↑ k) x = var→val-suc-shift
  inc-suc (x₁ • ρ) zero = refl
  inc-suc (x₁ • ρ) (suc x) = inc-suc ρ x

  inc=⨟↑ : ∀ σ → gen-inc σ ≡ σ ⨟ ↑ 1
  inc=⨟↑ (↑ k) rewrite +-comm k 1 = refl
  inc=⨟↑ (v • σ) = cong₂ _•_ (shift-⟪↑1⟫ v) (inc=⨟↑ σ)

  exts-cons-shift : ∀ σ v → extend σ v ≡ (v • (σ ⨟ ↑ 1))
  exts-cons-shift (↑ k) v rewrite +-comm k 1 = refl
  exts-cons-shift (w • σ) v rewrite inc=⨟↑ σ | shift-⟪↑1⟫ w = refl

  drop-add : ∀{x : Var} (k : ℕ) (σ : Substitution V)
           → ⧼ drop k σ ⧽ x ≡ ⧼ σ ⧽ (k + x)
  drop-add {x} k (↑ k') rewrite +-comm k k' | +-assoc k' k x = refl
  drop-add {x} zero (v • σ) = refl
  drop-add {x} (suc k) (v • σ) = drop-add k σ

  sub-η : ∀ (σ : Substitution V) (x : Var)
        → ⧼ (⟪ σ ⟫ (var→val 0) • (↑ 1 ⨟ σ)) ⧽ x ≡ ⧼ σ ⧽ x
  sub-η σ 0 rewrite sub-var→val σ 0 = refl
  sub-η σ (suc x) = drop-add 1 σ

  Z-shift : ∀ x → ⧼ var→val 0 • ↑ 1 ⧽ x ≡ var→val x
  Z-shift 0 = refl
  Z-shift (suc x) = refl

  sub-idL : (σ : Substitution V)
         → id ⨟ σ ≡ σ
  sub-idL (↑ k) = refl
  sub-idL (M • σ) = refl

  sub-dist :  ∀ {σ : Substitution V} {τ : Substitution V} {M : V}
           → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
  sub-dist = refl

  seq-subst : ∀ σ τ x → ⧼ σ ⨟ τ ⧽ x ≡ ⟪ τ ⟫ (⧼ σ ⧽ x)
  seq-subst (↑ k) τ x rewrite drop-add {x} k τ | sub-var→val τ (k + x) = refl
  seq-subst (M • σ) τ zero = refl
  seq-subst (M • σ) τ (suc x) = seq-subst σ τ x

  exts-ids : ∀{σ : Substitution V}
     → (∀ x → ⧼ σ ⧽ x ≡ var→val x)
     → (∀ x → ⧼ extend σ (var→val 0) ⧽ x ≡ var→val x)
  exts-ids {σ} is-id zero
      rewrite exts-cons-shift σ (var→val 0) = refl
  exts-ids {σ} is-id (suc x)
      rewrite exts-cons-shift σ (var→val 0) | seq-subst σ (↑ 1) x | inc-suc σ x
      | is-id x | var→val-suc-shift {x} = refl

{-
module IdFold
  (Op : Set) (sig : Op → List ℕ)
  where
  open OpSig Op sig hiding (shift; rename)
  open Rename Op sig
  open Subst Op sig
  shift = rename (↑ 1)
  open GenericSub ABT `_ shift
  open ArgResult ABT ABT

  open GenericSub2 ABT `_ shift subst (λ {x} → refl) (λ σ x → refl)
  
  res→arg : ∀{b} → ArgRes b → Arg b
  res→arg {zero} M = ast M
  res→arg {suc b} r = bind (res→arg (r (` 0)))

  res→args : ∀{bs} → ArgsRes bs → Args bs
  res→args {[]} rnil = nil
  res→args {b ∷ bs} (rcons r rs) = cons (res→arg r) (res→args rs)
      
  id-is-foldable : Foldable ABT ABT Op sig (Substitution ABT)
  id-is-foldable = record { env = subst-is-env ; ret = λ M → M ;
            fold-free-var = `_ ; fold-op = λ o rs → o ⦅ res→args rs ⦆ }

  module IdFold = Folder id-is-foldable
  open IdFold renaming (fold to ids; fold-arg to id-arg; fold-args to id-args)

  id-id : ∀ M σ
     → (∀ x → ⧼ σ ⧽ x ≡ ` x)
     → ids σ M ≡ M
  id-id-arg : ∀ {b} (arg : Arg b) σ
     → (∀ x → ⧼ σ ⧽ x ≡ ` x)
     → res→arg {b} (id-arg σ arg) ≡ arg
  id-id-args : ∀ {bs} (args : Args bs) σ
     → (∀ x → ⧼ σ ⧽ x ≡ ` x)
     → res→args {bs} (id-args σ args) ≡ args
  
  id-id (` x) σ σ-id = σ-id x
  id-id (op ⦅ args ⦆) σ σ-id =
      cong (_⦅_⦆ op) (id-id-args args σ σ-id)
  id-id-arg {zero} (ast M) σ σ-id = cong ast (id-id M σ σ-id)
  id-id-arg {suc b} (bind arg) σ σ-id =
      cong bind (id-id-arg arg (extend σ (` 0)) E)
      where
      E : ∀ x → ⧼ extend σ (` 0) ⧽ x ≡ (` x)
      E zero = refl
      E (suc x) =
{-
          let isx : ⧼ inc σ ⧽ x ≡ shift (⧼ σ ⧽ x)
              isx = inc-suc σ x in
          let ss = σ-id x in
-}
           {!!}
      {- 
Goal: ⧼ extend σ (` 0) ⧽ (suc x) ≡ (` suc x)
      ⧼ (inc σ) ⧽ x
      


      -}
      
  id-id-args {[]} nil σ σ-id = refl
  id-id-args {b ∷ bs} (cons arg args) σ σ-id =
      cong₂ cons (id-id-arg arg σ σ-id) (id-id-args args σ σ-id)
-}


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

  inc-suc : ∀ ρ x → ⧼ inc ρ ⧽ x ≡ shift (⧼ ρ ⧽ x)
  inc-suc (↑ k) x = var→val-suc-shift
  inc-suc (x₁ • ρ) zero = refl
  inc-suc (x₁ • ρ) (suc x) = inc-suc ρ x
  
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


module RelGenericSubst (V₁ V₂ : Set) (_∼_ : V₁ → V₂ → Set) where
  data _≊_ : Substitution V₁ → Substitution V₂ → Set where
     r-up : ∀{k} → (↑ k) ≊ (↑ k)
     r-cons : ∀{v₁ σ₁ v₂ σ₂}
        → v₁ ∼ v₂  →   σ₁ ≊ σ₂
        → (v₁ • σ₁) ≊ (v₂ • σ₂)


module RelateSub (V₁ V₂ : Set)
  (_∼_ : V₁ → V₂ → Set)
  (var→val₁ : Var → V₁)
  (shift₁ : V₁ → V₁)
  (var→val₂ : Var → V₂)
  (shift₂ : V₂ → V₂)
  (var→val∼ : ∀{x} → var→val₁ x ∼ var→val₂ x)
  (shift∼ : ∀ {v₁ v₂} → v₁ ∼ v₂ → shift₁ v₁ ∼ shift₂ v₂)
  where

  open GenericSub V₁ var→val₁ shift₁
     renaming (⧼_⧽ to ⧼_⧽₁; subst-is-env to subst-is-env₁; gen-inc to inc₁)
  open GenericSub V₂ var→val₂ shift₂
     renaming (⧼_⧽ to ⧼_⧽₂; subst-is-env to subst-is-env₂; gen-inc to inc₂)
  open RelGenericSubst V₁ V₂ _∼_

  lookup∼ : {σ₁ : Substitution V₁} {σ₂ : Substitution V₂} →
      σ₁ ≊ σ₂ → {x : ℕ} → ⧼ σ₁ ⧽₁ x ∼ ⧼ σ₂ ⧽₂ x
  lookup∼ (r-up{k}) {x} = var→val∼
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {zero} = v₁∼v₂
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {suc x} = lookup∼ σ₁≊σ₂

  ≊-inc : ∀{σ₁}{σ₂}
    → σ₁ ≊ σ₂
    → (inc₁ σ₁) ≊ (inc₂ σ₂)
  ≊-inc {.(↑ _)} {.(↑ _)} r-up = r-up
  ≊-inc {.(_ • _)} {.(_ • _)} (r-cons v₁∼v₂ σ₁≊σ₂) = r-cons (shift∼ v₁∼v₂) (≊-inc σ₁≊σ₂)

  sub-is-rel-env : RelatedEnv _∼_ subst-is-env₁ subst-is-env₂
  sub-is-rel-env = record { _≊_ = _≊_ ; lookup∼ = lookup∼ ;
                    extend≊ = λ v₁∼v₂ σ₁≊σ₂ → r-cons v₁∼v₂ (≊-inc σ₁≊σ₂) }

module SubstSubst
  (Op : Set) (sig : Op → List ℕ) 
  (V₁ V₂ : Set)
  (_∼_ : V₁ → V₂ → Set)
  (var→val₁ : Var → V₁)
  (shift₁ : V₁ → V₁)
  (val→abt₁ : V₁ → AbstractBindingTree.ABT Op sig)
  (var→val₂ : Var → V₂)
  (shift₂ : V₂ → V₂)
  (val→abt₂ : V₂ → AbstractBindingTree.ABT Op sig)
  (var→val∼ : ∀{x} → var→val₁ x ∼ var→val₂ x)
  (shift∼ : ∀ {v₁ v₂} → v₁ ∼ v₂ → shift₁ v₁ ∼ shift₂ v₂)
  (val→abt∼ : ∀{v₁ v₂} → v₁ ∼ v₂ → val→abt₁ v₁ ≡ val→abt₂ v₂)
  where

  _≈_ = _≡_

  open AbstractBindingTree Op sig
  open RelGenericSubst V₁ V₂ _∼_
  open RelateSub V₁ V₂ _∼_ var→val₁ shift₁ var→val₂ shift₂ var→val∼ shift∼
  open SimArgResult {Op}{sig}{V₁}{ABT}{V₂}{ABT} _∼_ _≈_
  open GenericSubst V₁ var→val₁ shift₁ Op sig val→abt₁
      renaming (gen-subst to gen-subst₁;
          gen-subst-is-foldable to gsubst-foldable₁;
          s-arg to s-arg₁; s-args to s-args₁)
  open GenericSubst V₂ var→val₂ shift₂ Op sig val→abt₂
      renaming (gen-subst to gen-subst₂;
          gen-subst-is-foldable to gsubst-foldable₂;
          s-arg to s-arg₂; s-args to s-args₂)
  open Foldable gsubst-foldable₁ renaming (fold-op to fop₁)
  open Foldable gsubst-foldable₂ renaming (fold-op to fop₂)

  op∼ : ∀{op : Op}{Rs₁ : ArgsRes₁ (sig op)}{Rs₂ : ArgsRes₂ (sig op)}
         → ArgsRes∼ Rs₁ Rs₂
         → fop₁ op Rs₁ ≈ fop₂ op Rs₂
  op∼ {op}{Rs₁}{Rs₂} rs∼ = G
    where
    I : ∀{b}{R₁ : ArgRes₁ b}{R₂ : ArgRes₂ b} → ArgRes∼ R₁ R₂
       → s-arg₁ R₁ ≡ s-arg₂ R₂
    I {zero} {R₁} {.R₁} refl = refl
    I {suc b} {R₁} {R₂} r~ = cong bind (I (r~ var→val∼))
    
    H : ∀{bs}{Rs₁ : ArgsRes₁ bs}{Rs₂ : ArgsRes₂ bs} → ArgsRes∼ Rs₁ Rs₂
       → s-args₁ Rs₁ ≡ s-args₂ Rs₂
    H {[]} {rnil₁} {rnil₂} rnil∼ = refl
    H {b ∷ bs} {rcons₁ r₁ Rs₁} {rcons₂ r₂ Rs₂} (rcons∼ r∼ rs∼) =
        cong₂ cons (I r∼) (H rs∼)

    G : op ⦅ s-args₁ Rs₁ ⦆ ≡ op ⦅ s-args₂ Rs₂ ⦆
    G = cong (_⦅_⦆ op) (H rs∼)

  SubSubRel : Related gsubst-foldable₁ gsubst-foldable₂
  SubSubRel = record { _∼_ = _∼_ ; _≈_ = _≈_ ; env∼ = sub-is-rel-env ;
         ret≈ = λ {v₁} {v₂} v₁∼v₂ → val→abt∼ v₁∼v₂ ; vars∼ = λ {x} → var→val∼ ;
         op∼ = op∼ }

  module Sim = Simulator gsubst-foldable₁ gsubst-foldable₂ SubSubRel

  subsub-sim : ∀{σ₁}{σ₂} (M : ABT) → σ₁ ≊ σ₂ → gen-subst₁ σ₁ M ≡ gen-subst₂ σ₂ M
  subsub-sim M = Sim.sim {M = M}


module RenSub (Op : Set) (sig : Op → List ℕ) where

  open AbstractBindingTree Op sig using (ABT; `_; _⦅_⦆; cons; bind)
  {- ; rename→subst; ⟪_⟫) -}
  open Rename Op sig
  open Subst Op sig
  _∼_ = λ x M → ` x ≡ M
  open SubstSubst Op sig Var ABT _∼_ (λ x → x) suc `_ `_ (rename (↑ 1))
        (λ M → M) (λ {x} → refl) (λ { refl → refl } ) (λ { refl → refl })
  open RelGenericSubst Var ABT _∼_
  
{-
  rename→subst-≊ : ∀{ρ} → ρ ≊ rename→subst ρ
  rename→subst-≊ {↑ k} = r-up
  rename→subst-≊ {x • ρ} = r-cons refl rename→subst-≊

  rensub : ∀ ρ M → rename ρ M ≡ subst (rename→subst ρ) M
  rensub ρ M = subsub-sim M rename→subst-≊
-}
