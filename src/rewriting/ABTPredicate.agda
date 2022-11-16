{-# OPTIONS --without-K --rewriting #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.List using (List; []; _∷_; length; map; foldl)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties
    using (+-suc; ≤-trans; ≤-step; ≤-refl; ≤-reflexive; m≤m+n; ≤-pred;
    m≤m⊔n; n≤m⊔n; m≤n⇒m<n∨m≡n; m≤n⇒m≤o⊔n)
open import Data.Product
    using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Level using (levelOfType)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import ListAux
open import Sig
open import Var

{----- Predicate on ABT's (e.g. type system for expressions) -----}

module rewriting.ABTPredicate {I : Set}
  (Op : Set) (sig : Op → List Sig)
  (𝑉 : List I → Var → I → I → Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set)
  where

open import rewriting.AbstractBindingTree Op sig
open Renaming

private
  variable
    x : Var
    b : Sig
    A B : I
    Γ : List I
    M : ABT

{- changing
   Set (levelOfType I)
   to
   Set
   in _⊢_⦂_ triggers an internal error when processing the Lambda example.
-}
data _⊢_⦂_ : List I → ABT → I → Set (levelOfType I)
data _∣_∣_⊢ₐ_⦂_ : (b : Sig) → List I → BType I b → Arg b → I
   → Set (levelOfType I)
data _∣_∣_⊢₊_⦂_ : (bs : List Sig) → List I → BTypes I bs → Args bs
                → Vec I (length bs) → Set (levelOfType I)

data _⊢_⦂_ where
  var-p : Γ ∋ x ⦂ A  →  𝑉 Γ x A B
     → Γ ⊢ ` x ⦂ B
  op-p : ∀{op}{args : Args (sig op)}{As : Vec I (length (sig op))}
           {Bs : BTypes I (sig op)}
     → (sig op) ∣ Γ ∣ Bs ⊢₊ args ⦂ As
     → 𝑃 op As Bs A
     → Γ ⊢ op ⦅ args ⦆ ⦂ A

data _∣_∣_⊢ₐ_⦂_ where
  ast-p : Γ ⊢ M ⦂ A
     → ■ ∣ Γ ∣ tt ⊢ₐ ast M ⦂ A

  bind-p : ∀{Bs arg}
     → b ∣ (B ∷ Γ) ∣ Bs ⊢ₐ arg ⦂ A
     → ν b ∣ Γ ∣ ⟨ B , Bs ⟩ ⊢ₐ bind arg ⦂ A

data _∣_∣_⊢₊_⦂_ where
  nil-p : [] ∣ Γ ∣ tt ⊢₊ nil ⦂ []̌ 
  cons-p : ∀{bs}{arg args}{As}{Bs}{Bss}
     → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A  →  bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As
     → (b ∷ bs) ∣ Γ ∣ ⟨ Bs , Bss ⟩ ⊢₊ cons arg args ⦂ (A ∷̌ As)

_⦂_⇒ᵣ_ : Rename → List I → List I → Set
_⦂_⇒ᵣ_ ρ Γ Δ = ∀{x : Var} {A B : I} → Γ ∋ x ⦂ A  → 𝑉 Γ x A B →  Δ ⊢ ` ρ x ⦂ B

_⦂_⇒_ : Subst → List I → List I → Set
_⦂_⇒_ σ Γ Δ = ∀{x : Var} {A : I} → Γ ∋ x ⦂ A  → Δ ⊢ σ x ⦂ A

module SubstPreserve
  (𝑉-refl : ∀{Γ x A} → Γ ∋ x ⦂ A → 𝑉 Γ x A A)
  (𝑉-zero : ∀{A B Γ Δ} → 𝑉 (A ∷ Γ) 0 A B → 𝑉 (A ∷ Δ) 0 A B)
  (𝑉-suc : ∀{A A′ B Δ x} → 𝑉 Δ x A A′ → 𝑉 (B ∷ Δ) (suc x) A A′)
  (𝑉-pred : ∀{A A′ B Δ x} → 𝑉 (B ∷ Δ) (suc x) A A′ → 𝑉 Δ x A A′)
  (𝑉-subsump : ∀{x M A B Γ Δ} → 𝑉 Γ x A B → Δ ⊢ M ⦂ A → Δ ⊢ M ⦂ B) where

  extr-pres : ∀ {ρ : Rename} {Γ Δ : List I} {A : I}
    → ρ      ⦂ Γ       ⇒ᵣ Δ
    → extr ρ ⦂ (A ∷ Γ) ⇒ᵣ (A ∷ Δ)
  extr-pres {ρ}{Γ}{Δ} ρ⦂ {zero} refl Vx = var-p refl (𝑉-zero Vx)
  extr-pres {ρ = ρ} ρ⦂ {suc x} ∋x Vx
        with ρ⦂ ∋x (𝑉-pred Vx)
  ... | var-p ∋y Vy = var-p ∋y (𝑉-suc Vy)

  rename-preserve : ∀ {Γ Δ}{ρ} (M : ABT)
     → Γ ⊢ M ⦂ A
     → ρ ⦂ Γ ⇒ᵣ Δ
     → Δ ⊢ rename ρ M ⦂ A
  rename-preserve (` x) (var-p ∋x Vx) ρ⦂ = ρ⦂ ∋x Vx
  rename-preserve (op ⦅ args ⦆) (op-p ⊢args Pop) ρ⦂ = op-p (pres-args ⊢args ρ⦂) Pop
    where
    pres-arg : ∀{b Γ Δ}{arg : Arg b}{A ρ Bs}
       → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A → ρ ⦂ Γ ⇒ᵣ Δ
       → b ∣ Δ ∣ Bs ⊢ₐ rename-arg ρ {b} arg ⦂ A
    pres-args : ∀{bs Γ Δ}{args : Args bs}{As ρ Bss}
       → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As → ρ ⦂ Γ ⇒ᵣ Δ
       → bs ∣ Δ ∣ Bss ⊢₊ rename-args ρ {bs} args ⦂ As
    pres-arg {b} {arg = ast M} (ast-p ⊢M) ρ⦂ =
        ast-p (rename-preserve M ⊢M ρ⦂)
    pres-arg {ν b}{Γ}{Δ}{bind arg}{ρ = ρ} (bind-p {B = B}{A = A} ⊢arg) ρ⦂ =
        bind-p (pres-arg ⊢arg (λ{x}{A} → extr-pres {ρ}{Γ}{Δ} ρ⦂ {x}{A}))
    pres-args {[]} {args = nil} nil-p ρ⦂ = nil-p
    pres-args {b ∷ bs} {args = cons arg args} (cons-p ⊢arg ⊢args) ρ⦂ =
        cons-p (pres-arg ⊢arg ρ⦂) (pres-args ⊢args ρ⦂)

  module LocalRewrites where
    {-# REWRITE seq-up-rename-suc #-}
  open LocalRewrites
      
  ext-pres : ∀ {σ : Subst} {Γ Δ : List I} {A : I}
    → σ     ⦂ Γ       ⇒ Δ
    → ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-pres {σ = σ} σ⦂ {zero} refl = var-p refl (𝑉-refl refl)
  ext-pres {σ = σ} σ⦂ {suc x} ∋x =
      rename-preserve {ρ = suc} (σ x) (σ⦂ ∋x)
          (λ {y} ∋y Vy → var-p ∋y (𝑉-suc Vy))

  sub-preserve : ∀ {Γ Δ}{σ} (M : ABT)
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢ ⟪ σ ⟫ M ⦂ A
  sub-preserve (` x) (var-p ∋x Vx) σ⦂ = 𝑉-subsump Vx (σ⦂ ∋x)
  sub-preserve (op ⦅ args ⦆) (op-p ⊢args Pop) σ⦂ = op-p (pres-args ⊢args σ⦂) Pop
    where
    pres-arg : ∀{b Γ Δ}{arg : Arg b}{A σ Bs}
       → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A → σ ⦂ Γ ⇒ Δ
       → b ∣ Δ ∣ Bs ⊢ₐ ⟪ σ ⟫ₐ {b} arg ⦂ A
    pres-args : ∀{bs Γ Δ}{args : Args bs}{As σ Bss}
       → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As → σ ⦂ Γ ⇒ Δ
       → bs ∣ Δ ∣ Bss ⊢₊ ⟪ σ ⟫₊ {bs} args ⦂ As
    pres-arg {b} {arg = ast M} (ast-p ⊢M) σ⦂ =
        ast-p (sub-preserve M ⊢M σ⦂)
    pres-arg {ν b}{Γ}{Δ}{bind arg}{σ = σ} (bind-p {B = B}{A = A} ⊢arg) σ⦂ =
        bind-p (pres-arg ⊢arg (λ{x}{A} → ext-pres {σ}{Γ}{Δ} σ⦂ {x}{A}))
    pres-args {[]} {args = nil} nil-p σ⦂ = nil-p
    pres-args {b ∷ bs} {args = cons arg args} (cons-p ⊢arg ⊢args) σ⦂ =
        cons-p (pres-arg ⊢arg σ⦂) (pres-args ⊢args σ⦂)

  preserve-substitution : ∀{Γ : List I}{A B : I} (N M : ABT)
    → (A ∷ Γ) ⊢ N ⦂ B
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N [ M ] ⦂ B
  preserve-substitution {Γ}{A} N M ⊢N ⊢M =
      sub-preserve {σ = M • id} N ⊢N
          λ { {0}{A} refl → ⊢M ; {suc x}{A} ∋x → var-p ∋x (𝑉-refl ∋x) }
