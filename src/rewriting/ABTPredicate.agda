{-# OPTIONS --without-K --rewriting #-}
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
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import ListAux
open import Sig
open import Var

{----- Predicate on ABT's (e.g. type system for expressions) -----}

module rewriting.ABTPredicate {I : Set}
  (Op : Set) (sig : Op → List Sig)
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

data _⊢_⦂_ : List I → ABT → I → Set
data _∣_∣_⊢ₐ_⦂_ : (b : Sig) → List I → BType I b → Arg b → I → Set
data _∣_∣_⊢₊_⦂_ : (bs : List Sig) → List I → BTypes I bs → Args bs
                → Vec I (length bs) → Set

data _⊢_⦂_ where
  var-p : Γ ∋ x ⦂ A
          -----------
        → Γ ⊢ ` x ⦂ A
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

_⦂_⇒_ : Subst → List I → List I → Set
_⦂_⇒_ σ Γ Δ = ∀ {x : Var} {A : I} → Γ ∋ x ⦂ A  → Δ ⊢ σ x ⦂ A

ext-ren-pres : ∀ {ρ : Rename} {Γ Δ : List I} {A : I}
  → ren ρ        ⦂ Γ       ⇒ Δ
  → ext (ren ρ)  ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-ren-pres {ρ}{Γ}{Δ} ρ⦂ {zero} refl = var-p refl
ext-ren-pres {ρ}{Γ}{Δ}{A} ρ⦂ {suc x} {B} ∋x = G
    where
    ρx⦂ : Δ ∋ ρ x ⦂ B
    ρx⦂  with ρ⦂ ∋x
    ... | ⊢ρx rewrite ren-def ρ x
        with ⊢ρx
    ... | var-p ∋ρx = ∋ρx

    G : (A ∷ Δ) ⊢ (ren ρ ⨟ ↑) x ⦂ B
    G rewrite seq-def (ren ρ) ↑ x | ren-def ρ x | sub-var ↑ (ρ x)
        | up-var (ρ x) = var-p ρx⦂

ren-preserve : ∀ {Γ Δ A}{ρ} (M : ABT)
   → Γ ⊢ M ⦂ A
   → ren ρ ⦂ Γ ⇒ Δ
   → Δ ⊢ ⟪ ren ρ ⟫ M ⦂ A
ren-preserve {ρ = ρ} (` x) (var-p ∋x) ρ⦂
    with ρ⦂ ∋x
... | ⊢ρx rewrite sub-var (ren ρ) x = ⊢ρx
ren-preserve {ρ = ρ} (op ⦅ args ⦆) (op-p ⊢args Pop) ρ⦂ =
  op-p (pres-args {ρ = ρ} ⊢args ρ⦂) Pop
  where
  pres-arg : ∀{b Γ Δ}{arg : Arg b}{A ρ Bs}
     → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A
     → ren ρ ⦂ Γ ⇒ Δ
     → b ∣ Δ ∣ Bs ⊢ₐ ⟪ ren ρ ⟫ₐ {b} arg ⦂ A
  pres-args : ∀{bs Γ Δ}{args : Args bs}{As ρ Bss}
     → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As
     → ren ρ ⦂ Γ ⇒ Δ
     → bs ∣ Δ ∣ Bss ⊢₊ ⟪ ren ρ ⟫₊ {bs} args ⦂ As
  pres-arg {b} {arg = ast M}{ρ = ρ} (ast-p ⊢M) ρ⦂ =
      ast-p (ren-preserve{ρ = ρ} M ⊢M ρ⦂)
  pres-arg {ν b}{Γ}{Δ}{bind arg}{ρ = ρ} (bind-p {B = B}{A = A} ⊢arg) ρ⦂ =
      let extρ = ext-ren-pres{ρ} ρ⦂ in
      let IH = pres-arg{ρ = extr ρ} ⊢arg (λ {x = x} → extρ{x = x}) in
      bind-p IH
  pres-args {[]} {args = nil} nil-p ρ⦂ = nil-p
  pres-args {b ∷ bs} {args = cons arg args}{ρ = ρ} (cons-p ⊢arg ⊢args) ρ⦂ =
      cons-p (pres-arg {ρ = ρ} ⊢arg ρ⦂) (pres-args {ρ = ρ} ⊢args ρ⦂)

ext-pres : ∀ {σ : Subst} {Γ Δ : List I} {A : I}
    → σ     ⦂ Γ       ⇒ Δ
    → ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-pres {σ} σ⦂ {zero} refl = var-p refl
ext-pres {σ}{Γ}{Δ} σ⦂ {suc x} {B} ∋x rewrite seq-def σ ↑ x | up-def =
    ren-preserve {ρ = suc} (σ x) (σ⦂ ∋x) ren-suc
    where
    ren-suc : ren suc ⦂ Δ ⇒ (A ∷ Δ)
    ren-suc {C}{y}{D} ∋y rewrite ren-def suc y = var-p ∋y

sub-preserve : ∀ {Γ Δ}{σ} (M : ABT)
   → Γ ⊢ M ⦂ A
   → σ ⦂ Γ ⇒ Δ
   → Δ ⊢ ⟪ σ ⟫ M ⦂ A
sub-preserve {σ = σ} (` x) (var-p ∋x) σ⦂ rewrite sub-var σ x = σ⦂ ∋x
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
        λ { {0}{A} refl → ⊢M ; {suc x}{A} ∋x → var-p ∋x }
