{-# OPTIONS --without-K #-}
{---------------------------------

  Fold preserves any ABT predicate

      Let "I" be the kind for type-like things.

      A : I
      Γ Δ : List I

  fold-preserves : ∀{M σ Γ Δ A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold σ M ⦂ A

 ----------------------------------}

import ABTPredicate
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Function using (_∘_)
open import GSubst
open import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import ScopedTuple
open import Sig
open import Structures
import Substitution
open import Var

module FoldPreserve (Op : Set) (sig : Op → List Sig) where

private
  variable
    ℓ ℓᵛ ℓᶜ ℓⁱ : Level
    V C I : Set ℓ

open import AbstractBindingTree Op sig
open import Fold Op sig
open Structures.WithOpSig Op sig

record FoldPreservable (V : Set ℓᵛ) (C : Set ℓᶜ) (I : Set ℓⁱ)
  {{_ : Shiftable V}} : Set (lsuc (ℓᵛ ⊔ ℓᶜ ⊔ ℓⁱ)) where
  field {{VC-Foldable}} : Foldable V C
  field 𝑉 : List I → Var → I → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        𝐴 : List I → V → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        _⊢c_⦂_ : List I → C → I → Set
        ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c ret v ⦂ A
        shift-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v ⇑ v ⦂ A
        prev-𝑉 : ∀{x A B C Γ} → 𝑉 (C ∷ Γ) (suc x) A B → 𝑉 Γ x A B
        𝑉-⊢v : ∀{x v A B Γ Δ} → 𝑉 Γ x A B → Δ ⊢v v ⦂ A → Δ ⊢v v ⦂ B
  open ABTPredicate Op sig 𝑉 𝑃 public
  
open FoldPreservable {{...}}

data _∣_∣_⊢ᵣ_⦂_ {V C I : Set}
    {{_ : Shiftable V}} {{_ : FoldPreservable V C I}}
  : (b : Sig) → List I → BType I b → Bind V C b → I → Set where
  ast-r : ∀{Δ}{c}{A}  →  Δ ⊢c c ⦂ A →  ■ ∣ Δ ∣ tt ⊢ᵣ lift c ⦂ A
  bind-r : ∀{b A B}{Bs : BType I b}{ Δ f}
        → (∀{v} → (B ∷ Δ) ⊢v v ⦂ B → 𝐴 (B ∷ Δ) v B
                → b ∣ (B ∷ Δ) ∣ Bs ⊢ᵣ (f v) ⦂ A)
        → (ν b) ∣ Δ ∣ ⟨ B , Bs ⟩ ⊢ᵣ f ⦂ A
  clear-r : ∀{Δ b c A}{Bs : BType I b}
        → b ∣ Δ ∣ Bs ⊢ᵣ c ⦂ A
        → ∁ b ∣ Δ ∣ Bs ⊢ᵣ c ⦂ A

⊢ᵣ→⊢c : ∀{V C I : Set}
    {{_ : Shiftable V}} {{_ : FoldPreservable V C I}}
    {Δ : List I}{Bs : ⊤}{c : C}{A}
    → ■ ∣ Δ ∣ Bs ⊢ᵣ lift c ⦂ A
    → Δ ⊢c c ⦂ A
⊢ᵣ→⊢c {Δ}{Bs}{c}{A} (ast-r ⊢cc) = ⊢cc


data _∣_∣_⊢ᵣ₊_⦂_ {V C I : Set}
    {{_ : Shiftable V}} {{_ : FoldPreservable V C I}}
  : ∀(bs : List Sig) → List I → BTypes I bs
              → Tuple bs (Bind V C) → Vec I (length bs) → Set where
  nil-r : ∀{Δ} → [] ∣ Δ ∣ tt ⊢ᵣ₊ tt ⦂ []̌ 
  cons-r : ∀{b bs r rs Δ A As Bs Bss} → b ∣ Δ ∣ Bs ⊢ᵣ r ⦂ A
      → bs ∣ Δ ∣ Bss ⊢ᵣ₊ rs ⦂ As
      → (b ∷ bs) ∣ Δ ∣ ⟨ Bs , Bss ⟩ ⊢ᵣ₊ ⟨ r , rs ⟩ ⦂ (A ∷̌ As)

_⦂_⇒_ : ∀{V C I : Set}
    {{_ : Shiftable V}} {{_ : FoldPreservable V C I}}
    → GSubst V → List I → List I → Set
σ ⦂ Γ ⇒ Δ = ∀{x A B} → Γ ∋ x ⦂ A  →  𝑉 Γ x A B  →  Δ ⊢v σ x ⦂ B

fold-preserves : ∀{V C I : Set}
    {{_ : Shiftable V}} {{_ : FoldPreservable V C I}}
    {M : ABT}{σ : GSubst V}{Γ Δ : List I}{A : I}
   → Γ ⊢ M ⦂ A
   → σ ⦂ Γ ⇒ Δ
   → (∀ {op : Op}{Rs : Tuple (sig op) (Bind V C)}{Δ}{A : I}
        {As : Vec I (length (sig op))}{Bs}
       → sig op ∣ Δ ∣ Bs ⊢ᵣ₊ Rs ⦂ As → 𝑃 op As Bs A → Δ ⊢c (fold-op op Rs) ⦂ A)
   → Δ ⊢c fold σ M ⦂ A
fold-preserves (var-p ∋x Vx) σ⦂ op-pres = ret-pres (σ⦂ ∋x Vx)
fold-preserves {V}{C}{I}{E} (op-p ⊢args Pop) σ⦂ op-pres =
  op-pres (pres-args ⊢args σ⦂) Pop
  where
  ext-pres : ∀{v : V}{σ : GSubst V}{Γ Δ : List I}{A : I}
     → (A ∷ Δ) ⊢v v ⦂ A
     → 𝐴 (A ∷ Δ) v A
     → σ ⦂ Γ ⇒ Δ
     → (σ , v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-pres {v}{σ} ⊢v⦂ Av σ⦂ {zero}{A}{B} refl V0 = 𝑉-⊢v V0 ⊢v⦂
  ext-pres {v}{σ} ⊢v⦂ Av σ⦂ {suc x}{A}{B} ∋x Vsx = shift-⊢v (σ⦂ ∋x (prev-𝑉 Vsx))
  
  pres-arg : ∀{b Γ Δ}{arg : Arg b}{A}{σ : GSubst V}{Bs}
     → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A → σ ⦂ Γ ⇒ Δ
     → b ∣ Δ ∣ Bs ⊢ᵣ fold-arg  σ {b} arg ⦂ A
  pres-args : ∀{bs Γ Δ}{args : Args bs}{As}{σ : GSubst V}{Bss}
     → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As
     → σ ⦂ Γ ⇒ Δ
     → bs ∣ Δ ∣ Bss ⊢ᵣ₊ fold-args σ args ⦂ As
  pres-arg {b}{Γ}{Δ}{ast M}{A}{σ} (ast-p ⊢arg) σΓΔ =
      ast-r (fold-preserves ⊢arg σΓΔ op-pres)
  pres-arg {ν b}{Γ}{Δ}{bind arg}{A}{σ}{⟨ B , Bs ⟩} (bind-p {b}{B} ⊢arg)
      σΓΔ = bind-r G
      where G : ∀{v} → (B ∷ Δ) ⊢v v ⦂ B
               → 𝐴 (B ∷ Δ) v B
               → b ∣ B ∷ Δ ∣ Bs ⊢ᵣ fold-arg σ (bind arg) v ⦂ A
            G {v} ⊢v⦂B 𝐴Mv =
                pres-arg ⊢arg (λ {x} → ext-pres {v}{σ}{Γ} ⊢v⦂B 𝐴Mv σΓΔ {x})
  pres-arg {b}{Γ}{Δ}{clear arg}{A}{σ} (clear-p ⊢arg) σΓΔ =
      clear-r (pres-arg {arg = arg} ⊢arg λ { (lift ()) _ })
  pres-args {[]} {Γ} {Δ} {nil} {[]̌} ⊢args σΓΔ = nil-r 
  pres-args {b ∷ bs} {Γ} {Δ} {cons arg args} {A ∷̌ As}
      (cons-p ⊢arg ⊢args) σΓΔ =
      cons-r  (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)
  

{-
module ABTPred {I : Set}
  (𝑉 : List I → Var → I → Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set) where

  open ABTPredicate Op sig 𝑉 𝑃 public

open import MapPreserve Op sig public

{----- Predicate on result of fold (e.g. type system for values) -----}

module FoldPred {I : Set}{V : Set}{ℓ : Level}{C : Set ℓ}
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set)
  (𝐴 : List I → V → I → Set)
  (_⊢v_⦂_ : List I → V → I → Set) (_⊢c_⦂_ : List I → C → I → Set)
  where

  data _∣_∣_⊢ᵣ_⦂_ : (b : ℕ) → List I → BType I b → Bind V C b → I → Set where
    ast-r : ∀{Δ}{c}{A}  →  Δ ⊢c c ⦂ A  →  0 ∣ Δ ∣ tt ⊢ᵣ c ⦂ A
    bind-r : ∀{b A B Bs Δ f}
          → (∀{v} → (B ∷ Δ) ⊢v v ⦂ B → 𝐴 (B ∷ Δ) v B
                  → b ∣ (B ∷ Δ) ∣ Bs ⊢ᵣ (f v) ⦂ A)
          → (suc b) ∣ Δ ∣ ⟨ B , Bs ⟩ ⊢ᵣ f ⦂ A

  ⊢ᵣ→⊢c : ∀{Δ}{Bs}{c}{A}  →  0 ∣ Δ ∣ Bs ⊢ᵣ c ⦂ A  →  Δ ⊢c c ⦂ A
  ⊢ᵣ→⊢c {Δ}{Bs}{c}{A} (ast-r ⊢cc) = ⊢cc

  data _∣_∣_⊢ᵣ₊_⦂_ : ∀(bs : List ℕ) → List I → BTypes I bs
                → Tuple bs (Bind V C) → Vec I (length bs) → Set where
    nil-r : ∀{Δ} → [] ∣ Δ ∣ tt ⊢ᵣ₊ tt ⦂ []̌ 
    cons-r : ∀{b bs r rs Δ A As Bs Bss} → b ∣ Δ ∣ Bs ⊢ᵣ r ⦂ A
        → bs ∣ Δ ∣ Bss ⊢ᵣ₊ rs ⦂ As
        → (b ∷ bs) ∣ Δ ∣ ⟨ Bs , Bss ⟩ ⊢ᵣ₊ ⟨ r , rs ⟩ ⦂ (A ∷̌ As)

{-------------------- FoldEnv Preserves ABTPred ---------------------}

record FoldEnvPreserveABTPred {V Env I : Set}{ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Env V C) : Set (lsuc ℓ) where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        𝐴 : List I → V → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        _⊢c_⦂_ : List I → C → I → Set

  open FoldEnv F
  open ABTPredicate Op sig 𝑉 𝑃 public ; open FoldPred 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_ public

  _⦂_⇒_ : Env → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v lookup σ x ⦂ A
  
  field ext-pres : ∀{v σ Γ Δ A} → (A ∷ Δ) ⊢v v ⦂ A → 𝐴 (A ∷ Δ) v A
                → σ ⦂ Γ ⇒ Δ → (σ , v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
        ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c ret v ⦂ A
        op-pres : ∀ {op}{Rs}{Δ}{A : I}{As : Vec I (length (sig op))}{Bs}
             → sig op ∣ Δ ∣ Bs ⊢ᵣ₊ Rs ⦂ As
             → 𝑃 op As Bs A
             → Δ ⊢c (fold-op op Rs) ⦂ A

  preserve-fold : ∀{M σ Γ Δ A} → Γ ⊢ M ⦂ A → σ ⦂ Γ ⇒ Δ → Δ ⊢c fold σ M ⦂ A
  pres-arg : ∀{b Γ Δ}{arg : Arg b}{A σ Bs} → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A → σ ⦂ Γ ⇒ Δ
     → b ∣ Δ ∣ Bs ⊢ᵣ fold-arg  σ {b} arg ⦂ A
  pres-args : ∀{bs Γ Δ}{args : Args bs}{As σ Bss} → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As
     → σ ⦂ Γ ⇒ Δ  →  bs ∣ Δ ∣ Bss ⊢ᵣ₊ fold-args σ args ⦂ As
  preserve-fold {` x} {σ} {Γ} {Δ} {A} (var-p ∋x 𝑉x) σ⦂ = ret-pres (σ⦂ ∋x)
  preserve-fold {op ⦅ args ⦆} {σ} {Γ} {Δ} {A} (op-p ⊢args 𝑃op) σΓΔ =
      op-pres  (pres-args  ⊢args σΓΔ) 𝑃op
  pres-arg {zero}{Γ}{Δ}{ast M}{A}{σ} (ast-p ⊢arg) σΓΔ =
      ast-r (preserve-fold ⊢arg σΓΔ)
  pres-arg {suc b}{Γ}{Δ}{bind arg}{A}{σ}{⟨ B , Bs ⟩} (bind-p {b}{B} ⊢arg)
      σΓΔ = bind-r G
      where G : ∀{v} → (B ∷ Δ) ⊢v v ⦂ B
               → 𝐴 (B ∷ Δ) v B
               → b ∣ B ∷ Δ ∣ Bs ⊢ᵣ fold-arg σ (bind arg) v ⦂ A
            G {v} ⊢v⦂B 𝐴Mv =
                pres-arg ⊢arg (λ {x} → ext-pres {v}{σ}{Γ} ⊢v⦂B 𝐴Mv σΓΔ {x})
  pres-args {[]} {Γ} {Δ} {nil} {[]̌} ⊢args σΓΔ = nil-r 
  pres-args {b ∷ bs} {Γ} {Δ} {cons arg args} {A ∷̌ As}
      (cons-p ⊢arg ⊢args) σΓΔ =
      cons-r  (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)


record FunEnvPredExt {V I : Set} (_⊢v_⦂_ : List I → V → I → Set)
  (𝐴 : List I → V → I → Set) (S : Shiftable V) : Set where
  
  open Shiftable S
  field shift-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
  
  E = Var → V
  open import Environment
  open Env (Fun-is-Env {V}{{S}})

  _⦂_⇒_ : E → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v lookup σ x ⦂ A

  ext-pres : ∀{v σ Γ Δ A}
          → (A ∷ Δ) ⊢v v ⦂ A   →   𝐴 (A ∷ Δ) v A
          → σ ⦂ Γ ⇒ Δ
          → (σ , v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-pres ⊢v⦂ Av σ⦂ {zero} {B} refl = ⊢v⦂
  ext-pres {v}{σ}{Γ}{Δ}{A} ⊢v⦂ Av σ⦂ {suc x} {B} ∋x = shift-⊢v (σ⦂ ∋x)


{-------------------- Fold Preserves ABTPred ---------------------}

record FoldPreserveABTPred {V I : Set} {ℓ : Level}{C : Set ℓ}
  (F : Fold V C) : Set (lsuc ℓ) where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        𝐴 : List I → V → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        _⊢c_⦂_ : List I → C → I → Set

  open Fold F ; open GenericSubst V-is-Shiftable
  open ABTPredicate Op sig 𝑉 𝑃 public ; open FoldPred 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_ public
  open GSubstPred V-is-Shiftable _⊢v_⦂_ public

  field shift-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
        ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c ret v ⦂ A
        op-pres : ∀ {op}{Rs}{Δ}{A : I}{As : Vec I (length (sig op))}{Bs}
             → sig op ∣ Δ ∣ Bs ⊢ᵣ₊ Rs ⦂ As
             → 𝑃 op As Bs A
             → Δ ⊢c (fold-op op Rs) ⦂ A

  ext-pres : ∀{v σ Γ Δ A} → (A ∷ Δ) ⊢v v ⦂ A → 𝐴 (A ∷ Δ) v A
           → σ ⦂ Γ ⇒ Δ → (g-extend v σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-pres {v} {σ} {Γ} {Δ} {A} ⊢v⦂ Av σ⦂ {zero} {B} refl = ⊢v⦂
  ext-pres {v} {σ} {Γ} {Δ} {A} ⊢v⦂ Av σ⦂ {suc x} {B} ∋x
      rewrite g-inc-shift σ x = shift-⊢v (σ⦂ {x}{B} ∋x)

  FEPP : FoldEnvPreserveABTPred GSubst-is-FoldEnv
  FEPP = record { 𝑉 = 𝑉 ; 𝑃 = 𝑃 ; 𝐴 = 𝐴 ; _⊢v_⦂_ = _⊢v_⦂_ ; _⊢c_⦂_ = _⊢c_⦂_
           ; ext-pres = ext-pres ; ret-pres = ret-pres ; op-pres = op-pres }
  open FoldEnvPreserveABTPred FEPP
     using (preserve-fold; pres-arg; pres-args) public


-}
