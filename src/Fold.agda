{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_) renaming (map to lmap)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product
    using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (levelOfType)
open import Structures
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var
open import ScopedTuple
    using (Tuple; map; _✖_; zip; zip-refl; map-pres-zip; map-compose-zip;
           map-compose; zip-map→rel; Lift-Eq-Tuple; Lift-Rel-Tuple; zip→rel)
open import GSubst
open import GenericSubstitution
open import Sig

module Fold (Op : Set) (sig : Op → List Sig) where

open import AbstractBindingTree Op sig
open Structures.WithOpSig Op sig

private
  variable
    ℓ : Level
    V V₁ V₂ C C₁ C₂ : Set ℓ

{-------------------------------------------------------------------------------
 Folding over an abstract binding tree
 ------------------------------------------------------------------------------}

fold : {{_ : Shiftable V}} {{_ : Foldable V C}}
   → GSubst V → ABT → C
fold-arg : {{_ : Shiftable V}} {{_ : Foldable V C}}
   → GSubst V → {b : Sig} → Arg b → Bind V C b
fold-args : {{_ : Shiftable V}} {{_ : Foldable V C}}
   → GSubst V → {bs : List Sig} → Args bs → Tuple bs (Bind V C)

fold σ (` x) = ret (σ x)
fold σ (op ⦅ args ⦆) = fold-op op (fold-args σ {sig op} args)
fold-arg σ (ast M) = lift (fold σ M)
fold-arg σ (bind arg) v = fold-arg (σ , v) arg
fold-arg σ (clear arg) = fold-arg id arg
fold-args σ {[]} nil = tt
fold-args σ {b ∷ bs} (cons arg args) = ⟨ fold-arg σ arg , fold-args σ args ⟩

{-------------------------------------------------------------------------------
 Simulation between two folds
 ------------------------------------------------------------------------------}

_≅_ : {{_ : Equiv V₁ V₂}}
   (σ₁ : GSubst V₁) (σ₂ : GSubst V₂) → Set (levelOfType V₁ ⊔ levelOfType V₂)
_≅_ σ₁ σ₂ = ∀ x → σ₁ x ≈ σ₂ x

sim-ext : {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{v₁ : V₁}{v₂ : V₂}
  {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
  {{_ : Relatable V₁ V₂}}
   → σ₁ ≅ σ₂ → v₁ ≈ v₂ → (σ₁ , v₁) ≅ (σ₂ , v₂)
sim-ext {σ₁} {σ₂} {v₁} {v₂} σ₁≅σ₂ v₁≈v₂ zero = v₁≈v₂
sim-ext {σ₁} {σ₂} {v₁} {v₂} σ₁≅σ₂ v₁≈v₂ (suc x) = shift≈ (σ₁≅σ₂ x)
    
sim : ∀ {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}
   {{S1 : Shiftable V₁}} {{S2 : Shiftable V₂}}
   {{F1 : Foldable V₁ C₁}} {{F2 : Foldable V₂ C₂}}
   {{EqV : Equiv V₁ V₂}} {{EqC : Equiv C₁ C₂}} {{Sim : Similar V₁ V₂ C₁ C₂}}
   → (M : ABT)
   → σ₁ ≅ σ₂
   → (fold σ₁ M) ≈ (fold σ₂ M)

sim-arg : ∀ {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{b} (arg : Arg b)
   {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
   {{_ : Foldable V₁ C₁}} {{_ : Foldable V₂ C₂}}
   {{_ : Equiv C₁ C₂}} {{_ : Similar V₁ V₂ C₁ C₂}}
   → σ₁ ≅ σ₂ → (_⩳_ {b = b}) (fold-arg σ₁ {b} arg) (fold-arg σ₂ {b} arg)

sim-args : ∀ {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{bs} (args : Args bs)
   {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
   {{_ : Foldable V₁ C₁}} {{_ : Foldable V₂ C₂}}
   {{_ : Equiv C₁ C₂}} {{_ : Similar V₁ V₂ C₁ C₂}}   
   → σ₁ ≅ σ₂
   → zip (λ {b} → _⩳_{V₁ = V₁}{V₂}{C₁}{C₂}{b = b}) (fold-args σ₁ {bs} args)
                   (fold-args σ₂ {bs} args)

sim (` x) σ₁≅σ₂ = ret≈ (σ₁≅σ₂ x)
sim {V₁ = V₁}{V₂}{C₁}{C₂}{σ₁}{σ₂} (op ⦅ args ⦆) σ₁≅σ₂ =
    op⩳ (sim-args args σ₁≅σ₂)

sim-arg (ast M) σ₁≊σ₂ = lift (sim M σ₁≊σ₂)
sim-arg {b = ν b} (bind arg) σ₁≊σ₂ v₁≈v₂ = 
    sim-arg {b = b} arg (sim-ext σ₁≊σ₂ v₁≈v₂)
sim-arg (clear arg) σ₁≊σ₂ = sim-arg arg λ x → var→val≈ x

sim-args {bs = []} args σ₁≊σ₂ = tt
sim-args {bs = b ∷ bs} (cons arg args) σ₁≊σ₂ =
    ⟨ sim-arg arg σ₁≊σ₂ , sim-args args σ₁≊σ₂ ⟩


fold-refl : ∀ {σ : GSubst V}
   {{_ : Shiftable V}} {{_ : Foldable V C}}
   {{_ : Equiv C C}} {{_ : Similar V V C C}}
   → (M : ABT)
   → σ ≅ σ
   → fold σ M ≈ fold σ M
fold-refl M σ≅σ = sim M σ≅σ

fold-arg-refl : ∀ {σ : GSubst V}{b} (arg : Arg b)
   {{_ : Shiftable V}} {{_ : Foldable V C}}
   {{_ : Equiv C C}} {{_ : Similar V V C C}}
   → σ ≅ σ → (_⩳_ {b = b}) (fold-arg σ {b} arg) (fold-arg σ {b} arg)
fold-arg-refl arg σ≅σ = sim-arg arg σ≅σ


{-------------------------------------------------------------------------------
 FV of fold
 ------------------------------------------------------------------------------}

fv-env : {{_ : SyntacticFold V C}} → GSubst V → Var → Set
fv-env γ x = Σ[ y ∈ Var ] fvᵛ (γ y) x


fv-bind : {{_ : SyntacticFold V C}} {b : Sig} → Bind V C b → Var → Set
fv-bind {b = ■} (lift r) x = fvᶜ r x
fv-bind {b = ν b} r x = fv-bind {b = b} (r (var→val 0)) (suc x)
fv-bind {b = ∁ b} r x = ⊥

fv-binds : {{_ : SyntacticFold V C}} {bs : List Sig}
    → Tuple bs (Bind V C) → Var → Set
fv-binds {bs = []} tt x = ⊥
fv-binds {bs = b ∷ bs} ⟨ r , rs ⟩ x = fv-bind {b = b} r x ⊎ fv-binds rs x

FV-fold : {{_ : SyntacticFold V C}}
     (γ : GSubst V) (M : ABT) (x : Var)
   → ((γ : GSubst V) (op : Op) (args : Args (sig op)) (x : Var)
      → fvᶜ (fold-op op (fold-args γ args)) x
      → fv-binds (fold-args γ args) x)
   → fvᶜ (fold γ M) x
   → fv-env γ x

FV-fold γ (` y) x fv-op fv-fold rewrite fv-ret (γ y) = ⟨ y , fv-fold ⟩
FV-fold {V = V}{C} γ (op ⦅ args ⦆) x fv-op fv-fold =
    FV-fold-args γ args x (fv-op γ op args x fv-fold)
  where
  FV-fold-arg : ∀ (γ : GSubst V) {b : Sig} (arg : Arg b) (x : Var)
     → fv-bind {b = b} (fold-arg γ arg) x → fv-env γ x
  FV-fold-arg γ (ast M) x fv-fold = FV-fold γ M x fv-op fv-fold
  FV-fold-arg γ (bind arg) x fv-fold 
      with FV-fold-arg (γ , var→val 0) arg (suc x) fv-fold
  ... | ⟨ suc y , fvγ'y ⟩ = ⟨ y , fv-shift (γ y) x fvγ'y ⟩
  ... | ⟨ 0 , fvγ'y ⟩ rewrite fv-var→val {V = V} 0 (suc x)
      with fvγ'y
  ... | ()
  FV-fold-arg γ (clear arg) x ()
  
  FV-fold-args : ∀ (γ : GSubst V) {bs : List Sig} (args : Args bs) (x : Var)
     → fv-binds (fold-args γ args) x → fv-env γ x
  FV-fold-args γ nil x ()
  FV-fold-args γ (cons arg args) x (inj₁ fv-fld) = FV-fold-arg γ arg x fv-fld
  FV-fold-args γ (cons arg args) x (inj₂ fv-fld) = FV-fold-args γ args x fv-fld 
