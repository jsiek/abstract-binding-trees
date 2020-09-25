{-# OPTIONS --without-K #-}
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

module ABTPredicate {ℓ}{I : Set ℓ}
  (Op : Set) (sig : Op → List Sig)
  (𝑉 : List I → Var → I → I → Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set) where

open import AbstractBindingTree Op sig

private
  variable
    x : Var
    b : Sig
    A B : I
    Γ : List I
    M : ABT

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

  clear-p : ∀{Bs arg}
     → b ∣ [] ∣ Bs ⊢ₐ arg ⦂ A
     → ∁ b ∣ Γ ∣ Bs ⊢ₐ clear arg ⦂ A

data _∣_∣_⊢₊_⦂_ where
  nil-p : [] ∣ Γ ∣ tt ⊢₊ nil ⦂ []̌ 
  cons-p : ∀{bs}{arg args}{As}{Bs}{Bss}
     → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A  →  bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As
     → (b ∷ bs) ∣ Γ ∣ ⟨ Bs , Bss ⟩ ⊢₊ cons arg args ⦂ (A ∷̌ As)
