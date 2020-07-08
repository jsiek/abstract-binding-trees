open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
   using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n; _≤?_)
open import Data.Nat.Properties
    using (+-comm; +-suc; ≤-pred; m≤m+n; ≤⇒≯; suc-injective)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)

module Syntax where

open import Var public
open import Substitution public

module OpSig (Op : Set) (sig : Op → List ℕ)  where

  open import AbstractBindingTree Op sig public
  open Substitution.ABTOps Op sig public
  open import WellScoped Op sig public

