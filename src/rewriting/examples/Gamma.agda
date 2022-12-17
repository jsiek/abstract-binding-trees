{-# OPTIONS --without-K --rewriting #-}
{-
  Intermediate language prior to key step in closure conversion.
-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Var
open import Sig
open import rewriting.examples.Denot

module rewriting.examples.Gamma where

data Op : Set where
  op-gamma : Op
  op-app : Op
  op-lit : ℕ → Op
  op-cons : Op
  op-fst : Op
  op-snd : Op

sig : Op → List Sig
sig op-gamma = ν (ν ■) ∷ ■ ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit k) = []
sig op-cons = ■ ∷ ■ ∷ []
sig op-fst = ■ ∷ []
sig op-snd = ■ ∷ []

open import rewriting.AbstractBindingTree Op sig hiding (`_)
open import rewriting.AbstractBindingTree Op sig
  using (`_) renaming (ABT to Term) public

pattern $ k  = op-lit k ⦅ nil ⦆

pattern γ N M  = op-gamma ⦅ cons (bind (bind (ast N))) (cons (ast M) nil) ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

infixl 7  ⟨_,_⟩
pattern ⟨_,_⟩ L M = op-cons ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern fst L = op-fst ⦅ (cons (ast L) nil) ⦆

pattern snd L = op-snd ⦅ (cons (ast L) nil) ⦆

⟦_⟧ : Term → (List D) → D
⟦ ` x ⟧ ρ = nth x ρ ⊥′
⟦ $ k ⟧ ρ v = (v ≡ lit k)
⟦ γ N M ⟧ ρ w = (∃[ v ] ⟦ M ⟧ ρ v) × (Λ (λ D → ⟦ N ⟧ (⟦ M ⟧ ρ ∷ D ∷ [])) w)
⟦ L · M ⟧ ρ = ⟦ L ⟧ ρ ● ⟦ M ⟧ ρ 
⟦ ⟨ L , M ⟩ ⟧ ρ =  ⦅ ⟦ L ⟧ ρ , ⟦ M ⟧ ρ ⦆
⟦ fst L ⟧ ρ = π₁ (⟦ L ⟧ ρ)
⟦ snd L ⟧ ρ = π₂ (⟦ L ⟧ ρ)


