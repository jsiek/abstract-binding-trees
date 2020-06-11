{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Size using (Size)
open import Var
open import experimental.ScopedTuple using (map; map-cong; map-compose)
open import GenericSubstitution

module experimental.Map2 (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig

{-------------------------------------------------------------------------------
 Mapping a substitution over an abstract binding tree
 (generalizes renaming and substitution)
 ------------------------------------------------------------------------------}

record Map (V : Set) : Set where
  field S : Substable V
        “_” : V → ABT
  open Substable S public
  open GenericSubst S

{- Termination problem
  map-abt : GSubst V → ABT → ABT
  map-arg : GSubst V → (b : ℕ) →  Arg b → Arg b
  
  map-abt σ (` x) = “ ⧼ σ ⧽ x ”
  map-abt σ (op ⦅ args ⦆) = op ⦅ map₊ (λ {b} → map-arg σ b) args ⦆
  map-arg σ zero (ast M) = ast (map-abt σ M)
  map-arg σ (suc b) (bind M) = bind (map-arg (g-ext σ) b M)
-}

  map-abt : GSubst V → ABT → ABT
  map-arg : GSubst V → (b : ℕ) →  Arg b → Arg b
  map-args : GSubst V → (bs : List ℕ) →  Args bs → Args bs
  
  map-abt σ (` x) = “ ⧼ σ ⧽ x ”
  map-abt σ (op ⦅ args ⦆) = op ⦅ map-args σ (sig op) args ⦆
  map-arg σ zero (ast M) = ast (map-abt σ M)
  map-arg σ (suc b) (bind M) = bind (map-arg (g-ext σ) b M)
  map-args σ [] nil = nil
  map-args σ (b ∷ bs) (cons x args) = cons (map-arg σ b x) (map-args σ bs args)

