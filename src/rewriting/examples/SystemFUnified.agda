{-# OPTIONS --rewriting #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; map; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤?_)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Function using (_∘_)
open import Sig

module rewriting.examples.SystemFUnified where

{-------------      Types and Terms    -------------}


data Op : Set where
  {-- types --}
  op-fun-ty : Op
  op-all-ty : Op
  op-nat-ty : Op
  {-- terms --}
  op-nat : ℕ → Op
  op-lam : Op
  op-app : Op
  op-tyabs : Op
  op-tyapp : Op

sig : Op → List Sig
sig op-fun-ty = ■ ∷ ■ ∷ []
sig op-all-ty = (ν ■) ∷ []
sig op-nat-ty = []
sig (op-nat n) = []
sig op-lam = ■ ∷ (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-tyabs = ■ ∷ []
sig op-tyapp = ■ ∷ ■ ∷ []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern Nat = op-nat-ty ⦅ nil ⦆
infixl 7  _⇒_
pattern _⇒_ A B = op-fun-ty ⦅ cons (ast A) (cons (ast B) nil) ⦆
pattern ∀̇ A = op-all-ty ⦅ cons (bind (ast A)) nil ⦆

pattern $ n = (op-nat n) ⦅ nil ⦆
pattern ƛ A N  = op-lam ⦅ cons (ast A) (cons (bind (ast N)) nil) ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern Λ N  = op-tyabs ⦅ cons (ast N) nil ⦆
pattern _❲_❳ L A = op-tyapp ⦅ cons (ast L) (cons (ast A) nil) ⦆

{----------------------- Values ------------------------}

data Value : Term → Set where

  V-nat : ∀ {n : ℕ}
      -------------
    → Value ($ n)
    
  V-ƛ : ∀ {A N : Term}
      ---------------------------
    → Value (ƛ A N)

  V-Λ : ∀ {N : Term}
      ---------------------------
    → Value (Λ N)
    
value : ∀ {V : Term}
  → (v : Value V)
    -------------
  → Term
value {V = V} v  =  V  

{----------------------- Frames ------------------------}

infix  6 □·_
infix  6 _·□

data Frame : Set where

  □·_ : 
      (M : Term)
      ----------
    → Frame

  _·□ : ∀ {V : Term}
    → (v : Value V)
      -------------
    → Frame

  □[_] :
      (A : Term)
      ----------
    → Frame

  ƛ_□ : 
      (A : Term)
      ----------
    → Frame

_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
□[ A ] ⟦ M ⟧        =  M ❲ A ❳
ƛ A □ ⟦ M ⟧         =  ƛ A M

{-------------      Reduction Semantics    -------------}

infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξξ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ M ⟧
    → N′ ≡ F ⟦ N ⟧
    → M —→ N
      --------
    → M′ —→ N′

  β-ƛ : ∀ {A N M : Term}
      ----------------------
    → (ƛ A N) · M —→ N [ M ]

  β-Λ : ∀ {A N : Term}
      ----------------------
    → (Λ N) ❲ A ❳ —→ N [ A ]

pattern ξ F M—→N = ξξ F refl refl M—→N

{-------------      Type System    -------------}

