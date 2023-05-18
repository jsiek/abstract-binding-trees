{-# OPTIONS --rewriting #-}
{-
  UNDER CONSTRUCTION
-}

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

module rewriting.examples.SystemF where

{-------------      Types    -------------}


data TypeOp : Set where
  op-fun : TypeOp
  op-all : TypeOp
  op-nat-ty : TypeOp

type-sig : TypeOp → List Sig
type-sig op-fun = ■ ∷ ■ ∷ []
type-sig op-all = (ν ■) ∷ []
type-sig op-nat-ty = []

open import rewriting.AbstractBindingTree TypeOp type-sig
  using ()
  renaming (ABT to Type; Rename to Renameᵗ; Subst to Substᵗ;
            ren to renᵗ; ren-def to ren-defᵗ; extr to extrᵗ; ext to extᵗ;
            ⟪_⟫ to ⟪_⟫ᵗ; sub-var to sub-varᵗ; seq-def to seq-defᵗ; ↑ to ↑ᵗ;
            _[_] to _⦗_⦘; _⦅_⦆ to _‹_›; _•_ to _•ᵗ_; id to idᵗ; _⨟_ to _⨟ᵗ_;
            nil to tnil; cons to tcons; bind to tbind; ast to tast; `_ to ^_) public

pattern Nat = op-nat-ty ‹ tnil ›

infixl 7  _⇒_
pattern _⇒_ A B = op-fun ‹ tcons (tast A) (tcons (tast B) tnil) ›

pattern ∀̇ A = op-all ‹ tcons (tbind (tast A)) tnil ›

{-------------      Terms    -------------}

data Op : Set where
  op-nat : ℕ → Op
  op-lam : Op
  op-app : Op
  op-tyabs : Op
  op-tyapp : Op

sig : Op → List Sig
sig (op-nat n) = []
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-tyabs = ■ ∷ []
sig op-tyapp = ■ ∷ []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern $ n = (op-nat n) ⦅ nil ⦆
pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern Λ N  = op-tyabs ⦅ cons (ast N) nil ⦆
pattern _[·] L = op-tyapp ⦅ cons (ast L) nil ⦆

{----------------------- Values ------------------------}

data Value : Term → Set where

  V-nat : ∀ {n : ℕ}
      -------------
    → Value ($ n)
    
  V-ƛ : ∀ {N : Term}
      ---------------------------
    → Value (ƛ N)

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

  □[·] : Frame

  ƛ□ : Frame

_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
□[·] ⟦ M ⟧          =  M [·]
ƛ□ ⟦ M ⟧            =  ƛ M

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

  β-ƛ : ∀ {N M : Term}
      --------------------
    → (ƛ N) · M —→ N [ M ]

  β-Λ : ∀ {N : Term}
      ------------------
    → (Λ N) [·] —→ N

pattern ξ F M—→N = ξξ F refl refl M—→N

