{-# OPTIONS --without-K --rewriting #-}
{-
  UNDER CONSTRUCTION
-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Sig

module rewriting.examples.SystemF where

{-------------      Types    -------------}


data TypeOp : Set where
  op-fun : Op
  op-all : Op
  op-nat-ty : Op

type-sig : Op → List Sig
type-sig op-fun = ■ ∷ ■ ∷ []
type-sig op-all = (ν ■) ∷ []
type-sig op-nat-ty = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Type)

pattern Nat = op-nat-ty ⦅ nil ⦆

infixl 7  _⇒_
pattern _⇒_ A B = op-fun ⦅ cons (ast A) (cons (ast B) nil) ⦆

pattern Π A = op-all ⦅ cons (bind (ast A)) nil ⦆

{-------------      Terms    -------------}

data Op : Set where
  op-nat : ℕ → Op
  op-lam : Op
  op-app : Op
  op-tyabs : Op
  op-tyapp : Op
  op-nu : Op

sig : Op → List Sig
sig (op-nat n) = []
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-tyabs = (ν ■) ∷ []
sig (op-tyapp B) = ■ ∷ ■ ∷ []
sig (op-nu B) = ■ ∷ (ν ■) ∷ []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term)

pattern $ n = (op-nat n) ⦅ nil ⦆
pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern Λ N  = op-tyabs ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _․_
pattern _․_ L A = op-tyapp ⦅ cons (ast L) (cons (ast A) nil) ⦆
pattern ν A N  = op-nu A ⦅ cons (ast A) (cons (bind (ast N)) nil) ⦆


{-------------      Reduction Semantics    -------------}

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

    
infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M : Term}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {L M M′ : Term}
    → Value L
    → M —→ M′
      ---------------
    → L · M —→ L · M′

  ξ-ƛ : ∀ {N N′ : Term}
    → N —→ N′
      ---------------
    → (ƛ N) —→ (ƛ N′)

  β-ƛ : ∀ {N M : Term}
      --------------------
    → (ƛ N) · M —→ N [ M ]

  ξ-․ : ∀ {L L′ : Term}{A : Type}
    → L —→ L′
      ---------------
    → L ․ A —→ L′ ․ A
    
  β-Λ : ∀ {N : Term} {A : Type}
      ------------------
    → (Λ N) ․ A —→ ν A N

{-------------      Type System    -------------}

open import Var

data Cat : Set where
  trm : Type → Cat    {- trm A means: a term of type A -}
  typ : Type → Cat    {- typ A means: a type which is A -}

TyEnv : Set
TyEnv = List Cat

data 𝑃 : (op : Op) → Vec Cat (length (sig op)) → BTypes Cat (sig op) → Cat → Set where
  𝑃-nat : ∀{n} → 𝑃 (op-nat n) []̌ tt (trm Nat)
{-
   Γ, trm A ⊢ N : trm B
   ---------------------
   Γ ⊢ ƛ N ⦂ trm (A ⇒ B)
-}
  𝑃-lam : ∀{A B} → 𝑃 op-lam (trm B ∷̌ []̌) ⟨ ⟨ trm A , tt ⟩ , tt ⟩ (trm (A ⇒ B))
{-
   Γ ⊢ L : trm (A → B)
   Γ ⊢ M : trm A
   -----------------
   Γ ⊢ L · M ⦂ trm B
-}
  𝑃-app : ∀{A B} → 𝑃 op-app (trm (A ⇒ B) ∷̌ trm A ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ (trm B)
{-
   Γ, typ ⊢ N : trm A
   ----------------
   Γ ⊢ Λ N ⦂ trm (Π A)
-}
  𝑃-tyabs : ∀{A B} → 𝑃 op-tyabs (trm A ∷̌ []̌) ⟨ ⟨ typ B , tt ⟩ , tt ⟩ (trm (Π A))
{-
   Γ ⊢ L : trm (Π A)
   Γ ⊢ B : typ B
   -----------------
   Γ ⊢ L ․ B ⦂ trm A [ B ]
-}
  𝑃-tyapp : ∀{A B}
     → 𝑃 op-tyapp (trm (Π A) ∷̌ typ B ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ (trm (A [ B ]))
{-
   Γ , typ ⊢ N : trm A
   Γ ⊢ B : typ B
   -----------------
   Γ ⊢ nu B N ⦂ trm A [ B ]
-}
  𝑃-nu : ∀{A B}
     → 𝑃 op-nu (trm (Π A) ∷̌ typ B ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ (trm (A [ B ]))
{-
  Γ ⊢ A ⦂ typ A
  Γ ⊢ B ⦂ typ B
  -----------------------
  Γ ⊢ A ⇒ B ⦂ typ (A ⇒ B)
-}
  𝑃-fun : ∀{A B} → 𝑃 op-fun  (typ A ∷̌ typ B ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ (typ (A ⇒ B))
{-
  Γ, typ B ⊢ A ⦂ typ A
  ---------------------
  Γ ⊢ Π A ⦂ typ (Π A)
-}
  𝑃-all : ∀{A B} → 𝑃 op-all (typ A ∷̌ []̌) ⟨ ⟨ typ B , tt ⟩ , tt ⟩ (typ (Π A))
{-
  -----------------
  Γ ⊢ Nat ⦂ typ Nat
-}
  𝑃-nat-ty : 𝑃 op-nat-ty []̌ tt (typ Nat)

open import rewriting.ABTPredicate Op sig 𝑃

{-------------      Type System Rules    -------------}

pattern ⊢` ∋x = var-p ∋x
pattern ⊢$ n = op-p {op = op-nat n} nil-p 𝑃-nat
pattern ⊢ƛ ⊢N = op-p {op = op-lam} (cons-p (bind-p (ast-p ⊢N)) nil-p)  𝑃-lam
pattern ⊢· ⊢L ⊢M = op-p {op = op-app}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) 𝑃-app
pattern ⊢Λ ⊢N = op-p {op = op-tyabs} (cons-p (bind-p (ast-p ⊢N)) nil-p) 𝑃-tyabs
pattern ⊢․ ⊢L ⊢A = op-p {op = op-tyapp}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢A) nil-p)) 𝑃-tyapp
pattern ⊢ℕ = op-p {op = op-nat-ty} nil-p 𝑃-nat-ty
pattern ⊢⇒ ⊢A ⊢B = op-p {op = op-fun}
                           (cons-p (ast-p ⊢A) (cons-p (ast-p ⊢B) nil-p)) 𝑃-fun
pattern ⊢Π ⊢A = op-p {op = op-all} (cons-p (bind-p (ast-p ⊢A)) nil-p) 𝑃-all

{-------------      Proof of Progress    -------------}

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M


nat-not-fun : ∀{Γ n A B} → Γ ⊢ $ n ⦂ trm (A ⇒ B) → ⊥
nat-not-fun (op-p _ ())

Λ-not-fun : ∀{Γ N A B} → Γ ⊢ Λ N ⦂ trm (A ⇒ B) → ⊥
Λ-not-fun (op-p _ ())

ƛ-not-all : ∀{Γ N A} → Γ ⊢ ƛ N ⦂ trm (Π A) → ⊥
ƛ-not-all (op-p _ ())

nat-not-all : ∀{Γ n A} → Γ ⊢ $ n ⦂ trm (Π A) → ⊥
nat-not-all (op-p _ ())

progress : ∀ {M A}
  → [] ⊢ M ⦂ trm A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢$ n)                      = done V-nat
progress (⊢ƛ ⊢N)                     =  done V-ƛ
progress (⊢· ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                    =  step (ξ-·₁ L—→L′)
... | done V-ƛ                      =  step β-ƛ
... | done V-nat                    = ⊥-elim (nat-not-fun ⊢L)
... | done V-Λ                      = ⊥-elim (Λ-not-fun ⊢L)
progress (⊢Λ ⊢N)                    =  done V-Λ
progress (⊢․ ⊢L ⊢A)
    with progress ⊢L
... | step L—→L′                    = step (ξ-․ L—→L′)
... | done V-ƛ                      = ⊥-elim (ƛ-not-all ⊢L)
... | done V-nat                    = ⊥-elim (nat-not-all ⊢L)
... | done V-Λ                      = step β-Λ

{-------------      Proof of Preservation    -------------}

preserve : ∀ {Γ M N A}
  → Γ ⊢ M ⦂ A
  → M —→ N
    ----------
  → Γ ⊢ N ⦂ A
preserve (⊢· ⊢L ⊢M) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M
preserve (⊢· ⊢L ⊢M) (ξ-·₂ x M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) 
preserve (⊢ƛ ⊢M) (ξ-ƛ M—→N) = ⊢ƛ (preserve ⊢M M—→N)
preserve (⊢· (⊢ƛ ⊢N) ⊢M) β-ƛ = preserve-substitution _ _ ⊢N ⊢M
preserve (⊢․ ⊢L ⊢A) (ξ-․ L—→L′) = ⊢․ (preserve ⊢L L—→L′) ⊢A
preserve (⊢․ (⊢Λ ⊢N) ⊢A) β-Λ = {!!}
  
{-
preserve (⊢· ⊢L ⊢M) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M 
preserve (⊢· ⊢L ⊢M) (ξ-·₂ vL M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) 
preserve (⊢ƛ ⊢M) (ξ-ƛ M—→N) = ⊢ƛ (preserve ⊢M M—→N) 
preserve {Γ}{(ƛ N) · M}{_}{B} ⊢λN·M β-ƛ = {!!}
preserve-substitution N M ⊢N ⊢M
-}
