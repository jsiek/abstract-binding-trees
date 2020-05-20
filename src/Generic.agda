{-

  Experiments in generic functions and theorems over abstract binding trees.

  Trying to draw inspiration from "A Type and Scope Safe Universe of Syntaxes with Biding", ICFP 2018.

-}

{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import Syntax

module Generic where

module GenericSub 
  (Op : Set)
  (sig : Op → List ℕ)
  (V : Set)
  (var→val : Var → V)
  (apply : Substitution V → V → V)
  where

  ⧼_⧽ : Substitution V → Var → V
  ⧼ ↑ k ⧽ x = var→val (k + x)
  ⧼ y • σ ⧽ 0 = y
  ⧼ y • σ ⧽ (suc x) = ⧼ σ ⧽ x

  drop : (k : ℕ) → Substitution V → Substitution V
  drop k (↑ k') = ↑ (k + k')
  drop zero (x • σ) = x • σ
  drop (suc k) (x • σ) = drop k σ

  infixr 5 _⨟_

  _⨟_ : Substitution V → Substitution V → Substitution V
  ↑ k ⨟ σ = drop k σ
  (v • σ₁) ⨟ σ₂ = (apply σ₂ v) • (σ₁ ⨟ σ₂)


module ArgResult (V : Set) (C : Set) where

  ArgRes : ℕ → Set
  ArgRes 0 = C
  ArgRes (suc n) = V → ArgRes n

  data ArgsRes : List ℕ → Set where
    rnil : ArgsRes []
    rcons : ∀{b bs} → ArgRes b → ArgsRes bs → ArgsRes (b ∷ bs)


record Foldable (V : Set) (C : Set) (Op : Set) (sig : Op → List ℕ) : Set where
  open ArgResult V C
  field ret : V → C
  field fold-free-var : Var → V
  field fold-op : (o : Op) → ArgsRes (sig o) → C
  field apply-subst : Substitution V → V → V


module Folder {V}{C}{Op}{sig} (F : Foldable V C Op sig) where

  open OpSig Op sig hiding (_⨟_)
  open Foldable F
  open GenericSub Op sig V fold-free-var apply-subst public
  open ArgResult V C

  fold : Substitution V → ABT → C
  fold-arg : ∀{b} → Substitution V → Arg b → ArgRes b
  fold-args : ∀{bs} → Substitution V → Args bs → ArgsRes bs

  fold σ (` x) = ret (⧼ σ ⧽ x)
  fold σ (o ⦅ args ⦆) = fold-op o (fold-args σ args)

  fold-arg σ (ast M) = fold σ M
  fold-arg σ (bind M) = λ v → fold-arg (v • (σ ⨟ ↑ 1)) M

  fold-args σ nil = rnil
  fold-args σ (cons arg args) = rcons (fold-arg σ arg) (fold-args σ args)


module SimAux {Op sig}{V₁ C₁ : Set} {V₂ C₂ : Set}
  (_∼_ : V₁ → V₂ → Set)
  (_≈_ : C₁ → C₂ → Set)
  where
  
  open import Syntax
  open OpSig Op sig hiding (_⨟_; drop)
  
  data _≊_ : Substitution V₁ → Substitution V₂ → Set where
     r-up : ∀{k} → (↑ k) ≊ (↑ k)
     r-cons : ∀{v₁ σ₁ v₂ σ₂}
        → v₁ ∼ v₂
        → σ₁ ≊ σ₂
        → (v₁ • σ₁) ≊ (v₂ • σ₂)
  
  open ArgResult V₁ C₁ renaming (ArgRes to ArgRes₁; ArgsRes to ArgsRes₁; rnil to rnil₁; rcons to rcons₁) public
  open ArgResult V₂ C₂ renaming (ArgRes to ArgRes₂; ArgsRes to ArgsRes₂; rnil to rnil₂; rcons to rcons₂) public
  
  ArgRes∼ : ∀ {b} → ArgRes₁ b → ArgRes₂ b → Set 
  ArgRes∼ {zero} c₁ c₂ = c₁ ≈ c₂
  ArgRes∼ {suc b} f₁ f₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → ArgRes∼ (f₁ v₁) (f₂ v₂)
  
  data ArgsRes∼ : {bs : List ℕ} → ArgsRes₁ bs → ArgsRes₂ bs → Set where
    rnil∼ : ArgsRes∼ rnil₁ rnil₂
    rcons∼ : ∀{b bs}{r₁ rs₁}{r₂ rs₂}
        → ArgRes∼ r₁ r₂
        → ArgsRes∼ rs₁ rs₂
        → ArgsRes∼ {b ∷ bs} (rcons₁ r₁ rs₁) (rcons₂ r₂ rs₂)

record Related {Op sig}{V₁ C₁} {V₂ C₂}
  (F₁ : Foldable V₁ C₁ Op sig)
  (F₂ : Foldable V₂ C₂ Op sig)
  : Set₁ where
  field _∼_ : V₁ → V₂ → Set
  field _≈_ : C₁ → C₂ → Set
  open SimAux {Op}{sig} _∼_ _≈_
  open Foldable F₁ renaming (fold-free-var to ffvar₁; ret to ret₁; apply-subst to app₁; fold-op to fop₁)
  open Foldable F₂ renaming (fold-free-var to ffvar₂; ret to ret₂; apply-subst to app₂; fold-op to fop₂)
  field ret≈ : ∀{v₁ v₂} → v₁ ∼ v₂ → ret₁ v₁ ≈ ret₂ v₂
  field vars∼ : ∀{x} → ffvar₁ x ∼ ffvar₂ x
  field op∼ : ∀{op : Op}{Rs₁ : ArgsRes₁ (sig op)}{Rs₂ : ArgsRes₂ (sig op)} → ArgsRes∼ Rs₁ Rs₂ → fop₁ op Rs₁ ≈ fop₂ op Rs₂
  field apply∼ : ∀{v₁ v₂ τ₁ τ₂} → v₁ ∼ v₂ → τ₁ ≊ τ₂ → app₁ τ₁ v₁ ∼ app₂ τ₂ v₂

module Simulator {Op sig}{V₁ C₁} {V₂ C₂}
  (F₁ : Foldable V₁ C₁ Op sig)
  (F₂ : Foldable V₂ C₂ Op sig)
  (R : Related F₁ F₂)
  where

  module Folder₁ = Folder F₁
  fold₁ = Folder₁.fold
  _⨟₁_ = Folder₁._⨟_
  drop₁ = Folder₁.drop
  
  module Folder₂ = Folder F₂
  fold₂ = Folder₂.fold
  _⨟₂_ = Folder₂._⨟_
  drop₂ = Folder₂.drop

  open Related R
  open SimAux {Op}{sig} _∼_ _≈_

  open import Syntax
  open OpSig Op sig hiding (_⨟_; drop)

  ≊-drop : ∀{σ₁}{σ₂}{k : ℕ}
    → σ₁ ≊ σ₂
    → drop₁ k σ₁ ≊ drop₂ k σ₂
  ≊-drop {.(↑ _)} {.(↑ _)} {k} r-up = r-up
  ≊-drop {.(_ • _)} {.(_ • _)} {zero} (r-cons v₁∼v₂ σ₁≊σ₂) = r-cons v₁∼v₂ σ₁≊σ₂
  ≊-drop {.(_ • _)} {.(_ • _)} {suc k} (r-cons x σ₁≊σ₂) = ≊-drop σ₁≊σ₂

  ≊-⨟ : ∀{σ₁}{τ₁}{σ₂}{τ₂}
    → σ₁ ≊ σ₂
    → τ₁ ≊ τ₂
    → (σ₁ ⨟₁ τ₁) ≊ (σ₂ ⨟₂ τ₂)
  ≊-⨟ (r-up{k = k}) τ₁≊τ₂ = ≊-drop τ₁≊τ₂
  ≊-⨟ (r-cons v₁∼v₂ σ₁≊σ₂) τ₁≊τ₂ =
      let IH = ≊-⨟ σ₁≊σ₂ τ₁≊τ₂ in
      r-cons (apply∼ v₁∼v₂ τ₁≊τ₂) IH

  sim : ∀{M}{σ₁ σ₂}
     → σ₁ ≊ σ₂
     → (fold₁ σ₁ M) ≈ (fold₂ σ₂ M)
     
  sim-arg : ∀{σ₁}{σ₂}{b}{arg : Arg b}
     → σ₁ ≊ σ₂
     → ArgRes∼ (Folder₁.fold-arg σ₁ arg) (Folder₂.fold-arg σ₂ arg)
  sim-arg {σ₁} {σ₂} {zero} {ast M} σ₁≊σ₂ = sim {M} σ₁≊σ₂ 
  sim-arg {σ₁} {σ₂} {suc b} {bind arg} σ₁≊σ₂ {v₁}{v₂} v₁∼v₂ =
     sim-arg {v₁ • (σ₁ ⨟₁ ↑ 1)}{v₂ • (σ₂ ⨟₂ ↑ 1)}{b} {arg} (r-cons v₁∼v₂ (≊-⨟ σ₁≊σ₂ r-up))

  sim-args : ∀{σ₁}{σ₂}{bs}{args : Args bs}
     → σ₁ ≊ σ₂
     → ArgsRes∼ (Folder₁.fold-args σ₁ args) (Folder₂.fold-args σ₂ args)
  sim-args {σ₁} {σ₂} {[]} {nil} σ₁≊σ₂ = rnil∼
  sim-args {σ₁} {σ₂} {b ∷ bs} {cons A As} σ₁≊σ₂ =
    let sa = sim-arg {arg = A} σ₁≊σ₂ in
    rcons∼ sa (sim-args {σ₁} {σ₂} {bs} {As} σ₁≊σ₂)

  sim {` x} {↑ k} {.(↑ _)} r-up = ret≈ vars∼
  sim {` zero} {v₁ • _} {v₂ • _} (r-cons v₁∼v₂ σ₁~σ₂) = ret≈ v₁∼v₂
  sim {` suc x} {_ • σ₁} {_ • σ₂} (r-cons _ σ₁~σ₂) = sim {` x} {σ₁} {σ₂} σ₁~σ₂ 
  sim {op ⦅ args ⦆}{σ₁}{σ₂} σ₁~σ₂ = op∼ (sim-args {args = args} σ₁~σ₂)

{-------------------------

 Examples

 -------------------------}


module Rename 
  (Op : Set)
  (sig : Op → List ℕ)
  where

  open OpSig Op sig hiding (rename)
  open ArgResult Var ABT

  r-arg : ∀{b} → ArgRes b → Arg b
  r-arg {zero} argr = ast argr
  r-arg {suc b} argr = bind (r-arg (argr 0))

  r-args : ∀{bs} → ArgsRes bs → Args bs
  r-args rnil = nil
  r-args (rcons argr argsr) = cons (r-arg argr) (r-args argsr)
      
  r-op : (o : Op) → ArgsRes (sig o) → ABT
  r-op o rs = o ⦅ r-args rs ⦆
  
  R : Foldable Var ABT Op sig
  R = record { ret = λ x → ` x ;
               fold-free-var = λ x → x ;
               fold-op = r-op ;
               apply-subst = ⦉_⦊ }

  module RenFold = Folder R

  rename : Rename → ABT → ABT
  rename = RenFold.fold

module Subst
  (Op : Set)
  (sig : Op → List ℕ)
  where

  open OpSig Op sig
  open ArgResult ABT ABT
  
  s-arg : ∀{b} → ArgRes b → Arg b
  s-arg {zero} M = ast M
  s-arg {suc b} f = bind (s-arg (f (` 0)))

  s-args : ∀{bs} → ArgsRes bs → Args bs
  s-args rnil = nil
  s-args (rcons R Rs) = cons (s-arg R) (s-args Rs)
      
  s-op : (o : Op) → ArgsRes (sig o) → ABT
  s-op o Rs = o ⦅ s-args Rs ⦆

  S : Foldable ABT ABT Op sig
  S = record { ret = λ M → M ;
               fold-free-var = λ x → ` x ;
               fold-op = s-op ;
               apply-subst = ⟪_⟫ }

  module SubFold = Folder S

  subst : Subst → ABT → ABT
  subst = SubFold.fold


module LambdaExample where

  data Op : Set where
    op-lam : Op
    op-app : Op

  sig : Op → List ℕ
  sig op-lam = 1 ∷ []
  sig op-app = 0 ∷ 0 ∷ []

  open OpSig Op sig hiding (rename)

  infix 6 ƛ_
  pattern ƛ_ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

  infixl 7  _·_
  pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
  
  M₀ : ABT
  M₀ = (` 0) · (` 1)

  M₁ : ABT
  M₁ = ƛ (` 0) · (` 1)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
  open Rename Op sig

  _ : rename (↑ 1) M₀ ≡ (` 1) · (` 2)
  _ = refl

  _ : rename (↑ 1) M₁ ≡ ƛ (` 0) · (` 2)
  _ = refl

  open Subst Op sig

  σ₀ : Substitution ABT
  σ₀ = ` 3 • id

  _ : subst σ₀ M₀ ≡ (` 3) · (` 0)
  _ = refl

  _ : subst σ₀ M₁ ≡ ƛ (` 0) · (` 4)
  _ = refl

  _ : ⟪ σ₀ ⟫ M₁ ≡ ƛ (` 0) · (` 4)
  _ rewrite exts-cons-shift σ₀ = refl


module ArithExample where

  data Op : Set where
    op-num : ℕ → Op
    op-mult : Op
    op-let : Op

  sig : Op → List ℕ
  sig (op-num n) = []
  sig op-mult = 0 ∷ 0 ∷ []
  sig op-let = 0 ∷ 1 ∷ []

  open OpSig Op sig hiding (rename)

  pattern $ n  = op-num n ⦅ nil ⦆

  infixl 7  _×_
  pattern _×_ L M = op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆

  pattern bind_｛_｝ L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆

  open import Data.Maybe using (Maybe; nothing; just)
  open ArgResult (Maybe ℕ) (Maybe ℕ)

  _>>=_ : Maybe ℕ → (ℕ → Maybe ℕ) → Maybe ℕ
  x >>= f
      with x
  ... | nothing = nothing
  ... | just n = f n

  eval-op : (o : Op) → ArgsRes (sig o) → Maybe ℕ
  eval-op (op-num n) res = just n
  eval-op op-mult (rcons x (rcons y rnil)) = do n ← x; m ← y; just (n * m)
  eval-op op-let (rcons x (rcons f rnil)) = do n ← x; f (just n)

  E : Foldable (Maybe ℕ) (Maybe ℕ) Op sig
  E = record { ret = λ x → x ;
               fold-free-var = λ x → nothing ;
               fold-op = eval-op ;
               apply-subst = λ σ x → x }

  module ArithFold = Folder E

  eval : ABT → Maybe ℕ
  eval = ArithFold.fold id

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

  _ : eval ($ 2 × $ 21) ≡ just 42
  _ = refl
  
  _ : eval (` 0) ≡ nothing
  _ = refl
  
  _ : eval (bind $ 21 ｛ $ 2 × ` 0 ｝) ≡ just 42
  _ = refl

  _ : eval (bind ` 0 ｛ $ 2 × $ 21 ｝) ≡ nothing
  _ = refl
