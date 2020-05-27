{-

  Experiments in generic functions and theorems over abstract binding trees.

  Trying to draw inspiration from "A Type and Scope Safe Universe of Syntaxes with Biding", ICFP 2018.

-}

{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
  renaming (subst to eq-subst)

open import Syntax

module Generic where

{------------------------------------------

   Generic fold over abstract binding trees

 -------------------------------------------}
 
record EnvSig (E : Set) (V : Set) : Set where
  field lookup : E → Var → V
  field extend : E → V → E

module ArgResult (V : Set) (C : Set) where

  ArgRes : ℕ → Set
  ArgRes 0 = C
  ArgRes (suc n) = V → ArgRes n

  data ArgsRes : List ℕ → Set where
    rnil : ArgsRes []
    rcons : ∀{b bs} → ArgRes b → ArgsRes bs → ArgsRes (b ∷ bs)

record Foldable V C (Op : Set) (sig : Op → List ℕ) Env : Set where
  open ArgResult V C
  field env : EnvSig Env V
  open EnvSig env public
  field ret : V → C
  field fold-free-var : Var → V
  field fold-op : (o : Op) → ArgsRes (sig o) → C

module Folder {V}{C}{Op}{sig}{Env} (F : Foldable V C Op sig Env) where

  open OpSig Op sig hiding (_⨟_)
  open Foldable F
  open ArgResult V C

  fold : Env → ABT → C
  fold-arg : ∀{b} → Env → Arg b → ArgRes b
  fold-args : ∀{bs} → Env → Args bs → ArgsRes bs

  fold σ (` x) = ret (lookup σ x)
  fold σ (o ⦅ args ⦆) = fold-op o (fold-args σ args)

  fold-arg σ (ast M) = fold σ M
  fold-arg σ (bind M) = λ v → fold-arg (extend σ v) M

  fold-args σ nil = rnil
  fold-args σ (cons arg args) = rcons (fold-arg σ arg) (fold-args σ args)


{---------------------------------------

   Simulation between two folds

   σ₁ ≊ σ₂ → (fold₁ σ₁ M) ≈ (fold₂ σ₂ M)

 ---------------------------------------}

module SimArgResult {Op : Set}{sig : Op → List ℕ}{V₁ C₁ : Set} {V₂ C₂ : Set}
  (_∼_ : V₁ → V₂ → Set) (_≈_ : C₁ → C₂ → Set) where
  
  open ArgResult V₁ C₁ renaming (ArgRes to ArgRes₁; ArgsRes to ArgsRes₁;
      rnil to rnil₁; rcons to rcons₁) public
  open ArgResult V₂ C₂ renaming (ArgRes to ArgRes₂; ArgsRes to ArgsRes₂;
      rnil to rnil₂; rcons to rcons₂) public
  
  ArgRes∼ : ∀ {b} → ArgRes₁ b → ArgRes₂ b → Set 
  ArgRes∼ {zero} c₁ c₂ = c₁ ≈ c₂
  ArgRes∼ {suc b} f₁ f₂ = ∀{v₁ v₂} → v₁ ∼ v₂ → ArgRes∼ (f₁ v₁) (f₂ v₂)
  
  data ArgsRes∼ : {bs : List ℕ} → ArgsRes₁ bs → ArgsRes₂ bs → Set where
    rnil∼ : ArgsRes∼ rnil₁ rnil₂
    rcons∼ : ∀{b bs}{r₁ rs₁}{r₂ rs₂}
        → ArgRes∼ r₁ r₂
        → ArgsRes∼ rs₁ rs₂
        → ArgsRes∼ {b ∷ bs} (rcons₁ r₁ rs₁) (rcons₂ r₂ rs₂)

record RelatedEnv {V₁ Env₁}{V₂ Env₂}
  (_∼_ : V₁ → V₂ → Set)
  (E₁ : EnvSig Env₁ V₁) (E₂ : EnvSig Env₂ V₂)
  : Set₁ where
  open EnvSig E₁ renaming (lookup to lookup₁; extend to ext₁)
  open EnvSig E₂ renaming (lookup to lookup₂; extend to ext₂)
  field _≊_ : Env₁ → Env₂ → Set
  field lookup∼ : ∀ {σ₁ σ₂} → σ₁ ≊ σ₂ → ∀{x} → lookup₁ σ₁ x ∼ lookup₂ σ₂ x
  field extend≊ : ∀ {v₁ v₂ σ₁ σ₂} → v₁ ∼ v₂ → σ₁ ≊ σ₂ → ext₁ σ₁ v₁ ≊ ext₂ σ₂ v₂
  
record Related {Op sig}{V₁ C₁ Env₁} {V₂ C₂ Env₂}
  (F₁ : Foldable V₁ C₁ Op sig Env₁)
  (F₂ : Foldable V₂ C₂ Op sig Env₂)
  : Set₁ where
  field _∼_ : V₁ → V₂ → Set
  field _≈_ : C₁ → C₂ → Set
  field env∼ : RelatedEnv _∼_ (Foldable.env F₁) (Foldable.env F₂)
  open RelatedEnv env∼ public
  open SimArgResult {Op}{sig} _∼_ _≈_
  open Foldable F₁
      renaming (fold-free-var to ffvar₁; ret to ret₁; fold-op to fop₁)
  open Foldable F₂
      renaming (fold-free-var to ffvar₂; ret to ret₂; fold-op to fop₂)
  field ret≈ : ∀{v₁ v₂} → v₁ ∼ v₂ → ret₁ v₁ ≈ ret₂ v₂
  field vars∼ : ∀{x} → ffvar₁ x ∼ ffvar₂ x
  field op∼ : ∀{op}{Rs₁}{Rs₂} → ArgsRes∼ Rs₁ Rs₂ → fop₁ op Rs₁ ≈ fop₂ op Rs₂

module Simulator {Op sig}{V₁ C₁ Env₁} {V₂ C₂ Env₂}
  (F₁ : Foldable V₁ C₁ Op sig Env₁)
  (F₂ : Foldable V₂ C₂ Op sig Env₂)
  (R : Related F₁ F₂)
  where

  open Folder F₁
     renaming (fold to fold₁; fold-arg to fold-arg₁; fold-args to fold-args₁)
  open Folder F₂
     renaming (fold to fold₂; fold-arg to fold-arg₂; fold-args to fold-args₂)

  open Related R
  open SimArgResult {Op}{sig} _∼_ _≈_

  open OpSig Op sig

  sim : ∀{M}{σ₁ σ₂}
     → σ₁ ≊ σ₂
     → (fold₁ σ₁ M) ≈ (fold₂ σ₂ M)
  sim-arg : ∀{σ₁}{σ₂}{b}{arg : Arg b}
     → σ₁ ≊ σ₂
     → ArgRes∼ (fold-arg₁ σ₁ arg) (fold-arg₂ σ₂ arg)
  sim-args : ∀{σ₁}{σ₂}{bs}{args : Args bs}
     → σ₁ ≊ σ₂
     → ArgsRes∼ (fold-args₁ σ₁ args) (fold-args₂ σ₂ args)
  sim {` x} {σ₁} {σ₂} σ₁~σ₂ = ret≈ (lookup∼ σ₁~σ₂)
  sim {op ⦅ args ⦆}{σ₁}{σ₂} σ₁~σ₂ = op∼ (sim-args {args = args} σ₁~σ₂)
  sim-arg {σ₁} {σ₂} {zero} {ast M} σ₁≊σ₂ = sim {M} σ₁≊σ₂ 
  sim-arg {σ₁} {σ₂} {suc b} {bind arg} σ₁≊σ₂ {v₁}{v₂} v₁∼v₂ =
     sim-arg {b = b}{arg = arg} (extend≊ v₁∼v₂ σ₁≊σ₂)
  sim-args {σ₁} {σ₂} {[]} {nil} σ₁≊σ₂ = rnil∼
  sim-args {σ₁} {σ₂} {b ∷ bs} {cons A As} σ₁≊σ₂ =
    let sa = sim-arg {arg = A} σ₁≊σ₂ in
    rcons∼ sa (sim-args {σ₁} {σ₂} {bs} {As} σ₁≊σ₂)


{---------------------------

 Preservation of a predicate

      A : I
      Γ : List I

      Γ ⊢ M ⦂ A 
    → σ ⦂ Γ ⇒ Δ 
    → Δ ⊢ (fold σ M) ⦂ A

 ---------------------------}

_∋_⦂_ : ∀{I : Set} → List I → Var → I → Set
_∋_⦂_ {I} [] x A = ⊥
_∋_⦂_ {I} (B ∷ Γ) zero A = A ≡ B
_∋_⦂_ {I} (B ∷ Γ) (suc x) A = Γ ∋ x ⦂ A

module ABTPred (Op : Set) (sig : Op → List ℕ) {I : Set}
  (𝒫 : Op → List I → I → Set)
  where
  
  open OpSig Op sig

  data _⊢_⦂_ : List I → OpSig.ABT Op sig → I → Set
  data _∣_⊢a_⦂_ : (b : ℕ) → List I → Arg b → I → Set 
  data _∣_⊢as_⦂_ : (bs : List ℕ) → List I → Args bs → List I → Set   
  
  data _⊢_⦂_ where
    var-p : ∀{Γ x A}
       → Γ ∋ x ⦂ A
       → Γ ⊢ ` x ⦂ A
    op-op : ∀{Γ op args}{B As}
       → (sig op) ∣ Γ ⊢as args ⦂ As
       → 𝒫 op As B
       → Γ ⊢ op ⦅ args ⦆ ⦂ B

  data _∣_⊢a_⦂_ where
    ast-a : ∀{Γ}{M}{A}
       → Γ ⊢ M ⦂ A
       → 0 ∣ Γ ⊢a ast M ⦂ A
       
    bind-a : ∀{b}{B Γ arg A}
       → b ∣ (B ∷ Γ) ⊢a arg ⦂ A
       → (suc b) ∣ Γ ⊢a bind arg ⦂ A

  data _∣_⊢as_⦂_ where
    nil-a : ∀{Γ} → [] ∣ Γ ⊢as nil ⦂ []
    
    cons-a : ∀{b bs}{arg args}{Γ}{A}{As}
       → b ∣ Γ ⊢a arg ⦂ A
       → bs ∣ Γ ⊢as args ⦂ As
       → (b ∷ bs) ∣ Γ ⊢as (cons arg args) ⦂ (A ∷ As)


module PresArgResult (Op : Set) (sig : Op → List ℕ) {V C : Set}{I : Set}
  (𝒫 : Op → List I → I → Set)
  (_⊢v_⦂_ : List I → V → I → Set)
  (_⊢c_⦂_ : List I → C → I → Set)
  where

  open ABTPred Op sig 𝒫
  open ArgResult V C
  
  data _∣_⊢r_⦂_ : (b : ℕ) → List I → ArgRes b → I → Set where
    ast-r : ∀{Δ}{c}{A}
       → Δ ⊢c c ⦂ A
       → 0 ∣ Δ ⊢r c ⦂ A
       
    bind-r : ∀{b}{A B Δ}{f}
          → (∀ {v} → (B ∷ Δ) ⊢v v ⦂ B → b ∣ (B ∷ Δ) ⊢r (f v) ⦂ A)
          → (suc b) ∣ Δ ⊢r f ⦂ A
  
  data _∣_⊢rs_⦂_ : (bs : List ℕ) → List I → ArgsRes bs → List I → Set where
    nil-r : ∀{Δ} → [] ∣ Δ ⊢rs rnil ⦂ []
    cons-r : ∀{b bs}{r rs}{Δ}{A}{As}
        → b ∣ Δ ⊢r r ⦂ A
        → bs ∣ Δ ⊢rs rs ⦂ As
        → (b ∷ bs) ∣ Δ ⊢rs rcons r rs ⦂ (A ∷ As)


record Preservable {Op}{sig}{V C Env} (I : Set) (F : Foldable V C Op sig Env) : Set₁ where
  open OpSig Op sig using (ABT; `_; _⦅_⦆)
  field 𝒫 : Op → List I → I → Set
  field _⦂_⇒_ : Env → List I → List I → Set
  field _⊢v_⦂_ : List I → V → I → Set
  field _⊢c_⦂_ : List I → C → I → Set
  open PresArgResult Op sig 𝒫 _⊢v_⦂_ _⊢c_⦂_
  open Foldable F
  open ArgResult V C
  field lookup-pres : ∀{σ}{Γ Δ}{x}{A} → σ ⦂ Γ ⇒ Δ → Γ ∋ x ⦂ A → Δ ⊢v (EnvSig.lookup env σ x) ⦂ A
  field extend-pres : ∀ {v}{σ}{Γ Δ A} → (A ∷ Δ) ⊢v v ⦂ A → σ ⦂ Γ ⇒ Δ → (EnvSig.extend env σ v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  field ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c (ret v) ⦂ A
  field var-pres : ∀{x}{Δ}{A} → Δ ∋ x ⦂ A → Δ ⊢v fold-free-var x ⦂ A
  field op-pres : ∀ {op}{Rs}{Δ}{A}{As} → sig op ∣ Δ ⊢rs Rs ⦂ As → 𝒫 op As A → Δ ⊢c (fold-op op Rs) ⦂ A


module Preservation {Op sig}{V C Env}{I}
  (F : Foldable V C Op sig Env)
  (P : Preservable I F)
  where
  open Folder F using (fold; fold-arg; fold-args)
  open Foldable F using (env; fold-op)
  open Preservable P

  open ABTPred Op sig 𝒫
  open PresArgResult Op sig 𝒫 _⊢v_⦂_ _⊢c_⦂_ public
  open OpSig Op sig

  preserve : ∀{M}{σ}{Γ Δ}{A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c fold σ M ⦂ A
  pres-arg : ∀{b}{Γ Δ}{arg : Arg b}{A}{σ}
     → b ∣ Γ ⊢a arg ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → b ∣ Δ ⊢r fold-arg σ arg ⦂ A
  pres-args : ∀{bs}{Γ Δ}{args : Args bs}{As}{σ}
     → bs ∣ Γ ⊢as args ⦂ As
     → σ ⦂ Γ ⇒ Δ
     → bs ∣ Δ ⊢rs fold-args σ args ⦂ As
  preserve {OpSig.` x} {σ} {Γ} {Δ} {A} (var-p ∋x) σΓΔ =
      ret-pres (lookup-pres σΓΔ ∋x)
  preserve {op OpSig.⦅ args ⦆} {σ} {Γ} {Δ} {A} (op-op ⊢args 𝒫op) σΓΔ =
      op-pres (pres-args ⊢args σΓΔ) 𝒫op
  pres-arg {zero} {Γ} {Δ} {ast M} {A} {σ} (ast-a ⊢M) σΓΔ = ast-r (preserve ⊢M σΓΔ)
  pres-arg {suc b} {Γ} {Δ} {bind arg} {A} {σ} (bind-a {b}{B} ⊢arg) σΓΔ =
      bind-r G
      where
      G : ∀ {v}
         → (B ∷ Δ) ⊢v v ⦂ B
         → b ∣ B ∷ Δ ⊢r fold-arg σ (bind arg) v ⦂ A
      G {v} ⊢v⦂B = pres-arg {b} {arg = arg} ⊢arg (extend-pres ⊢v⦂B σΓΔ)
  pres-args {[]} {Γ} {Δ} {nil} {[]} ⊢args σΓΔ = nil-r
  pres-args {b ∷ bs} {Γ} {Δ} {cons arg args} {A ∷ As} (cons-a ⊢arg ⊢args) σΓΔ =
      cons-r (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)

{---------------------------------------
 Function representation of environments
 ---------------------------------------}

module FunEnv (V : Set) where

  extend : (Var → V) → V → (Var → V)
  extend ρ v zero = v
  extend ρ v (suc x) = ρ x {- assumes values aren't affected by substitution! -}

  fun-is-env : EnvSig (Var → V) V
  fun-is-env = record { lookup = λ ρ x → ρ x ; extend = extend }

{--------------------------------------------

 Example: Renaming, Substitution, and a Lemma

 --------------------------------------------}

module GenericSub (V : Set) (var→val : Var → V) (shift : V → V) where

  ⧼_⧽ : Substitution V → Var → V
  ⧼ ↑ k ⧽ x = var→val (k + x)
  ⧼ y • σ ⧽ 0 = y
  ⧼ y • σ ⧽ (suc x) = ⧼ σ ⧽ x

  inc : Substitution V → Substitution V
  inc (↑ k) = ↑ (suc k)
  inc (v • ρ) = shift v • inc ρ

  {- generalization of ext and exts. -}
  extend : Substitution V → V → Substitution V
  extend σ v = v • inc σ

  sub-is-env : EnvSig (Substitution V) V
  sub-is-env = record { lookup = ⧼_⧽ ; extend = extend }

  drop : (k : ℕ) → Substitution V → Substitution V
  drop k (↑ k') = ↑ (k + k')
  drop zero (v • σ) = v • σ
  drop (suc k) (v • σ) = drop k σ
  
  sub-head : (v : V) (σ : Substitution V)
     → ⧼ v • σ ⧽ 0 ≡ v
  sub-head v σ = refl
  
  sub-suc-var : (v : V) (σ : Substitution V) (x : Var)
     → ⧼ v • σ ⧽ (suc x) ≡ ⧼ σ ⧽ x
  sub-suc-var M σ x = refl

module GenericSubst (V : Set) (var→val : Var → V) (shift : V → V)
  (Op : Set) (sig : Op → List ℕ) 
  (val→abt : V → OpSig.ABT Op sig)
  where

  open OpSig Op sig hiding (shift)
  open GenericSub V var→val shift
  open ArgResult V ABT
  
  s-op : (o : Op) → ArgsRes (sig o) → ABT
  s-arg : ∀{b} → ArgRes b → Arg b
  s-args : ∀{bs} → ArgsRes bs → Args bs
  s-op o Rs = o ⦅ s-args Rs ⦆
  s-arg {zero} M = ast M
  s-arg {suc b} f = bind (s-arg (f (var→val 0)))
  s-args rnil = nil
  s-args (rcons r rs) = cons (s-arg r) (s-args rs)

  gen-subst-is-foldable : Foldable V ABT Op sig (Substitution V)
  gen-subst-is-foldable = record { ret = val→abt ; fold-free-var = var→val ; 
               fold-op = s-op ; env = sub-is-env }

  module SubstFold = Folder gen-subst-is-foldable

  gen-subst : Substitution V → ABT → ABT
  gen-subst = SubstFold.fold


module Rename (Op : Set) (sig : Op → List ℕ) where
  open OpSig Op sig using (`_)
  open GenericSubst Var (λ x → x) suc Op sig `_
      renaming (gen-subst to rename;
                gen-subst-is-foldable to rename-is-foldable) public


module Subst (Op : Set) (sig : Op → List ℕ) where
  open OpSig Op sig using (ABT; `_)
  open Rename Op sig using (rename)
  open GenericSubst ABT `_ (rename (↑ 1)) Op sig (λ M → M)
    renaming (gen-subst to subst;
              gen-subst-is-foldable to subst-is-foldable) public 

module GenericSub2 (V : Set)
  (var→val : Var → V)
  (shift : V → V)
  (⟪_⟫ : Substitution V → V → V)
  (var→val-suc-shift : ∀{x} → var→val (suc x) ≡ ⟪ ↑ 1 ⟫ (var→val x))
  (sub-var→val : ∀ σ x → ⟪ σ ⟫ (var→val x) ≡ GenericSub.⧼_⧽ V var→val shift  σ x)
  where

  open GenericSub V var→val shift
  open import Data.Nat.Properties using (+-comm; +-assoc)

  infixr 5 _⨟_

  _⨟_ : Substitution V → Substitution V → Substitution V
  ↑ k ⨟ σ = drop k σ
  (v • σ₁) ⨟ σ₂ = ⟪ σ₂ ⟫ v • (σ₁ ⨟ σ₂)

  sub-tail : (v : V) (σ : Substitution V)
     → (↑ 1 ⨟ v • σ) ≡ σ
  sub-tail v (↑ k) = refl
  sub-tail v (w • σ) = refl

  inc-suc : ∀ ρ x → ⧼ inc ρ ⧽ x ≡ shift (⧼ ρ ⧽ x)
  inc-suc (↑ k) x = ? {- var→val-suc-shift -}
  inc-suc (x₁ • ρ) zero = refl
  inc-suc (x₁ • ρ) (suc x) = inc-suc ρ x

  inc=⨟↑ : ∀ σ → inc σ ≡ σ ⨟ ↑ 1
  inc=⨟↑ (↑ k) rewrite +-comm k 1 = refl
  inc=⨟↑ (M • σ) = cong₂ _•_ ? (inc=⨟↑ σ)

  exts-cons-shift : ∀ σ v → extend σ v ≡ (v • (σ ⨟ ↑ 1))
  exts-cons-shift (↑ k) v rewrite +-comm k 1 = refl
  exts-cons-shift (w • σ) v rewrite inc=⨟↑ σ = ?

  drop-add : ∀{x : Var} (k : ℕ) (σ : Substitution V)
           → ⧼ drop k σ ⧽ x ≡ ⧼ σ ⧽ (k + x)
  drop-add {x} k (↑ k') rewrite +-comm k k' | +-assoc k' k x = refl
  drop-add {x} zero (v • σ) = refl
  drop-add {x} (suc k) (v • σ) = drop-add k σ

  sub-η : ∀ (σ : Substitution V) (x : Var)
        → ⧼ (⟪ σ ⟫ (var→val 0) • (↑ 1 ⨟ σ)) ⧽ x ≡ ⧼ σ ⧽ x
  sub-η σ 0 rewrite sub-var→val σ 0 = refl
  sub-η σ (suc x) = drop-add 1 σ

  Z-shift : ∀ x → ⧼ var→val 0 • ↑ 1 ⧽ x ≡ var→val x
  Z-shift 0 = refl
  Z-shift (suc x) = refl

  sub-idL : (σ : Substitution V)
         → id ⨟ σ ≡ σ
  sub-idL (↑ k) = refl
  sub-idL (M • σ) = refl

  sub-dist :  ∀ {σ : Substitution V} {τ : Substitution V} {M : V}
           → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
  sub-dist = refl

  seq-subst : ∀ σ τ x → ⧼ σ ⨟ τ ⧽ x ≡ ⟪ τ ⟫ (⧼ σ ⧽ x)
  seq-subst (↑ k) τ x rewrite drop-add {x} k τ | sub-var→val τ (k + x) = refl
  seq-subst (M • σ) τ zero = refl
  seq-subst (M • σ) τ (suc x) = seq-subst σ τ x

  exts-ids : ∀{σ : Substitution V}
     → (∀ x → ⧼ σ ⧽ x ≡ var→val x)
     → (∀ x → ⧼ extend σ (var→val 0) ⧽ x ≡ var→val x)
  exts-ids {σ} is-id zero
      rewrite exts-cons-shift σ (var→val 0) = refl
  exts-ids {σ} is-id (suc x)
      rewrite exts-cons-shift σ (var→val 0) | seq-subst σ (↑ 1) x | inc-suc σ x
      | is-id x | var→val-suc-shift {x} = ?

module IdFold
  (Op : Set) (sig : Op → List ℕ)
  where
  open OpSig Op sig hiding (shift; rename)
  open Rename Op sig
  open Subst Op sig
  shift = rename (↑ 1)
  open GenericSub ABT `_ shift
  open ArgResult ABT ABT

  open GenericSub2 ABT `_ shift subst (λ {x} → refl) (λ σ x → refl)
  
  res→arg : ∀{b} → ArgRes b → Arg b
  res→arg {zero} M = ast M
  res→arg {suc b} r = bind (res→arg (r (` 0)))

  res→args : ∀{bs} → ArgsRes bs → Args bs
  res→args {[]} rnil = nil
  res→args {b ∷ bs} (rcons r rs) = cons (res→arg r) (res→args rs)
      
  id-is-foldable : Foldable ABT ABT Op sig (Substitution ABT)
  id-is-foldable = record { env = sub-is-env ; ret = λ M → M ;
            fold-free-var = `_ ; fold-op = λ o rs → o ⦅ res→args rs ⦆ }

  module IdFold = Folder id-is-foldable
  open IdFold renaming (fold to ids; fold-arg to id-arg; fold-args to id-args)

  id-id : ∀ M σ
     → (∀ x → ⧼ σ ⧽ x ≡ ` x)
     → ids σ M ≡ M
  id-id-arg : ∀ {b} (arg : Arg b) σ
     → (∀ x → ⧼ σ ⧽ x ≡ ` x)
     → res→arg {b} (id-arg σ arg) ≡ arg
  id-id-args : ∀ {bs} (args : Args bs) σ
     → (∀ x → ⧼ σ ⧽ x ≡ ` x)
     → res→args {bs} (id-args σ args) ≡ args
  
  id-id (` x) σ σ-id = σ-id x
  id-id (op ⦅ args ⦆) σ σ-id =
      cong (_⦅_⦆ op) (id-id-args args σ σ-id)
  id-id-arg {zero} (ast M) σ σ-id = cong ast (id-id M σ σ-id)
  id-id-arg {suc b} (bind arg) σ σ-id =
      cong bind (id-id-arg arg (extend σ (` 0)) E)
      where
      E : ∀ x → ⧼ extend σ (` 0) ⧽ x ≡ (` x)
      E zero = refl
      E (suc x) =
          let isx : ⧼ inc σ ⧽ x ≡ shift (⧼ σ ⧽ x)
              isx = inc-suc σ x in
          let ss = σ-id x in
          {!!}
      {- 
Goal: ⧼ extend σ (` 0) ⧽ (suc x) ≡ (` suc x)
      ⧼ (inc σ) ⧽ x
      


      -}
      
  id-id-args {[]} nil σ σ-id = refl
  id-id-args {b ∷ bs} (cons arg args) σ σ-id =
      cong₂ cons (id-id-arg arg σ σ-id) (id-id-args args σ σ-id)



module GenericSubstPres (V : Set) (var→val : Var → V) (shift : V → V)
  (Op : Set) (sig : Op → List ℕ) {I : Set}
  (𝒫 : Op → List I → I → Set)
  (_⊢v_⦂_ : List I → V → I → Set)
  (⊢var→val : ∀{Δ}{x}{A} → Δ ∋ x ⦂ A → Δ ⊢v var→val x ⦂ A)
  (val→abt : V → OpSig.ABT Op sig)
  (⊢val→abt : ∀{Δ v A} → Δ ⊢v v ⦂ A → ABTPred._⊢_⦂_ Op sig 𝒫 Δ (Foldable.ret (GenericSubst.gen-subst-is-foldable V var→val shift Op sig val→abt) v) A)
  (⊢shift : ∀{Δ A B σ x} → Δ ⊢v GenericSub.⧼_⧽ V var→val shift σ x ⦂ B → (A ∷ Δ) ⊢v shift (GenericSub.⧼_⧽ V var→val shift σ x) ⦂ B)
  (var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x))
  where

  open OpSig Op sig hiding (shift)
  open GenericSub V var→val shift hiding (extend)
  open GenericSubst V var→val shift Op sig val→abt
  open ArgResult V ABT
  open ABTPred Op sig 𝒫
  open PresArgResult Op sig {V}{ABT} 𝒫 _⊢v_⦂_ _⊢_⦂_

  res→arg : ∀{Δ : List I}{b}{R : ArgRes b}{A : I}
     → b ∣ Δ ⊢r R ⦂ A
     → b ∣ Δ ⊢a s-arg R ⦂ A
  res→arg {Δ} {zero} {R} {A} (ast-r ⊢R) = ast-a ⊢R
  res→arg {Δ} {suc b} {R} {A} (bind-r f) =
      bind-a (res→arg (f (⊢var→val refl)))
  
  res→args : ∀{Δ}{bs}{Rs : ArgsRes bs}{As : List I}
     → bs ∣ Δ ⊢rs Rs ⦂ As
     → bs ∣ Δ ⊢as s-args Rs ⦂ As
  res→args {Δ} {[]} {.rnil} {.[]} nil-r = nil-a
  res→args {Δ} {b ∷ bs} {.(rcons _ _)} {.(_ ∷ _)} (cons-r ⊢R ⊢Rs) =
      cons-a (res→arg ⊢R) (res→args ⊢Rs)

  open Foldable gen-subst-is-foldable
  
  op-pres : ∀ {op : Op}{Rs : ArgsRes (sig op)}{Δ : List I}{A : I}{As : List I}
     → sig op ∣ Δ ⊢rs Rs ⦂ As
     → 𝒫 op As A
     → Δ ⊢ (fold-op op Rs) ⦂ A
  op-pres {op}{Rs}{Δ}{A}{As} ⊢Rs 𝒫op =
      let ⊢sargs = (eq-subst (λ □ → sig op ∣ □ ⊢as s-args Rs ⦂ As) refl
                            (res→args ⊢Rs)) in
      op-op ⊢sargs 𝒫op

  inc-suc : ∀ ρ x → ⧼ inc ρ ⧽ x ≡ shift (⧼ ρ ⧽ x)
  inc-suc (↑ k) x = var→val-suc-shift
  inc-suc (x₁ • ρ) zero = refl
  inc-suc (x₁ • ρ) (suc x) = inc-suc ρ x
  
  _⦂_⇒_ : Substitution V → List I → List I → Set
  _⦂_⇒_ ρ Γ Δ = ∀ {x}{A} → Γ ∋ x ⦂ A → Δ ⊢v ⧼ ρ ⧽ x ⦂ A
  
  extend-pres : ∀ {v : V}{σ}{Γ}{Δ}{A}
     → (A ∷ Δ) ⊢v v ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → (extend σ v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  extend-pres {v} {σ} {Γ} {Δ} {A} ∋v σΓΔ {zero} {B} refl = ∋v
  extend-pres {v} {σ} {Γ} {Δ} {A} ∋v σΓΔ {suc x} {B} ∋x
      rewrite inc-suc σ x =
      ⊢shift {σ = σ} (σΓΔ ∋x)

  gen-subst-is-preservable : Preservable I gen-subst-is-foldable
  gen-subst-is-preservable = record { 𝒫 = 𝒫 ; _⦂_⇒_ = _⦂_⇒_ ; _⊢v_⦂_ = _⊢v_⦂_
   ; _⊢c_⦂_ = _⊢_⦂_
   ; lookup-pres = λ σΓΔ Γ∋x → σΓΔ Γ∋x ; extend-pres = extend-pres
   ; ret-pres = ⊢val→abt ; var-pres = λ Γ∋x → ⊢var→val Γ∋x ; op-pres = op-pres }
  open Preservation gen-subst-is-foldable gen-subst-is-preservable public


module RenamePres (Op : Set) (sig : Op → List ℕ) {I : Set}
  (𝒫 : Op → List I → I → Set) where
  open OpSig Op sig using (`_)
  open GenericSubstPres Var (λ x → x) suc Op sig 𝒫 _∋_⦂_ (λ {Δ} {x} {A} z → z)
       `_ ABTPred.var-p (λ {Δ} {A} {B} {σ} {x} z → z) (λ {x} → refl) public


module SubstPres (Op : Set) (sig : Op → List ℕ) {I : Set}
  (𝒫 : Op → List I → I → Set) where
  open OpSig Op sig using (ABT; `_)
  open Rename Op sig using (rename)
  open ABTPred Op sig 𝒫
  open RenamePres Op sig 𝒫 renaming (preserve to rename-preserve)
  open GenericSubstPres ABT `_ (rename (↑ 1)) Op sig 𝒫 _⊢_⦂_ var-p (λ M → M)
          (λ {Δ} {v} {A} z → z)
          (λ ⊢M → (rename-preserve {σ = ↑ 1} ⊢M λ {x} {A} z → z))
          (λ {x} → refl) public

module TestRenameSubstOnLambda where

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


module RelGenericSubst (V₁ V₂ : Set) (_∼_ : V₁ → V₂ → Set) where
  data _≊_ : Substitution V₁ → Substitution V₂ → Set where
     r-up : ∀{k} → (↑ k) ≊ (↑ k)
     r-cons : ∀{v₁ σ₁ v₂ σ₂}
        → v₁ ∼ v₂  →   σ₁ ≊ σ₂
        → (v₁ • σ₁) ≊ (v₂ • σ₂)


module RelateSub (V₁ V₂ : Set)
  (_∼_ : V₁ → V₂ → Set)
  (var→val₁ : Var → V₁)
  (shift₁ : V₁ → V₁)
  (var→val₂ : Var → V₂)
  (shift₂ : V₂ → V₂)
  (var→val∼ : ∀{x} → var→val₁ x ∼ var→val₂ x)
  (shift∼ : ∀ {v₁ v₂} → v₁ ∼ v₂ → shift₁ v₁ ∼ shift₂ v₂)
  where

  open GenericSub V₁ var→val₁ shift₁
     renaming (⧼_⧽ to ⧼_⧽₁; sub-is-env to sub-is-env₁; inc to inc₁)
  open GenericSub V₂ var→val₂ shift₂
     renaming (⧼_⧽ to ⧼_⧽₂; sub-is-env to sub-is-env₂; inc to inc₂)
  open RelGenericSubst V₁ V₂ _∼_

  lookup∼ : {σ₁ : Substitution V₁} {σ₂ : Substitution V₂} →
      σ₁ ≊ σ₂ → {x : ℕ} → ⧼ σ₁ ⧽₁ x ∼ ⧼ σ₂ ⧽₂ x
  lookup∼ (r-up{k}) {x} = var→val∼
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {zero} = v₁∼v₂
  lookup∼ (r-cons v₁∼v₂ σ₁≊σ₂) {suc x} = lookup∼ σ₁≊σ₂

  ≊-inc : ∀{σ₁}{σ₂}
    → σ₁ ≊ σ₂
    → (inc₁ σ₁) ≊ (inc₂ σ₂)
  ≊-inc {.(↑ _)} {.(↑ _)} r-up = r-up
  ≊-inc {.(_ • _)} {.(_ • _)} (r-cons v₁∼v₂ σ₁≊σ₂) = r-cons (shift∼ v₁∼v₂) (≊-inc σ₁≊σ₂)

  sub-is-rel-env : RelatedEnv _∼_ sub-is-env₁ sub-is-env₂
  sub-is-rel-env = record { _≊_ = _≊_ ; lookup∼ = lookup∼ ;
                    extend≊ = λ v₁∼v₂ σ₁≊σ₂ → r-cons v₁∼v₂ (≊-inc σ₁≊σ₂) }

module SubstSubst
  (Op : Set) (sig : Op → List ℕ) 
  (V₁ V₂ : Set)
  (_∼_ : V₁ → V₂ → Set)
  (var→val₁ : Var → V₁)
  (shift₁ : V₁ → V₁)
  (val→abt₁ : V₁ → OpSig.ABT Op sig)
  (var→val₂ : Var → V₂)
  (shift₂ : V₂ → V₂)
  (val→abt₂ : V₂ → OpSig.ABT Op sig)
  (var→val∼ : ∀{x} → var→val₁ x ∼ var→val₂ x)
  (shift∼ : ∀ {v₁ v₂} → v₁ ∼ v₂ → shift₁ v₁ ∼ shift₂ v₂)
  (val→abt∼ : ∀{v₁ v₂} → v₁ ∼ v₂ → val→abt₁ v₁ ≡ val→abt₂ v₂)
  where

  _≈_ = _≡_

  open OpSig Op sig
  open RelGenericSubst V₁ V₂ _∼_
  open RelateSub V₁ V₂ _∼_ var→val₁ shift₁ var→val₂ shift₂ var→val∼ shift∼
  open SimArgResult {Op}{sig}{V₁}{ABT}{V₂}{ABT} _∼_ _≈_
  open GenericSubst V₁ var→val₁ shift₁ Op sig val→abt₁
      renaming (gen-subst to gen-subst₁;
          gen-subst-is-foldable to gsubst-foldable₁;
          s-arg to s-arg₁; s-args to s-args₁)
  open GenericSubst V₂ var→val₂ shift₂ Op sig val→abt₂
      renaming (gen-subst to gen-subst₂;
          gen-subst-is-foldable to gsubst-foldable₂;
          s-arg to s-arg₂; s-args to s-args₂)
  open Foldable gsubst-foldable₁ renaming (fold-op to fop₁)
  open Foldable gsubst-foldable₂ renaming (fold-op to fop₂)

  op∼ : ∀{op : Op}{Rs₁ : ArgsRes₁ (sig op)}{Rs₂ : ArgsRes₂ (sig op)}
         → ArgsRes∼ Rs₁ Rs₂
         → fop₁ op Rs₁ ≈ fop₂ op Rs₂
  op∼ {op}{Rs₁}{Rs₂} rs∼ = G
    where
    I : ∀{b}{R₁ : ArgRes₁ b}{R₂ : ArgRes₂ b} → ArgRes∼ R₁ R₂
       → s-arg₁ R₁ ≡ s-arg₂ R₂
    I {zero} {R₁} {.R₁} refl = refl
    I {suc b} {R₁} {R₂} r~ = cong bind (I (r~ var→val∼))
    
    H : ∀{bs}{Rs₁ : ArgsRes₁ bs}{Rs₂ : ArgsRes₂ bs} → ArgsRes∼ Rs₁ Rs₂
       → s-args₁ Rs₁ ≡ s-args₂ Rs₂
    H {[]} {rnil₁} {rnil₂} rnil∼ = refl
    H {b ∷ bs} {rcons₁ r₁ Rs₁} {rcons₂ r₂ Rs₂} (rcons∼ r∼ rs∼) =
        cong₂ cons (I r∼) (H rs∼)

    G : op ⦅ s-args₁ Rs₁ ⦆ ≡ op ⦅ s-args₂ Rs₂ ⦆
    G = cong (_⦅_⦆ op) (H rs∼)

  SubSubRel : Related gsubst-foldable₁ gsubst-foldable₂
  SubSubRel = record { _∼_ = _∼_ ; _≈_ = _≈_ ; env∼ = sub-is-rel-env ;
         ret≈ = λ {v₁} {v₂} v₁∼v₂ → val→abt∼ v₁∼v₂ ; vars∼ = λ {x} → var→val∼ ;
         op∼ = op∼ }

  module Sim = Simulator gsubst-foldable₁ gsubst-foldable₂ SubSubRel

  subsub-sim : ∀{σ₁}{σ₂} (M : ABT) → σ₁ ≊ σ₂ → gen-subst₁ σ₁ M ≡ gen-subst₂ σ₂ M
  subsub-sim M = Sim.sim {M = M}


module RenSub (Op : Set) (sig : Op → List ℕ) where

  open OpSig Op sig using (ABT; `_; _⦅_⦆; cons; bind; rename→subst; ⟪_⟫)
  open Rename Op sig
  open Subst Op sig
  _∼_ = λ x M → ` x ≡ M
  open SubstSubst Op sig Var ABT _∼_ (λ x → x) suc `_ `_ (rename (↑ 1))
        (λ M → M) (λ {x} → refl) (λ { refl → refl } ) (λ { refl → refl })
  open RelGenericSubst Var ABT _∼_
  
  rename→subst-≊ : ∀{ρ} → ρ ≊ rename→subst ρ
  rename→subst-≊ {↑ k} = r-up
  rename→subst-≊ {x • ρ} = r-cons refl rename→subst-≊

  rensub : ∀ ρ M → rename ρ M ≡ subst (rename→subst ρ) M
  rensub ρ M = subsub-sim M rename→subst-≊
