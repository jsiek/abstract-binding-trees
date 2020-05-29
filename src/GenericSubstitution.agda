{-# OPTIONS --rewriting #-}

module GenericSubstitution where

import AbstractBindingTree
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-assoc)
open import Fold
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Var

module SNF where

  infixr 6 _•_

  data Substitution : (V : Set) → Set where
    ↑ : (k : ℕ) → ∀{V} → Substitution V
    _•_ : ∀{V} → V → Substitution V → Substitution V

  id : ∀ {V} → Substitution V
  id = ↑ 0


module GenericSub (V : Set) (var→val : Var → V) (shift : V → V) where
  open SNF

  ⧼_⧽ : Substitution V → Var → V
  ⧼ ↑ k ⧽ x = var→val (k + x)
  ⧼ y • σ ⧽ 0 = y
  ⧼ y • σ ⧽ (suc x) = ⧼ σ ⧽ x

  gen-inc : Substitution V → Substitution V
  gen-inc (↑ k) = ↑ (suc k)
  gen-inc (v • ρ) = shift v • gen-inc ρ

  {- generalization of ext and exts. -}
  extend : Substitution V → V → Substitution V
  extend σ v = v • gen-inc σ

  extend-0 : ∀ σ v → ⧼ extend σ v ⧽ 0 ≡ v
  extend-0 σ v = refl

  {- extend-suc is in GenericSubProperties.agda -}

  gen-subst-is-env : EnvSig (Substitution V) V
  gen-subst-is-env = record { lookup = ⧼_⧽ ; extend = extend }

  drop : (k : ℕ) → Substitution V → Substitution V
  drop k (↑ k') = ↑ (k + k')
  drop zero (v • σ) = v • σ
  drop (suc k) (v • σ) = drop k σ
  
  drop-0 : ∀ σ → drop 0 σ ≡ σ
  drop-0 (↑ k) = refl
  drop-0 (v • σ) = refl
    
  {-# REWRITE drop-0 #-}
  
  drop-add : ∀{x : Var} (k : ℕ) (σ : Substitution V)
           → ⧼ drop k σ ⧽ x ≡ ⧼ σ ⧽ (k + x)
  drop-add {x} k (↑ k') rewrite +-comm k k' | +-assoc k' k x = refl
  drop-add {x} zero (v • σ) = refl
  drop-add {x} (suc k) (v • σ) = drop-add k σ

  drop-drop : ∀ k k' σ → drop (k + k') σ ≡ drop k (drop k' σ)
  drop-drop k k' (↑ k₁) rewrite +-assoc k k' k₁ = refl
  drop-drop zero k' (v • σ) = refl
  drop-drop (suc k) zero (v • σ) rewrite +-comm k 0 = refl
  drop-drop (suc k) (suc k') (v • σ)
      with drop-drop (suc k) k' σ
  ... | IH rewrite +-comm k (suc k') | +-comm k k' = IH

  drop-inc : ∀ k σ → drop k (gen-inc σ) ≡ gen-inc (drop k σ)
  drop-inc k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
  drop-inc zero (v • σ) = refl
  drop-inc (suc k) (v • σ) = drop-inc k σ

  drop-extend : ∀ k σ v → drop (suc k) (extend σ v) ≡ gen-inc (drop k σ)
  drop-extend k (↑ k₁) v rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
  drop-extend zero (x • σ) v = refl
  drop-extend (suc k) (x • σ) v = drop-inc k σ

  gen-sub-head : (v : V) (σ : Substitution V)
     → ⧼ v • σ ⧽ 0 ≡ v
  gen-sub-head v σ = refl
  
  gen-sub-suc-var : (v : V) (σ : Substitution V) (x : Var)
     → ⧼ v • σ ⧽ (suc x) ≡ ⧼ σ ⧽ x
  gen-sub-suc-var v σ x = refl

  Z-shift : ∀ x → ⧼ var→val 0 • ↑ 1 ⧽ x ≡ var→val x
  Z-shift 0 = refl
  Z-shift (suc x) = refl


module ComposeGenSubst
  (V : Set) (var→val : Var → V) (shift : V → V)
  (⦑_⦒ : SNF.Substitution V → V → V)
  where
  open SNF
  open GenericSub V var→val shift
  
  infixr 5 _⨟_
  _⨟_ : Substitution V → Substitution V → Substitution V
  ↑ k ⨟ σ = drop k σ
  (v • σ₁) ⨟ σ₂ = ⦑ σ₂ ⦒ v • (σ₁ ⨟ σ₂)

{-

 Substitution is a fold that produces an AST.

 -}

module GenericSubst (V : Set) (var→val : Var → V) (shift : V → V)
  (Op : Set) (sig : Op → List ℕ) 
  (val→abt : V → AbstractBindingTree.ABT Op sig)
{-
  (val→abt∘var→val : ∀ x → val→abt (var→val x) ≡ AbstractBindingTree.`_ x)
-}
  where

  open AbstractBindingTree Op sig
  open GenericSub V var→val shift
  open ArgResult V ABT
  open SNF
  
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
               fold-op = s-op ; env = gen-subst-is-env }

  open Folder gen-subst-is-foldable
      using ()
      renaming (fold to gen-subst; fold-arg to ⟪_⟫ₐ; fold-args to ⟪_⟫₊) public

  ⟪_⟫ : Substitution V → ABT → ABT
  ⟪ σ ⟫ = gen-subst σ

record Substable (V : Set) : Set where
  open SNF
  field var→val : Var → V
  field shift : V → V
  field ⦑_⦒ : Substitution V → V → V
  open GenericSub V var→val shift
  field var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x)
  field sub-var→val : ∀ σ x → ⦑ σ ⦒ (var→val x) ≡ ⧼ σ ⧽  x
  field shift-⦑↑1⦒ : ∀ v → shift v ≡ ⦑ ↑ 1 ⦒ v
