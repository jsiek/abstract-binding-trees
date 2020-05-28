module GenericSubstitution where

import AbstractBindingTree
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-assoc)
open import Fold
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
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

  gen-subst-is-env : EnvSig (Substitution V) V
  gen-subst-is-env = record { lookup = ⧼_⧽ ; extend = extend }

  drop : (k : ℕ) → Substitution V → Substitution V
  drop k (↑ k') = ↑ (k + k')
  drop zero (v • σ) = v • σ
  drop (suc k) (v • σ) = drop k σ
  
  drop-add : ∀{x : Var} (k : ℕ) (σ : Substitution V)
           → ⧼ drop k σ ⧽ x ≡ ⧼ σ ⧽ (k + x)
  drop-add {x} k (↑ k') rewrite +-comm k k' | +-assoc k' k x = refl
  drop-add {x} zero (v • σ) = refl
  drop-add {x} (suc k) (v • σ) = drop-add k σ
  
  gen-sub-head : (v : V) (σ : Substitution V)
     → ⧼ v • σ ⧽ 0 ≡ v
  gen-sub-head v σ = refl
  
  gen-sub-suc-var : (v : V) (σ : Substitution V) (x : Var)
     → ⧼ v • σ ⧽ (suc x) ≡ ⧼ σ ⧽ x
  gen-sub-suc-var M σ x = refl

  Z-shift : ∀ x → ⧼ var→val 0 • ↑ 1 ⧽ x ≡ var→val x
  Z-shift 0 = refl
  Z-shift (suc x) = refl


module GenericSubst (V : Set) (var→val : Var → V) (shift : V → V)
  (Op : Set) (sig : Op → List ℕ) 
  (val→abt : V → AbstractBindingTree.ABT Op sig)
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
      renaming (fold to gen-subst) public

record Substable (V : Set) : Set where
  open SNF
  field var→val : Var → V
  field shift : V → V
  field ⟪_⟫ : Substitution V → V → V
  open GenericSub V var→val shift
  field var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x)
  field sub-var→val : ∀ σ x → ⟪ σ ⟫ (var→val x) ≡ ⧼ σ ⧽  x
  field shift-⟪↑1⟫ : ∀ v → shift v ≡ ⟪ ↑ 1 ⟫ v
