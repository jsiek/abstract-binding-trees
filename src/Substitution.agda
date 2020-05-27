module Substitution where

import AbstractBindingTree
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Fold
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Var

infixr 6 _•_

data Substitution : (V : Set) → Set where
  ↑ : (k : ℕ) → ∀{V} → Substitution V
  _•_ : ∀{V} → V → Substitution V → Substitution V

id : ∀ {V} → Substitution V
id = ↑ 0


module GenericSub (V : Set) (var→val : Var → V) (shift : V → V) where

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
  
  gen-sub-head : (v : V) (σ : Substitution V)
     → ⧼ v • σ ⧽ 0 ≡ v
  gen-sub-head v σ = refl
  
  gen-sub-suc-var : (v : V) (σ : Substitution V) (x : Var)
     → ⧼ v • σ ⧽ (suc x) ≡ ⧼ σ ⧽ x
  gen-sub-suc-var M σ x = refl


module GenericSubst (V : Set) (var→val : Var → V) (shift : V → V)
  (Op : Set) (sig : Op → List ℕ) 
  (val→abt : V → AbstractBindingTree.ABT Op sig)
  where

  open AbstractBindingTree Op sig
  open GenericSub V var→val shift public
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
               fold-op = s-op ; env = gen-subst-is-env }

  module SubstFold = Folder gen-subst-is-foldable

  gen-subst : Substitution V → ABT → ABT
  gen-subst = SubstFold.fold


open GenericSub Var (λ x → x) suc
    using ()
    renaming (⧼_⧽ to ⦉_⦊; drop to dropr; gen-inc to inc) public

Rename : Set
Rename = Substitution Var


module Rename (Op : Set) (sig : Op → List ℕ) where
  open AbstractBindingTree Op sig using (`_)
  open GenericSubst Var (λ x → x) suc Op sig `_
      renaming (gen-subst to rename;
                gen-subst-is-foldable to rename-is-foldable;
                gen-subst-is-env to rename-is-env;
                ⧼_⧽ to ⦉_⦊; drop to dropr) public


module GenericSubProperties
  (V : Set)
  (var→val : Var → V)
  (shift : V → V)
  (var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x))
  where
  open GenericSub V var→val shift

  inc-suc : ∀ ρ x → ⧼ gen-inc ρ ⧽ x ≡ shift (⧼ ρ ⧽ x)
  inc-suc (↑ k) x = var→val-suc-shift
  inc-suc (x₁ • ρ) zero = refl
  inc-suc (x₁ • ρ) (suc x) = inc-suc ρ x

  extend-suc : ∀ σ v x → ⧼ extend σ v ⧽ (suc x) ≡ shift (⧼ σ ⧽ x)
  extend-suc σ v x = inc-suc σ x

module Subst (Op : Set) (sig : Op → List ℕ) where
  open AbstractBindingTree Op sig using (ABT; `_)
  open Rename Op sig using (rename)
  open GenericSubst ABT `_ (rename (↑ 1)) Op sig (λ M → M)
    renaming (⧼_⧽ to ⟦_⟧; gen-subst to ⟪_⟫;
              extend to exts;
              gen-subst-is-env to subst-is-env;
              gen-subst-is-foldable to subst-is-foldable) public
  open GenericSubProperties ABT `_ (rename (↑ 1)) (λ {x} → refl) public


