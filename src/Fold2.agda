{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Product
    using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.List using (List; []; _∷_) renaming (map to lmap)
open import Data.Unit.Polymorphic using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning

{-
open import GSubst
open import GenericSubstitution
-}
open import ScopedTuple
    using (Tuple; map; _✖_; zip; zip-refl; map-pres-zip; map-compose-zip;
           map-compose; zip-map→rel; Lift-Eq-Tuple; Lift-Rel-Tuple; zip→rel)
open import Sig
open import Structures
open import Var


module Fold2 (Op : Set) (sig : Op → List Sig) where

open import AbstractBindingTree Op sig
open import Substitution
open Substitution.ABTOps Op sig
open Structures.WithOpSig Op sig

private
  variable
    ℓ : Level
    V V₁ V₂ : Set ℓ

{-------------------------------------------------------------------------------
 Folding over an abstract binding tree

 fold f v₀ σ M

 Applies f to every operator node in M and the results of
 recursively folding its subexpressions.

 Applies σ to every variable node in M.

 When going under a "clear", σ is replaced with the default environment
 that maps every variable to v₀. 

 ------------------------------------------------------------------------------}

ArgTy : {ℓ : Level} → Set ℓ → Sig → Set ℓ
ArgTy V ■ = V
ArgTy V (ν b) = V → ArgTy V b
ArgTy V (∁ b) = ArgTy V b

fold : ((op : Op) → Tuple (sig op) (ArgTy V) → V)
   → V → GSubst V → ABT → V
fold-arg : ((op : Op) → Tuple (sig op) (ArgTy V) → V)
   → V → GSubst V → {b : Sig} → Arg b → ArgTy V b
fold-args : ((op : Op) → Tuple (sig op) (ArgTy V) → V)
   → V → GSubst V → {bs : List Sig} → Args bs → Tuple bs (ArgTy V)

fold f v₀ σ (` x) = σ x
fold f v₀ σ (op ⦅ args ⦆) = f op (fold-args f v₀ σ {sig op} args)
fold-arg f v₀ σ (ast M) = (fold f v₀ σ M)
fold-arg f v₀ σ (bind arg) v = fold-arg f v₀ (v • σ) arg
fold-arg f v₀ σ (clear arg) = fold-arg f v₀ (λ x → v₀) arg
fold-args f v₀ σ {[]} nil = tt
fold-args f v₀ σ {b ∷ bs} (cons arg args) =
  ⟨ fold-arg f v₀ σ arg , fold-args f v₀ σ args ⟩

{-------------------------------------------------------------------------------
 Fold-Rename Fusion

 fold f v₀ δ (rename ρ M) ≡ fold f v₀ (λ x → fold f v₀ δ (` ρ x)) M
 ------------------------------------------------------------------------------}

fold-rename-fusion : ∀ {f : ((op : Op) → Tuple (sig op) (ArgTy V) → V)}{v₀ : V}
     {δ : GSubst V}{ρ : Rename}
     (M : ABT)
   → fold f v₀ δ (rename ρ M) ≡ fold f v₀ (λ x → fold f v₀ δ (` ρ x)) M
fold-rename-fusion {f = f}{v₀} {δ} {ρ} (` x) = refl
fold-rename-fusion {ℓ}{V = V}{f = f}{v₀} {δ} {ρ} (op ⦅ args ⦆) =
  cong (λ X → f op X) (fuse-args {δ = δ}{ρ} args)
  where
  EQ : {δ : GSubst V}{ρ : Rename}(v : V) (x : Var)  
     → (v • δ) (ext ρ x) ≡ (v • (λ y → δ (ρ y))) x
  EQ v zero = refl
  EQ v (suc x) = refl

  fuse-arg : ∀{b}{δ : GSubst V}{ρ : Rename} (arg : Arg b)
    → fold-arg f v₀ δ (ren-arg ρ arg) ≡ fold-arg f v₀ (λ x → δ (ρ x)) arg
  fuse-arg {b = ∁ b} (clear arg) = refl
  fuse-arg {b = ■} (ast M) = fold-rename-fusion M
  fuse-arg {b = ν b}{δ}{ρ} (bind arg) = extensionality EXT
    where
    EXT : (v : V) →
      fold-arg f v₀ (v • δ) (ren-arg (ext ρ) arg) ≡
      fold-arg f v₀ (v • (λ y → δ (ρ y))) arg
    EXT v =
      begin
        fold-arg f v₀ (v • δ) (ren-arg (ext ρ) arg)
      ≡⟨ fuse-arg {b}{v • δ}{ext ρ} arg ⟩
        fold-arg f v₀ (λ x → (v • δ) (ext ρ x)) arg
      ≡⟨ cong (λ X → fold-arg f v₀ X arg) (extensionality (EQ {δ}{ρ} v)) ⟩
        fold-arg f v₀ (v • (λ y → δ (ρ y))) arg
      ∎

  fuse-args : ∀{bs}{δ : GSubst V}{ρ : Rename} (args : Args bs)
    → fold-args f v₀ δ (ren-args ρ args)
      ≡ fold-args f v₀ (λ x → δ (ρ x)) args
  fuse-args {bs = []} nil = refl
  fuse-args {bs = b ∷ bs}{δ}{ρ} (cons arg args)
    rewrite fuse-arg {b = b}{δ}{ρ} arg | fuse-args {bs}{δ}{ρ} args = refl  

{-------------------------------------------------------------------------------
 Fold-Subst Fusion

 fold f v₀ δ (⟪ σ ⟫ M) ≡ fold f v₀ (λ x → fold f v₀ δ (σ x)) M
 ------------------------------------------------------------------------------}

fold-subst-fusion : ∀ {f : ((op : Op) → Tuple (sig op) (ArgTy V) → V)}{v₀ : V}
     {δ : GSubst V}{σ : Subst}
     (M : ABT)
   → fold f v₀ δ (⟪ σ ⟫ M) ≡ fold f v₀ (λ x → fold f v₀ δ (σ x)) M
fold-subst-fusion {f = f}{v₀}{δ}{σ} (` x) = refl
fold-subst-fusion {ℓ}{V = V}{f = f}{v₀}{δ}{σ} (op ⦅ args ⦆) =
  cong (λ X → f op X) (fuse-args {δ = δ}{σ} args)
  where
  EQ : {δ : GSubst V}{σ : Subst}(v : V) (x : Var)
     → (fold f v₀ (v • δ) (ext σ x)) ≡ (v • (λ y → fold f v₀ δ (σ y))) x
  EQ {δ} {σ} v zero = refl
  EQ {δ} {σ} v (suc x) = fold-rename-fusion (σ x)

  fuse-arg : ∀{b}{δ : GSubst V}{σ : Subst} (arg : Arg b)
    → (fold-arg f v₀ δ (⟪ σ ⟫ₐ arg)) ≡
                  (fold-arg f v₀ (λ x → fold f v₀ δ (σ x)) arg)
  fuse-arg {∁ b} {δ} {σ} (clear arg) = refl
  fuse-arg {■} {δ} {σ} (ast M) = fold-subst-fusion M
  fuse-arg {ν b} {δ} {σ} (bind arg) = extensionality EXT
     where
     EXT : (v : V) →
          fold-arg f v₀ (v • δ) (⟪ ext σ ⟫ₐ arg)
          ≡ fold-arg f v₀ (v • (λ y → (fold f v₀ δ (σ y)))) arg
     EXT v =
       begin
         fold-arg f v₀ (v • δ) (⟪ ext σ ⟫ₐ arg)
       ≡⟨ fuse-arg {b}{v • δ}{ext σ} arg ⟩
         fold-arg f v₀ (λ x → fold f v₀ (v • δ) (ext σ x)) arg
       ≡⟨ cong (λ X → fold-arg f v₀ X arg) (extensionality (EQ {σ = σ} v)) ⟩
        fold-arg f v₀ (v • (λ y → fold f v₀ δ (σ y))) arg
       ∎
       
  fuse-args : ∀{bs}{δ : GSubst V}{σ : Subst} (args : Args bs)
    → (fold-args f v₀ δ (⟪ σ ⟫₊ args)) ≡
                  (fold-args f v₀ (λ x → fold f v₀ δ (σ x)) args)
  fuse-args {[]} {δ} {σ} nil = refl
  fuse-args {b ∷ bs} {δ} {σ} (cons arg args) 
      rewrite fuse-arg {b = b}{δ}{σ} arg | fuse-args {bs}{δ}{σ} args = refl
