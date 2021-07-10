{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Product
    using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.List using (List; []; _∷_) renaming (map to lmap)
open import Data.Unit.Polymorphic using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)

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
 ------------------------------------------------------------------------------}

ArgTy : {ℓ : Level} → Set ℓ → Sig → Set ℓ
ArgTy V ■ = V
ArgTy V (ν b) = V → ArgTy V b
ArgTy V (∁ b) = ArgTy V b

fold : {{_ : Shiftable V}}
   → ((op : Op) → Tuple (sig op) (ArgTy V) → V)
   → GSubst V → ABT → V
fold-arg : {{_ : Shiftable V}} 
   → ((op : Op) → Tuple (sig op) (ArgTy V) → V)
   → GSubst V → {b : Sig} → Arg b → ArgTy V b
fold-args : {{_ : Shiftable V}}
   → ((op : Op) → Tuple (sig op) (ArgTy V) → V)
   → GSubst V → {bs : List Sig} → Args bs → Tuple bs (ArgTy V)

fold f σ (` x) = σ x
fold f σ (op ⦅ args ⦆) = f op (fold-args f σ {sig op} args)
fold-arg f σ (ast M) = (fold f σ M)
fold-arg f σ (bind arg) v = fold-arg f (v • ⟰ σ) arg
fold-arg f σ (clear arg) = fold-arg f id arg
fold-args f σ {[]} nil = tt
fold-args f σ {b ∷ bs} (cons arg args) =
  ⟨ fold-arg f σ arg , fold-args f σ args ⟩

{-------------------------------------------------------------------------------
 Fold-Rename Fusion
 ------------------------------------------------------------------------------}

fold-rename-fusion : ∀ {f : ((op : Op) → Tuple (sig op) (ArgTy V) → V)}
     {δ : GSubst V}{ρ : Rename}
     {{_ : Shiftable V}}
     (M : ABT)
   → fold f δ (rename ρ M) ≡ fold f (λ x → fold f δ (` ρ x)) M
fold-rename-fusion {f = f} {δ} {ρ} (` x) = refl
fold-rename-fusion {ℓ}{V = V}{f = f} {δ} {ρ} (op ⦅ args ⦆) =
  cong (λ X → f op X) (fuse-args {δ = δ}{ρ} args)

  where
  EQ : {δ : GSubst V}{ρ : Rename}(v : V) (x : Var)
     → (v • (λ x → ⇑ (δ (ρ x)))) x ≡  (v • ⟰ δ) (ext ρ x)
  EQ {δ} {ρ} v zero = refl
  EQ {δ} {ρ} v (suc x) = refl
     
  fuse-arg : ∀{b}{δ : GSubst V}{ρ : Rename} (arg : Arg b)
    → (fold-arg f δ (ren-arg ρ arg)) ≡
                  (fold-arg f (λ x → fold f δ “ ρ x ”) arg)
  fuse-arg {b = ■} (ast M) = fold-rename-fusion M
  fuse-arg {b = ν b}{δ}{ρ} (bind arg) = extensionality EXT
     where
     EXT : (v : V) →
          (fold-arg f (v • ⟰ δ) (ren-arg (ext ρ) arg)) ≡
                (fold-arg f (v •  (λ x → ⇑ (δ (ρ x)))) arg)
     EXT v rewrite extensionality (EQ {δ}{ρ} v) =
         fuse-arg {b}{v • ⟰ δ}{ext ρ} arg
  fuse-arg {b = ∁ b} (clear arg) = refl

  fuse-args : ∀{bs}{δ : GSubst V}{ρ : Rename} (args : Args bs)
    → (fold-args f δ (ren-args ρ args)) ≡
                  (fold-args f (λ x → fold f δ “ ρ x ”) args)
  fuse-args {bs = []} nil = refl
  fuse-args {bs = b ∷ bs}{δ}{ρ} (cons arg args)
      rewrite fuse-arg {b = b}{δ}{ρ} arg | fuse-args {bs}{δ}{ρ} args = refl

{-------------------------------------------------------------------------------
 Fold-Subst Fusion
 ------------------------------------------------------------------------------}

fold-subst-fusion : ∀ {f : ((op : Op) → Tuple (sig op) (ArgTy V) → V)}
     {δ : GSubst V}{σ : Subst}
     {{_ : Shiftable V}}
     (M : ABT)
   → fold f δ (⟪ σ ⟫ M) ≡ fold f (λ x → fold f δ (σ x)) M
fold-subst-fusion {f = f}{δ}{σ} (` x) = refl
fold-subst-fusion {ℓ}{V = V}{f = f}{δ}{σ} (op ⦅ args ⦆) =
  cong (λ X → f op X) (fuse-args {δ = δ}{σ} args)

  where
  fuse-arg : ∀{b}{δ : GSubst V}{σ : Subst} (arg : Arg b)
    → (fold-arg f δ (⟪ σ ⟫ₐ arg)) ≡
                  (fold-arg f (λ x → fold f δ (σ x)) arg)
  fuse-arg {■} {δ} {σ} (ast M) = fold-subst-fusion M
  fuse-arg {ν b} {δ} {σ} (bind arg) = extensionality EXT
     where
     EXT : (x : V) →
          fold-arg f (x • ⟰ δ) (⟪ ext σ ⟫ₐ arg)
          ≡ fold-arg f (x • (λ y → ⇑ (fold f δ (σ y)))) arg
     EXT v = {!!}
     
  fuse-arg {∁ b} {δ} {σ} (clear arg) = refl
  
  fuse-args : ∀{bs}{δ : GSubst V}{σ : Subst} (args : Args bs)
    → (fold-args f δ (⟪ σ ⟫₊ args)) ≡
                  (fold-args f (λ x → fold f δ (σ x)) args)
  fuse-args {[]} {δ} {σ} nil = refl
  fuse-args {b ∷ bs} {δ} {σ} (cons arg args) 
      rewrite fuse-arg {b = b}{δ}{σ} arg | fuse-args {bs}{δ}{σ} args = refl

