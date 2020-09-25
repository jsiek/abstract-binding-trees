{-# OPTIONS --without-K #-}
{----------------------------------------------------------------------------
                             Renaming
 ---------------------------------------------------------------------------}
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; suc-injective)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Structures hiding (module WithOpSig)
open import GSubst
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂)
open Eq.≡-Reasoning
open import Sig
open import Var 

module Renaming where

Rename : Set
Rename = GSubst Var

ext-0 : ∀ (ρ : Rename) → (ext ρ) 0 ≡ 0
ext-0 ρ = refl

ext-suc : ∀ (ρ : Rename) x → (ext ρ) (suc x) ≡ suc ((ρ) x)
ext-suc ρ x = refl

module WithOpSig (Op : Set) (sig : Op → List Sig)  where

  open import AbstractBindingTree Op sig
  open import Map Op sig

  rename : Rename → ABT → ABT
  rename = map
  ren-arg : Rename → {b : Sig} →  Arg b → Arg b
  ren-arg = map-arg
  ren-args : Rename → {bs : List Sig} →  Args bs → Args bs
  ren-args = map-args
  
  instance
    ABT-is-Shiftable : Shiftable ABT
    ABT-is-Shiftable = record { var→val = `_ ; ⇑ = rename (↑ 1)
                       ; var→val-suc-shift = λ {x} → refl }

  ren-up-seq : ∀ (k : ℕ) (ρ : Rename) → ↑ k ⨟ ρ ≡ drop k ρ
  ren-up-seq k ρ = up-seq k ρ

  ren-cons-seq : ∀ x (ρ₁ ρ₂ : Rename) → (x • ρ₁) ⨟ ρ₂ ≡ (ρ₂) x • (ρ₁ ⨟ ρ₂)
  ren-cons-seq x ρ₁ ρ₂ rewrite cons-seq x ρ₁ ρ₂ = refl

  ren-head : ∀ (ρ : Rename) x → rename (x • ρ) (` 0) ≡ ` x
  ren-head ρ x = refl

  ren-tail : ∀ (ρ : Rename) x → (↑ 1 ⨟ x • ρ) ≡ ρ
  ren-tail ρ x = refl

  inc=⨟ᵣ↑ : ∀ (ρ : Rename) → ⟰ ρ ≡ ρ ⨟ ↑ 1
  inc=⨟ᵣ↑ ρ = refl

  ext-cons-shift : ∀ (ρ : Rename) → ext ρ ≡ (0 • (ρ ⨟ ↑ 1))
  ext-cons-shift ρ = refl

  ren-η : ∀ (ρ : Rename) x → ((ρ) 0 • (↑ 1 ⨟ ρ)) x ≡ (ρ) x
  ren-η ρ 0 = refl
  ren-η ρ (suc x) = refl

  ren-idL : ∀ (ρ : Rename) → id ⨟ ρ ≡ ρ
  ren-idL ρ = refl

  ren-dist :  ∀ x (ρ : Rename) τ → ((x • ρ) ⨟ τ) ≡ (((τ) x) • (ρ ⨟ τ))
  ren-dist x ρ τ rewrite ren-cons-seq x ρ τ = refl

  ren-assoc : ∀ (σ τ θ : Rename) → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  ren-assoc σ τ θ = refl

  seq-rename : ∀ (ρ₁ ρ₂ : Rename) x → (ρ₁ ⨟ ρ₂) x ≡ ρ₂ (ρ₁ x)
  seq-rename ρ₁ ρ₂ x = refl

  compose-rename : ∀ (ρ₁ : Rename) (ρ₂ : Rename) (M : ABT)
     → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₂ ∘ ρ₁) M
  compose-rename ρ₁ ρ₂ M =
    map-map-fusion-ext M (λ x → refl) ren-ext
    where
    ren-ext : ∀{ρ₁ ρ₂ ρ₃ : Rename} → ρ₂ ○ ρ₁ ≈ ρ₃ → (ext ρ₂) ○ (ext ρ₁) ≈ ext ρ₃
    ren-ext ρ₂○ρ₁≈ρ₃ zero = refl
    ren-ext {ρ₁}{ρ₂}{ρ₃} ρ₂○ρ₁≈ρ₃ (suc x) rewrite var-injective (ρ₂○ρ₁≈ρ₃ x) =
       refl

  commute-↑1 : ∀ ρ M
     → rename (ext ρ) (rename (↑ 1) M) ≡ rename (↑ 1) (rename ρ M)
  commute-↑1 ρ M = begin
      rename (ext ρ) (rename (↑ 1) M)  ≡⟨ compose-rename (↑ 1) (ext ρ) M ⟩
      rename (↑ 1 ⨟ (ext ρ)) M
                        ≡⟨ cong (λ □ → rename (↑ 1 ⨟ □) M) (ext-cons-shift _) ⟩
      rename (↑ 1 ⨟ (0 • (ρ ⨟ ↑ 1))) M
                                  ≡⟨ cong (λ □ → rename □ M) (ren-tail _ zero) ⟩
      rename (ρ ⨟ ↑ 1) M           ≡⟨ sym (compose-rename ρ (↑ 1) M) ⟩
      rename (↑ 1) (rename ρ M)    ∎

  FV-rename-fwd : ∀ (ρ : Rename) M y → FV M y
     → FV (rename ρ M) (ρ y)
  FV-rename-fwd ρ (` x) y refl = refl
  FV-rename-fwd ρ (op ⦅ args ⦆) y fvMy = fvr-args ρ (sig op) args y fvMy
    where
    fvr-arg : ∀ (ρ : Rename) b (arg : Arg b) y
        → FV-arg arg y → FV-arg (ren-arg ρ arg) (ρ y)
    fvr-args : ∀ (ρ : Rename) bs (args : Args bs) y
        → FV-args args y → FV-args (ren-args ρ args) (ρ y)
    fvr-arg ρ ■ (ast M) y fvarg = FV-rename-fwd ρ M y fvarg
    fvr-arg ρ (ν b) (bind arg) y fvarg =
        fvr-arg (ρ , (var→val 0)) b arg (suc y) fvarg
    fvr-arg ρ (∁ b) (clear arg) y ()
    fvr-args ρ [] nil y ()
    fvr-args ρ (b ∷ bs) (cons arg args) y (inj₁ fvargy) =
        inj₁ (fvr-arg ρ b arg y fvargy)
    fvr-args ρ (b ∷ bs) (cons arg args) y (inj₂ fvargsy) =
        inj₂ (fvr-args ρ bs args y fvargsy)

  FV-rename : ∀ (ρ : Rename) M y → FV (rename ρ M) y
     → Σ[ x ∈ Var ] ρ x ≡ y × FV M x
  FV-rename ρ (` x) y refl = ⟨ x , ⟨ refl , refl ⟩ ⟩
  FV-rename ρ (op ⦅ args ⦆) y fv = fvr-args ρ (sig op) args y fv
    where
    fvr-arg : ∀ (ρ : Rename) b (arg : Arg b) y
        → FV-arg (ren-arg ρ arg) y → Σ[ x ∈ Var ] (ρ) x ≡ y × FV-arg arg x
    fvr-args : ∀ (ρ : Rename) bs (args : Args bs) y
        → FV-args (ren-args ρ args) y → Σ[ x ∈ Var ] (ρ) x ≡ y × FV-args args x
    fvr-arg ρ b (ast M) y fv = FV-rename ρ M y fv 
    fvr-arg ρ (ν b) (bind arg) y fv 
        with fvr-arg (ext ρ) b arg (suc y) fv
    ... | ⟨ 0 , eq ⟩  
        with eq
    ... | ()
    fvr-arg ρ (ν b) (bind arg) y fv 
        | ⟨ suc x , ⟨ eq , sx∈arg ⟩ ⟩ =
          ⟨ x , ⟨ suc-injective eq , sx∈arg ⟩ ⟩
    fvr-args ρ [] nil y ()
    fvr-args ρ (b ∷ bs) (cons arg args) y (inj₁ fv)
        with fvr-arg ρ b arg y fv
    ... | ⟨ x , ⟨ ρx , x∈arg ⟩ ⟩ = 
          ⟨ x , ⟨ ρx , (inj₁ x∈arg) ⟩ ⟩
    fvr-args ρ (b ∷ bs) (cons arg args) y (inj₂ fv)
        with fvr-args ρ bs args y fv
    ... | ⟨ x , ⟨ ρx , x∈args ⟩ ⟩ = 
          ⟨ x , ⟨ ρx , (inj₂ x∈args) ⟩ ⟩

  rename-FV-⊥ : ∀ y (ρ : Rename) M → (∀ x → (ρ) x ≢ y) → FV (rename ρ M) y → ⊥
  rename-FV-⊥ y ρ M ρx≢y fvρM 
      with FV-rename ρ M y fvρM
  ... | ⟨ x , ⟨ ρxy , x∈M ⟩ ⟩ = ⊥-elim (ρx≢y x ρxy)
  
  FV-↑1-0 : ∀ M → FV (rename (↑ 1) M) 0 → ⊥
  FV-↑1-0 M = rename-FV-⊥ 0 (↑ 1) M (λ { x () })
