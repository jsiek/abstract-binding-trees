open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import GenericSubstitution
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
    using (begin_; _≡⟨_⟩_; _∎)
open import SimulateSubst
open import Var

module SubstProperties (Op : Set) (sig : Op → List ℕ) where

  open import AbstractBindingTree Op sig
  open import Rename Op sig
     using (Rename; rename; ⦉_⦊; ren-arg; ren-args; ext)
  open import Subst Op sig
  open RenameSubst Op sig
              
  subst-is-substable : Substable ABT
  subst-is-substable = record
                          { var→val = `_
                          ; shift = rename (↑ 1)
                          ; ⦑_⦒ = ⟪_⟫
                          ; var→val-suc-shift = λ {x} → refl
                          ; sub-var→val = λ σ x → refl
                          ; shift-⦑↑1⦒ = λ M → rename-subst (↑ 1) M
                          }
  open import GenericSubProperties subst-is-substable
    using (_⨟_; extend-cons-shift; seq-subst)
    renaming (inc-suc to incs-suc; extend-suc to exts-suc-rename) public

  exts-cons-shift : ∀ (σ : Substitution ABT) → exts σ ≡ ((` 0) • (σ ⨟ ↑ 1))
  exts-cons-shift σ = extend-cons-shift σ (` 0)

  open import MoreGenSubProperties Op sig subst-is-substable
      (λ M → M) (λ x → refl) public

  {-

  need compose-rename

  commute-subst-rename : ∀{M : ABT}{σ : Subst}
                          {ρ : Rename}
       → (∀{x : Var} → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
       → ⟪ exts σ ⟫ (rename ρ M) ≡ rename ρ (⟪ σ ⟫ M)
  commute-subst-rename-arg : ∀{n}{A : Arg n}{σ : Subst}
                          {ρ : Rename}
       → (∀{x : Var} → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
       → ⟪ exts σ ⟫ₐ (ren-arg ρ A) ≡ ren-arg ρ (⟪ σ ⟫ₐ A)
  commute-subst-renames : ∀{S}{Ms : Args S}{σ : Subst}
                          {ρ : Rename}
       → (∀{x : Var} → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
       → ⟪ exts σ ⟫₊ (ren-args ρ Ms) ≡ ren-args ρ (⟪ σ ⟫₊ Ms)
  commute-subst-rename {` x} r = r
  commute-subst-rename {op ⦅ As ⦆} r =
      cong (λ □ → op ⦅ □ ⦆) (commute-subst-renames r)
  commute-subst-rename-arg {.0} {ast M}{σ}{ρ} r
      rewrite commute-subst-rename {M}{σ}{ρ} r = refl
  commute-subst-rename-arg {.(suc _)} {bind A}{σ}{ρ} r =
     cong bind (commute-subst-rename-arg (λ {x} → G{x}))
     where
     G : ∀{x} → ⟦ exts (exts σ) ⟧ (⦉ ext ρ ⦊ x) ≡ rename (ext ρ) (⟦ exts σ ⟧ x)
     G {zero} rewrite exts-cons-shift σ = refl
     G {suc x} rewrite exts-cons-shift (exts σ)
        | seq-subst (exts σ) (↑ 1) (⦉ ρ ⦊ x) | r {x}
        | exts-cons-shift σ | seq-subst σ (↑ 1) x
        | sym (rename-subst (↑ 1) (rename ρ (⟦ σ ⟧ x)))
        | sym (rename-subst (↑ 1) (⟦ σ ⟧ x))
        | compose-rename {⟦ σ ⟧ x} {ρ} {↑ 1}
        | compose-rename {⟦ σ ⟧ x} {↑ 1} {ext ρ}
        | dropr-ext 0 ρ | sym (dropr-inc 0 ρ)
        | dropr-0 (inc ρ) | inc=⨟ᵣ↑ ρ = refl

  commute-subst-renames {.[]} {nil} r = refl
  commute-subst-renames {.(_ ∷ _)} {cons A As} r =
      cong₂ cons (commute-subst-rename-arg r) (commute-subst-renames r)
-}
{-
  {- need commute-subst-rename? -}

  inc-shift : ∀ σ M → ⟪ incs σ ⟫ M ≡ rename (↑ 1) (⟪ σ ⟫ M)
  inc-shift σ M = {!!}

  open Params (λ σ v → refl) {!!} (λ σ v → refl) inc-shift public
-}

{-
  open Substable subst-is-substable

  ⦑σ⦒-tail : (σ : Substitution ABT) (v w : ABT) →
      ⦑ w • σ ⦒ (shift v) ≡ ⦑ σ ⦒ v
  ⦑σ⦒-tail σ v w =
    begin
      ⟪ w • σ ⟫ (rename (↑ 1) v)
    ≡⟨ {!!} ⟩
      ⟪ σ ⟫ v
    ∎
  {-
      rewrite rename-subst (↑ 1) v
      | sub-tail w σ = {!refl!}
  -}

  open Params (λ σ v → refl) {!!} (λ σ v → refl) 
-}
