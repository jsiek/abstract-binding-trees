{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import GenericSubstitution
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
    using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import SimulateSubst
open import Var

module SubstProperties (Op : Set) (sig : Op → List ℕ) where

  open import AbstractBindingTree Op sig
  open import Rename Op sig
     using (Rename; rename; ⦉_⦊; ren-arg; ren-args; ext; inc; compose-rename;
            dropr-ext; dropr-inc; dropr-0; inc=⨟ᵣ↑; _⨟ᵣ_; ext-suc;
            ren-res→arg; ren-res→args; ren-tail)
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
    renaming (inc-suc to incs-suc; inc=⨟↑ to incs=⨟↑;
              extend-suc to exts-suc-rename) public

  exts-cons-shift : ∀ (σ : Substitution ABT) → exts σ ≡ ((` 0) • (σ ⨟ ↑ 1))
  exts-cons-shift σ = extend-cons-shift σ (` 0)

  open import MoreGenSubProperties Op sig subst-is-substable
      (λ M → M) (λ x → refl) public

  commute-subst-rename : ∀{M : ABT}{σ : Subst}
                          {ρ : Rename}
       → (∀{x : Var} → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
       → ⟪ exts σ ⟫ (rename ρ M) ≡ rename ρ (⟪ σ ⟫ M)
  commute-subst-arg : ∀{b}{arg : Arg b}{σ}{ρ}
     → (∀{x : Var} → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
     → sub-res→arg (⟪ exts σ ⟫ₐ (ren-res→arg (ren-arg ρ arg)))
       ≡ ren-res→arg (ren-arg ρ (sub-res→arg (⟪ σ ⟫ₐ arg)))
  commute-subst-renames : ∀{bs}{args : Args bs}{σ}{ρ}
     → (∀{x : Var} → ⟦ exts σ ⟧ (⦉ ρ ⦊ x) ≡ rename ρ (⟦ σ ⟧ x))
     → sub-res→args (⟪ exts σ ⟫₊ (ren-res→args (ren-args ρ args)))
       ≡ ren-res→args (ren-args ρ (sub-res→args (⟪ σ ⟫₊ args)))


  commute-subst-rename {` x} r = r
  commute-subst-rename {op ⦅ args ⦆} r =
      cong (λ □ → op ⦅ □ ⦆) (commute-subst-renames {sig op}{args} r)
  commute-subst-arg {zero} {ast M} {σ} {ρ} r =
      cong ast (commute-subst-rename {M} r)
  commute-subst-arg {suc b} {bind arg} {σ} {ρ} r =
      cong bind (commute-subst-arg {b}{arg} (λ {x} → G {x}))
     where
     G : ∀{x} → ⟦ exts (exts σ) ⟧ (⦉ ext ρ ⦊ x) ≡ rename (ext ρ) (⟦ exts σ ⟧ x)
     G {zero} rewrite exts-cons-shift σ = refl
     G {suc x} =
         begin
            ⟦ exts (exts σ) ⟧ (⦉ ext ρ ⦊ (suc x))
         ≡⟨ cong (λ □ → ⟦ exts □ ⟧ (⦉ ext ρ ⦊ (suc x))) (exts-cons-shift σ) ⟩
            ⟦ exts (` 0 • (σ ⨟ ↑ 1)) ⟧ (⦉ ext ρ ⦊ (suc x))
         ≡⟨ cong (λ □ → ⟦ exts (` 0 • (σ ⨟ ↑ 1)) ⟧ □) (ext-suc ρ x) ⟩
            ⟦ ` 0 • (` 1 • incs (σ ⨟ ↑ 1)) ⟧ (suc (⦉ ρ ⦊ x))
         ≡⟨⟩
            ⟦ ` 1 • incs (σ ⨟ ↑ 1) ⟧ (⦉ ρ ⦊ x)
         ≡⟨ cong (λ □ → ⟦ ` 1 • □ ⟧ (⦉ ρ ⦊ x)) (incs=⨟↑ (σ ⨟ ↑ 1)) ⟩
           ⟦ ` 1 • ((σ ⨟ ↑ 1) ⨟ ↑ 1) ⟧ (⦉ ρ ⦊ x)
         ≡⟨ cong (λ □ → ⟦ ` 1 • (□ ⨟ ↑ 1) ⟧ (⦉ ρ ⦊ x)) (sym (incs=⨟↑ σ)) ⟩
           ⟦ ` 1 • (incs σ ⨟ ↑ 1) ⟧ (⦉ ρ ⦊ x)
         ≡⟨⟩
           ⟦ (` 0 • incs σ) ⨟ ↑ 1 ⟧ (⦉ ρ ⦊ x)
         ≡⟨ seq-subst (exts σ) (↑ 1) (⦉ ρ ⦊ x) ⟩
           ⟪ ↑ 1 ⟫ (⟦ exts σ ⟧ (⦉ ρ ⦊ x))
         ≡⟨ sym (rename-subst (↑ 1) (⟦ exts σ ⟧ (⦉ ρ ⦊ x))) ⟩
           rename (↑ 1) (⟦ exts σ ⟧ (⦉ ρ ⦊ x))
         ≡⟨ cong (λ □ → rename (↑ 1) □) (r {x}) ⟩
            rename (↑ 1) (rename ρ (⟦ σ ⟧ x))
         ≡⟨ compose-rename {⟦ σ ⟧ x} ⟩
            rename (ρ ⨟ᵣ ↑ 1) (⟦ σ ⟧ x)
         ≡⟨ cong (λ □ → rename □ (⟦ σ ⟧ x)) (sym (inc=⨟ᵣ↑ ρ)) ⟩
            rename (inc ρ) (⟦ σ ⟧ x)
         ≡⟨ cong (λ □ → rename □ (⟦ σ ⟧ x)) (ren-tail {inc ρ}{x}) ⟩
            rename (↑ 1 ⨟ᵣ (0 • inc ρ)) (⟦ σ ⟧ x)
         ≡⟨ sym (compose-rename {⟦ σ ⟧ x})  ⟩
            rename (0 • inc ρ) (rename (↑ 1) (⟦ σ ⟧ x))
         ≡⟨ cong (λ □ → rename (0 • inc ρ) □) (rename-subst (↑ 1) (⟦ σ ⟧ x)) ⟩
            rename (0 • inc ρ) (⟪ ↑ 1 ⟫ (⟦ σ ⟧ x))
         ≡⟨ cong (λ □ → rename (0 • inc ρ) □) (sym (seq-subst σ (↑ 1) x)) ⟩
            rename (0 • inc ρ) (⟦ σ ⨟ ↑ 1 ⟧ x)
         ≡⟨ cong (λ □ → rename (0 • inc ρ) (⟦ □ ⟧ x)) (sym (incs=⨟↑ σ)) ⟩
            rename (0 • inc ρ) (⟦ incs σ ⟧ x)
         ≡⟨⟩
            rename (ext ρ) (⟦ exts σ ⟧ (suc x))
         ∎
  commute-subst-renames {[]} {nil} {σ} {ρ} r = refl
  commute-subst-renames {b ∷ bs} {cons arg args} {σ} {ρ} r =
      cong₂ cons (commute-subst-arg{b}{arg} r)
                 (commute-subst-renames {bs}{args} r)

  exts-suc' : ∀ σ x → ⟦ exts σ ⟧ (suc x) ≡ rename (↑ 1) (⟦ σ ⟧ x)
  exts-suc' σ x =
      begin
          ⟦ exts σ ⟧ (suc x)
      ≡⟨⟩
          ⟦ incs σ ⟧ x
      ≡⟨ cong (λ □ → ⟦ □ ⟧ x) (incs=⨟↑ σ) ⟩
        ⟦ σ ⨟ ↑ 1 ⟧ x
      ≡⟨ seq-subst σ (↑ 1) x ⟩
        ⟪ ↑ 1 ⟫ (⟦ σ ⟧ x)
      ≡⟨ sym (rename-subst (↑ 1) (⟦ σ ⟧ x)) ⟩
        rename (↑ 1) (⟦ σ ⟧ x)
      ∎

  inc-shift : ∀ σ M → ⟪ incs σ ⟫ M ≡ rename (↑ 1) (⟪ σ ⟫ M)
  inc-shift σ M =
      begin
          ⟪ incs σ ⟫ M
      ≡⟨ cong (λ □ → ⟪ □ ⟫ M) (incs=⨟↑ σ) ⟩
          ⟪ σ ⨟ ↑ 1 ⟫ M
      ≡⟨ {!!} ⟩
          ⟪ ` 0 • incs σ ⟫ (rename (↑ 1) M)
      ≡⟨⟩
          ⟪ exts σ ⟫ (rename (↑ 1) M)
      ≡⟨ commute-subst-rename {M}{σ}{↑ 1} (λ {x} → exts-suc' σ x) ⟩
          rename (↑ 1) (⟪ σ ⟫ M)
      ∎

  open Params (λ σ v → refl) {!!} (λ σ v → refl) inc-shift public


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
