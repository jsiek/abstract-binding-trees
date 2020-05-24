{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Syntax
open import Generic

open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-step; suc-injective)
open import Data.List using (List; []; _∷_; length)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

module WellScoped (Op : Set) (sig : Op → List ℕ) where

  open OpSig Op sig hiding (rename)

  mk-list : ℕ → List ⊤
  mk-list 0 = []
  mk-list (suc n) = tt ∷ mk-list n

  len-mk-list : ∀ n → Data.List.foldr (λ _ → suc) 0 (mk-list n) ≡ n
  len-mk-list zero = refl
  len-mk-list (suc n) = cong suc (len-mk-list n)

  {-# REWRITE len-mk-list #-}

  WS : ℕ → ABT → Set
  WS-arg : ℕ → {b : ℕ} → Arg b → Set
  WS-args : ℕ → {bs : List ℕ} → Args bs → Set
  WS-Rename : ℕ → Rename → ℕ → Set
  
  𝒫 : Op → List ⊤ → ⊤ → Set
  𝒫 op Γ A = ⊤

  open ArgResult Var ABT
  open ABTPred Op sig 𝒫
  open PresArgResult Op sig 𝒫 _∋_⦂_ _⊢_⦂_
  open Rename Op sig
  open RenamePres Op sig 𝒫
  open Foldable R

  len : ∀{bs} → Args bs → ℕ
  len nil = 0
  len (cons _ args) = suc (len args)

  WS n M = (mk-list n) ⊢ M ⦂ tt
  WS-arg n {b} arg = b ∣ (mk-list n) ⊢a arg ⦂ tt
  WS-args n {bs} args = bs ∣ (mk-list n) ⊢as args ⦂ (mk-list (len args))
  
  open GenericSub Var (λ x → x) suc using (⧼_⧽; inc)

  {- move to new sister module of GenericSub. -Jeremy -}
  inc-suc : ∀ ρ x → ⧼ inc ρ ⧽ x ≡ suc (⧼ ρ ⧽ x)
  inc-suc (↑ k) x = refl
  inc-suc (x₁ • ρ) zero = refl
  inc-suc (x₁ • ρ) (suc x) = inc-suc ρ x
  
  {- Move to RenamePres? -}
  op-pres : ∀ {op : Op}{Rs : ArgsRes (sig op)}{Δ : List ⊤}{A : ⊤}{As : List ⊤}
     → sig op ∣ Δ ⊢rs Rs ⦂ As
     → 𝒫 op As A
     → Δ ⊢ (fold-op op Rs) ⦂ A
  op-pres {op}{Rs}{Δ}{A}{As} ⊢Rs 𝒫op =
      op-op (subst (λ □ → sig op ∣ □ ⊢as r-args Rs ⦂ As) refl (res→args ⊢Rs)) tt

  _⦂_⇒_ : Rename → List ⊤ → List ⊤ → Set
  _⦂_⇒_ ρ Γ Δ = ∀ {x}{A} → Γ ∋ x ⦂ tt → Δ ∋ ⧼ ρ ⧽ x ⦂ A

  WS-Rename Γ ρ Δ = ρ ⦂ (mk-list Γ) ⇒ (mk-list Δ)

  {- Move to RenamePres? -}
  extend-pres : ∀ {v}{σ}{Γ}{Δ}{A}
     → (A ∷ Δ) ∋ v ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → (extend σ v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  extend-pres {v} {σ} {Γ} {Δ} {tt} ∋v σΓΔ {zero} {tt} ∋x = ∋v
  extend-pres {v} {σ} {Γ} {Δ} {tt} ∋v σΓΔ {suc x} {tt} ∋x
      rewrite inc-suc σ x = σΓΔ ∋x

  WSPres : Preservable ⊤ R
  WSPres = record { 𝒫 = 𝒫 ; _⦂_⇒_ = _⦂_⇒_ ; _⊢v_⦂_ = _∋_⦂_ ; _⊢c_⦂_ = _⊢_⦂_
             ; lookup-pres = λ σΓΔ Γ∋x → σΓΔ Γ∋x
             ; extend-pres = extend-pres
             ; ret-pres = var-p ; var-pres = λ Γ∋x → Γ∋x ; op-pres = op-pres }
  open Preservation R WSPres

  WS-rename : ∀ {Γ Δ ρ M} → WS-Rename Γ ρ Δ → WS Γ M → WS Δ (rename ρ M)
  WS-rename {Γ}{Δ}{ρ}{M} ΓρΔ WSM = preserve {M}{ρ}{mk-list Γ}{mk-list Δ} WSM ΓρΔ

