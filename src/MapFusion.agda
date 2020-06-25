open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Environment
open import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Var

module MapFusion (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Map Op sig
open import Renaming
open WithOpSig Op sig

open Shiftable {{...}}
open Quotable {{...}}
open Env  {{...}}

record FusableMap (V₁ E₁ V₂ E₂ V₃ E₃ : Set)
  {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}}
  {{Q₁ : Quotable V₁}}{{Q₂ : Quotable V₂}}{{Q₃ : Quotable V₃}}
  : Set₁ where
  field quote-0₁ : “ (var→val{V₁} 0) ” ≡ ` 0
        quote-0₂ : “ (var→val{V₂} 0) ” ≡ ` 0
        quote-0₃ : “ (var→val{V₃} 0) ” ≡ ` 0
        quote-shift₂ : ∀ (v : V₂) → “ ⇑ v ” ≡ rename (↑ 1) “ v ”
        quote-shift₃ : ∀ (v : V₃) → “ ⇑ v ” ≡ rename (↑ 1) “ v ”

open FusableMap {{...}}

map-rename-fusion : ∀{V₂ E₂ V₃ E₃}
  {{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}}
  {{_ : Env E₂ V₂}} {{_ : Env E₃ V₃}}
  {{_ : Quotable V₂}} {{_ : Quotable V₃}}
  {{_ : FusableMap Var Rename V₂ E₂ V₃ E₃}}
  {σ₁ : Rename}{σ₂ : E₂}{σ₃ : E₃}
   → (M : ABT)
   → σ₂ ∘ σ₁ ≈ σ₃
   → map σ₂ (rename σ₁ M) ≡ map σ₃ M
map-rename-fusion {V₂}{E₂}{V₃}{E₃}{σ₁ = σ₁}{σ₂}{σ₃} M σ₂∘σ₁≈σ₃ =
  map-map-fusion-ext{Var}{Rename}{V₂}{E₂}{V₃}{E₃}{σ₁ = σ₁}{σ₂}{σ₃}
            M σ₂∘σ₁≈σ₃ map-ext
  where
  map-ext : ∀{σ₁ : Rename}{σ₂ : E₂}{σ₃ : E₃}
          → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃
  map-ext {σ₁} {σ₂} {σ₃} σ₂∘σ₁≈σ₃ zero rewrite lookup-0 σ₂ (var→val 0)
      | lookup-0 σ₃ (var→val 0) = trans quote-0₂ (sym quote-0₃)
  map-ext {σ₁} {σ₂} {σ₃} σ₂∘σ₁≈σ₃ (suc x) rewrite lookup-shift σ₁ x
      | lookup-suc σ₂ (var→val 0) (⟅ σ₁ ⟆ x)
      | lookup-suc σ₃ (var→val 0) x =
          trans (quote-shift₂ (⟅ σ₂ ⟆ (⟅ σ₁ ⟆ x)))
                (sym (trans (quote-shift₃ _)
                            (cong (rename (↑ 1)) (sym (σ₂∘σ₁≈σ₃ x)))))



  


map-map-fusion : ∀{V₁ E₁ V₂ E₂ V₃ E₃}
  {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}}
  {{_ : Env E₁ V₁}} {{_ : Env E₂ V₂}} {{_ : Env E₃ V₃}}
  {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
  {{_ : FusableMap V₁ E₁ V₂ E₂ V₃ E₃}}
  {σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
   → (M : ABT)
   → σ₂ ∘ σ₁ ≈ σ₃
   → (∀{σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
      → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃)
   → map σ₂ (map σ₁ M) ≡ map σ₃ M
map-map-fusion (` x) σ₂∘σ₁≈σ₃ mf-ext = σ₂∘σ₁≈σ₃ x
map-map-fusion {V₁}{E₁}{V₂}{E₂}{V₃}{E₃} (op ⦅ args ⦆) σ₂∘σ₁≈σ₃ mf-ext =
  cong (_⦅_⦆ op) (mmf-args args σ₂∘σ₁≈σ₃)
  where
  mm-fuse-ext : ∀{σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
      → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂∘σ₁≈σ₃ zero rewrite lookup-0 σ₁ (var→val 0)
      | lookup-0 σ₃ (var→val 0) =
      begin
          map (σ₂ , (var→val 0)) “ (var→val{V₁} 0) ”
                                     ≡⟨ cong (map (σ₂ , (var→val 0))) quote-0₁ ⟩
          map (σ₂ , (var→val 0)) (` 0)       ≡⟨⟩
          “ ⟅ σ₂ , (var→val 0) ⟆ 0 ”
                               ≡⟨ cong (λ □ → “ □ ”) (lookup-0 σ₂ (var→val 0)) ⟩
          “ (var→val{V₂} 0) ” ≡⟨ quote-0₂ ⟩
          ` 0                ≡⟨ sym quote-0₃ ⟩
          “ (var→val{V₃} 0) ”
      ∎
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂∘σ₁≈σ₃ (suc x) rewrite lookup-suc σ₁ (var→val 0) x
     | lookup-suc σ₃ (var→val 0) x = {!!}
{-
Goal: map (σ₂ , (var→val 0)) “ ⇑ (⟅ σ₁ ⟆ x) ” 
    ≡ map (σ₂ , (var→val 0)) (rename (⇑ 1) “ (⟅ σ₁ ⟆ x) ”)
    ≡ “ ⇑ (⟅ σ₃ ⟆ x) ”
-}

  mmf-arg : ∀{σ₁ σ₂ σ₃ b} (arg : Arg b) → σ₂ ∘ σ₁ ≈ σ₃
     → map-arg σ₂ (map-arg σ₁ arg) ≡ map-arg σ₃ arg
  mmf-args : ∀{σ₁ σ₂ σ₃ bs} (args : Args bs) → σ₂ ∘ σ₁ ≈ σ₃
     → map-args σ₂ (map-args σ₁ args) ≡ map-args σ₃ args
  mmf-arg {b = zero} (ast M) σ₂∘σ₁≈σ₃ =
      cong ast (map-map-fusion M σ₂∘σ₁≈σ₃ mf-ext)
  mmf-arg {b = suc b} (bind arg) σ₂∘σ₁≈σ₃ =
      cong bind (mmf-arg arg (mf-ext σ₂∘σ₁≈σ₃))
  mmf-args {bs = []} nil σ₂∘σ₁≈σ₃ = refl
  mmf-args {bs = b ∷ bs} (cons arg args) σ₂∘σ₁≈σ₃ =
      cong₂ cons (mmf-arg arg σ₂∘σ₁≈σ₃) (mmf-args args σ₂∘σ₁≈σ₃)
