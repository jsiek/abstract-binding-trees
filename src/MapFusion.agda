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

record QuoteShift (V : Set)
  {{S : Shiftable V}}{{Q : Quotable V}}
  : Set₁ where
  field quote-var→val : ∀ x → “ (var→val{V} x) ” ≡ ` x
        quote-shift : ∀ (v : V) → “ ⇑ v ” ≡ rename (↑ 1) “ v ”

open QuoteShift {{...}}

instance
  ABT-is-QuoteShift : QuoteShift ABT
  ABT-is-QuoteShift = record { quote-var→val = λ x → refl
                             ; quote-shift = λ v → refl }

map-rename-fusion : ∀{V₂ E₂ V₃ E₃}
  {{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}} {{_ : Env E₂ V₂}} {{_ : Env E₃ V₃}}
  {{_ : Quotable V₂}} {{_ : Quotable V₃}}
  {{_ : QuoteShift V₂}}{{_ : QuoteShift V₃}}
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
      | lookup-0 σ₃ (var→val 0) =
      trans (quote-var→val{V₂} 0) (sym (quote-var→val{V₃} 0))
  map-ext {σ₁} {σ₂} {σ₃} σ₂∘σ₁≈σ₃ (suc x) rewrite lookup-shift σ₁ x
      | lookup-suc σ₂ (var→val 0) (⟅ σ₁ ⟆ x)
      | lookup-suc σ₃ (var→val 0) x =
          trans (quote-shift{V₂} (⟅ σ₂ ⟆ (⟅ σ₁ ⟆ x)))
                (sym (trans (quote-shift{V₃} _)
                            (cong (rename (↑ 1)) (sym (σ₂∘σ₁≈σ₃ x)))))

rename-map-fusion : ∀{V₁ E₁ V₃ E₃}
  {{S₁ : Shiftable V₁}}{{S₃ : Shiftable V₃}} {{_ : Env E₁ V₁}} {{_ : Env E₃ V₃}}
  {{_ : Quotable V₁}} {{_ : Quotable V₃}}
  {{_ : QuoteShift V₁}}{{_ : QuoteShift V₃}}
  {σ₁ : E₁}{ρ₂ : Rename}{σ₃ : E₃}
   → (M : ABT)
   → ρ₂ ∘ σ₁ ≈ σ₃
   → rename ρ₂ (map σ₁ M) ≡ map σ₃ M
rename-map-fusion {V₁}{E₁}{V₃}{E₃}{σ₁ = σ₁}{ρ₂}{σ₃} M ρ₂∘σ₁≈σ₃ =
  map-map-fusion-ext{V₁}{E₁}{Var}{Rename}{V₃}{E₃}{σ₁ = σ₁}{ρ₂}{σ₃}
            M ρ₂∘σ₁≈σ₃ map-ext
  where
  map-ext : ∀{σ₁ : E₁}{ρ₂ : Rename}{σ₃ : E₃}
          → ρ₂ ∘ σ₁ ≈ σ₃ → ext ρ₂ ∘ ext σ₁ ≈ ext σ₃
  map-ext {σ₁} {ρ₂} {σ₃} ρ₂∘σ₁≈σ₃ zero rewrite lookup-0 σ₁ (var→val 0)
    | lookup-0 σ₃ (var→val 0) | quote-var→val{V₁} 0 | quote-var→val{V₃} 0 = refl
  map-ext {σ₁} {ρ₂} {σ₃} ρ₂∘σ₁≈σ₃ (suc x) rewrite lookup-suc σ₁ (var→val 0) x
      | lookup-suc σ₃ (var→val 0) x | quote-shift{V₁} (⟅ σ₁ ⟆ x)
      | quote-shift{V₃} (⟅ σ₃ ⟆ x) = begin
      rename (0 • inc ρ₂) (map (↑ 1) “ ⟅ σ₁ ⟆ x ”)
          ≡⟨ compose-rename (↑ 1) (0 • inc ρ₂) “ ⟅ σ₁ ⟆ x ” ⟩
      rename (↑ 1 ⨟ (0 • inc ρ₂)) “ ⟅ σ₁ ⟆ x ”
         ≡⟨ cong (λ □ → rename □ “ ⟅ σ₁ ⟆ x ”) (ren-tail (inc ρ₂) 0) ⟩
      rename (inc ρ₂) “ ⟅ σ₁ ⟆ x ”
         ≡⟨ cong (λ □ → rename □ “ ⟅ σ₁ ⟆ x ”) (inc=⨟ᵣ↑ ρ₂) ⟩
      rename (ρ₂ ⨟ ↑ 1) “ ⟅ σ₁ ⟆ x ”
         ≡⟨ sym (compose-rename ρ₂ (↑ 1) “ ⟅ σ₁ ⟆ x ”) ⟩
      rename (↑ 1) (rename ρ₂ “ ⟅ σ₁ ⟆ x ”)
         ≡⟨ cong (rename (↑ 1)) (ρ₂∘σ₁≈σ₃ x) ⟩
      map (↑ 1) “ ⟅ σ₃ ⟆ x ”
      ∎

map-map-fusion : ∀{V₁ E₁ V₂ E₂ V₃ E₃}
  {{S₁ : Shiftable V₁}}{{S₂ : Shiftable V₂}}{{S₃ : Shiftable V₃}}
  {{_ : Env E₁ V₁}} {{_ : Env E₂ V₂}} {{_ : Env E₃ V₃}}
  {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
  {{_ : QuoteShift V₁}}{{_ : QuoteShift V₂}}{{_ : QuoteShift V₃}}
  {σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
   → (M : ABT)
   → σ₂ ∘ σ₁ ≈ σ₃
   → map σ₂ (map σ₁ M) ≡ map σ₃ M
map-map-fusion (` x) σ₂∘σ₁≈σ₃ = σ₂∘σ₁≈σ₃ x
map-map-fusion {V₁}{E₁}{V₂}{E₂}{V₃}{E₃}{{S₁}}{{S₂}}{{S₃}}
  (op ⦅ args ⦆) σ₂∘σ₁≈σ₃ =
  cong (_⦅_⦆ op) (mmf-args args σ₂∘σ₁≈σ₃)
  where
  G : ∀{σ₂ : E₂} → _∘_≈_{Var}{Rename} (σ₂ , (var→val 0)) (↑ 1) (⟰ σ₂)
  G {σ₂} x rewrite lookup-suc σ₂ (var→val 0) x | lookup-shift σ₂ x = refl
  H : ∀{σ₂ : E₂} → ↑ 1 ∘ σ₂ ≈ ⟰ σ₂
  H {σ₂} x rewrite lookup-shift σ₂ x | quote-shift{V₂} (⟅ σ₂ ⟆ x) = refl

  mm-fuse-ext : ∀{σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}
      → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂∘σ₁≈σ₃ zero rewrite lookup-0 σ₁ (var→val 0)
      | lookup-0 σ₃ (var→val 0) =
      begin
          map (σ₂ , (var→val 0)) “ (var→val{V₁} 0) ”
                    ≡⟨ cong (map (σ₂ , (var→val{V₂} 0))) (quote-var→val{V₁} 0) ⟩
          map (σ₂ , (var→val 0)) (` 0)       ≡⟨⟩
          “ ⟅ σ₂ , (var→val 0) ⟆ 0 ”
                               ≡⟨ cong (λ □ → “ □ ”) (lookup-0 σ₂ (var→val 0)) ⟩
          “ (var→val{V₂} 0) ”        ≡⟨ (quote-var→val{V₂} 0) ⟩
          ` 0                        ≡⟨ sym (quote-var→val{V₃} 0) ⟩
          “ (var→val{V₃} 0) ”        ∎
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂∘σ₁≈σ₃ (suc x) rewrite lookup-suc σ₁ (var→val 0) x
      | lookup-suc σ₃ (var→val 0) x = begin
      map (σ₂ , (var→val 0)) “ ⇑ (⟅ σ₁ ⟆ x) ”
                ≡⟨ cong (map (σ₂ , (var→val 0))) (quote-shift{V₁} (⟅ σ₁ ⟆ x)) ⟩
      map (σ₂ , (var→val 0)) (rename (↑ 1) “ ⟅ σ₁ ⟆ x ”)
                     ≡⟨ map-rename-fusion “ ⟅ σ₁ ⟆ x ” G ⟩
      map (⟰ σ₂) “ ⟅ σ₁ ⟆ x ”
                              ≡⟨ sym (rename-map-fusion “ ⟅ σ₁ ⟆ x ” H) ⟩
      rename (↑ 1) (map σ₂ “ ⟅ σ₁ ⟆ x ”) ≡⟨ cong (rename (↑ 1)) (σ₂∘σ₁≈σ₃ x) ⟩
      rename (↑ 1) “ ⟅ σ₃ ⟆ x ” ≡⟨ sym (quote-shift{V₃} (⟅ σ₃ ⟆ x)) ⟩
      “ ⇑ (⟅ σ₃ ⟆ x) ” ∎

  mmf-arg : ∀{σ₁ σ₂ σ₃ b} (arg : Arg b) → σ₂ ∘ σ₁ ≈ σ₃
     → map-arg σ₂ (map-arg σ₁ arg) ≡ map-arg σ₃ arg
  mmf-args : ∀{σ₁ σ₂ σ₃ bs} (args : Args bs) → σ₂ ∘ σ₁ ≈ σ₃
     → map-args σ₂ (map-args σ₁ args) ≡ map-args σ₃ args
  mmf-arg {b = zero} (ast M) σ₂∘σ₁≈σ₃ =
      cong ast (map-map-fusion M σ₂∘σ₁≈σ₃)
  mmf-arg {b = suc b} (bind arg) σ₂∘σ₁≈σ₃ =
      cong bind (mmf-arg arg (mm-fuse-ext σ₂∘σ₁≈σ₃))
  mmf-args {bs = []} nil σ₂∘σ₁≈σ₃ = refl
  mmf-args {bs = b ∷ bs} (cons arg args) σ₂∘σ₁≈σ₃ =
      cong₂ cons (mmf-arg arg σ₂∘σ₁≈σ₃) (mmf-args args σ₂∘σ₁≈σ₃)

