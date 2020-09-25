{-# OPTIONS --without-K #-}
{-
     Fusion of fold and map:

     fold-map-fusion : fold δ (map σ M)  ≡  fold γ M

     and some specializations:

     fold-rename-fusion : fold δ (rename ρ M)  ≡ fold γ M

     fold-subst-fusion : fold δ (⟪ σ ⟫ M)  ≡ fold γ M

-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (_∘_)
import Substitution
open import GSubst
open import GenericSubstitution
open import Level using (levelOfType)
open import ScopedTuple using (Tuple; zip)
open import Structures
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Sig
open import Var

module FoldMapFusion (Op : Set) (sig : Op → List Sig) where

open import AbstractBindingTree Op sig
open import Substitution
open Substitution.ABTOps Op sig
open import Map Op sig using (map; map-arg; map-args)
open import MapFusion Op sig {- using (QuoteShift; ABT-is-QuoteShift) -}
open import Fold Op sig
open Structures.WithOpSig Op sig

private
  variable
    ℓ : Level
    Vᵐ Vᶠ Cᶠ A V C : Set ℓ

_⨟_⩰_ : {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    {{_ : Equiv Cᶠ Cᶠ}}
    → GSubst Vᵐ → GSubst Vᶠ → GSubst Vᶠ → Set (levelOfType Cᶠ)
σ ⨟ δ ⩰ γ = ∀ x → fold δ (“ σ x ”) ≈ ret (γ x)

_⊢_⨟_≈_ : {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    {{_ : Equiv Cᶠ Cᶠ}}
    → ABT → GSubst Vᵐ → GSubst Vᶠ → GSubst Vᶠ → Set (levelOfType Cᶠ)
M ⊢ σ ⨟ δ ≈ γ = ∀ x → FV M x → fold δ (“ σ x ”) ≈ ret (γ x)

_⊢ₐ_⨟_≈_ : {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    {{_ : Equiv Cᶠ Cᶠ}}
   → {b : Sig} → Arg b → GSubst Vᵐ → GSubst Vᶠ → GSubst Vᶠ
   → Set (levelOfType Cᶠ)
arg ⊢ₐ σ ⨟ δ ≈ γ = ∀ x → FV-arg arg x → fold δ (“ σ x ”) ≈ ret (γ x)

_⊢₊_⨟_≈_ : {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    {{_ : Equiv Cᶠ Cᶠ}}
    → {bs : List Sig} → Args bs → GSubst Vᵐ → GSubst Vᶠ → GSubst Vᶠ
    → Set (levelOfType Cᶠ)
args ⊢₊ σ ⨟ δ ≈ γ = ∀ x → FV-args args x → fold δ (“ σ x ”) ≈ ret (γ x)

module _ where

  fold-map-fusion-ext : {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
       {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
        {{_ : Equiv Cᶠ Cᶠ}} {{_ : Similar Vᶠ Vᶠ Cᶠ Cᶠ}}
       {σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}
       (M : ABT)
     → σ ⨟ δ ⩰ γ
     → (∀{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}{v₁ v₂ : Vᶠ}
         → v₁ ≈ v₂ → σ ⨟ δ ⩰ γ → ext σ ⨟ (δ , v₁) ⩰ (γ , v₂))
     → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
           → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
           → fold-op op rs ≈ fold-op op rs′)
     → fold δ (map σ M) ≈ fold γ M
  fold-map-fusion-ext (` x) σ⨟δ≈γ env-ext op-cong = σ⨟δ≈γ x
  fold-map-fusion-ext {Vᵐ = Vᵐ}{Vᶠ = Vᶠ}{Cᶠ = Cᶠ}{σ = σ}{δ}{γ} (op ⦅ args ⦆)
      σ⨟δ≈γ env-ext op-cong = op-cong (fuse-args {sig op} args σ⨟δ≈γ)
      where
      fuse-arg : ∀{b}{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ} (arg : Arg b)
         → σ ⨟ δ ⩰ γ
         → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b} (fold-arg δ (map-arg σ arg))
                                    (fold-arg γ arg)
                                    
      fuse-args : ∀{bs}{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ} (args : Args bs)
         → σ ⨟ δ ⩰ γ
         → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b})
               (fold-args δ (map-args σ args)) (fold-args γ args)
      fuse-arg {b} {σ} {δ} {γ} (ast M) σ⨟δ≈γ =
          lift (fold-map-fusion-ext M σ⨟δ≈γ env-ext op-cong)
      fuse-arg {ν b} {σ} {δ} {γ} (bind arg) σ⨟δ≈γ {v₁} v₁≈v₂ =
          fuse-arg {b} arg (env-ext v₁≈v₂ σ⨟δ≈γ) 
      fuse-arg {∁ b} {σ} {δ} {γ} (clear arg) σ⨟δ≈γ =
          fold-arg-refl arg var→val≈ 
      fuse-args {[]} {σ} {δ} {γ} nil σ⨟δ≈γ = tt
      fuse-args {b ∷ bs} {σ} {δ} {γ} (cons arg args) σ⨟δ≈γ =
          ⟨ fuse-arg{b}{σ}{δ}{γ} arg σ⨟δ≈γ , fuse-args {bs} args σ⨟δ≈γ ⟩

  fold-map-fusion-ext-FV : 
       {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
       {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
       {{_ : Equiv Cᶠ Cᶠ}} {{_ : Similar Vᶠ Vᶠ Cᶠ Cᶠ}}
       {σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}
       (M : ABT)
     → M ⊢ σ ⨟ δ ≈ γ
     → (∀{b}{arg : Arg b}{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}{v₁ v₂ : Vᶠ}
         → v₁ ≈ v₂
         → bind arg ⊢ₐ σ ⨟ δ ≈ γ
         → arg ⊢ₐ ext σ ⨟ (δ , v₁) ≈ (γ , v₂))
     → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
           → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
           → fold-op op rs ≈ fold-op op rs′)
     → fold δ (map σ M)  ≈ fold γ M
  fold-map-fusion-ext-FV (` x) σ⨟δ≈γ env-ext op-cong = σ⨟δ≈γ x refl
  fold-map-fusion-ext-FV {Vᵐ = Vᵐ}{Vᶠ = Vᶠ}{Cᶠ = Cᶠ}{σ = σ}{δ}{γ} (op ⦅ args ⦆)
      σ⨟δ≈γ env-ext op-cong = op-cong (fuse-args {sig op} args σ⨟δ≈γ)
      where
      fuse-arg : ∀{b}{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ} (arg : Arg b)
         → arg ⊢ₐ σ ⨟ δ ≈ γ
         → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b} (fold-arg δ (map-arg σ arg))
                                    (fold-arg γ arg)
      fuse-args : ∀{bs}{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ} (args : Args bs)
         → args ⊢₊ σ ⨟ δ ≈ γ
         → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b})
               (fold-args δ (map-args σ args)) (fold-args γ args)
      fuse-arg {b} {σ} {δ} {γ} (ast M) σ⨟δ≈γ =
          lift (fold-map-fusion-ext-FV M σ⨟δ≈γ
                     (λ{b}{arg} → env-ext{b}{arg}) op-cong)
      fuse-arg {ν b} {σ} {δ} {γ} (bind arg) σ⨟δ≈γ v₁≈v₂ =
         fuse-arg {b} arg (env-ext{b}{arg} v₁≈v₂ σ⨟δ≈γ)
      fuse-arg {∁ b} {σ} {δ} {γ} (clear arg) σ⨟δ≈γ = fold-arg-refl arg var→val≈
      fuse-args {[]} {σ} {δ} {γ} nil σ⨟δ≈γ = tt
      fuse-args {b ∷ bs} {σ} {δ} {γ} (cons arg args) σ⨟δ≈γ =
          ⟨ fuse-arg {b}{σ}{δ}{γ} arg G , fuse-args {bs} args H ⟩
          where
          G : arg ⊢ₐ σ ⨟ δ ≈ γ
          G x x∈arg = σ⨟δ≈γ x (inj₁ x∈arg)
          H : args ⊢₊ σ ⨟ δ ≈ γ
          H x x∈args = σ⨟δ≈γ x (inj₂ x∈args)

  fold-rename-fusion : 
       {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}} {{_ : Shiftable Cᶠ}}
       {{_ : Relatable Cᶠ Cᶠ}} {{_ : Similar Vᶠ Vᶠ Cᶠ Cᶠ}}
       {ρ : Rename}{δ γ : GSubst Vᶠ}
       (M : ABT)
     → ρ ⨟ δ ⩰ γ
     → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
           → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
           → fold-op op rs ≈ fold-op op rs′)
     → (∀ (v : Vᶠ) → ret (⇑ v) ≡ ⇑ (ret v))
     → fold δ (rename ρ M) ≈ fold γ M
  fold-rename-fusion {Vᶠ = Vᶠ}{Eᶠ} M ρ⨟δ≈γ op-cong shift-ret =
    fold-map-fusion-ext M ρ⨟δ≈γ ext-env op-cong
    where
    ext-env : ∀{ρ : Rename}{σ₁ σ₂ : GSubst Vᶠ}{v₁ v₂ : Vᶠ}
       → v₁ ≈ v₂ → ρ ⨟ σ₁ ⩰ σ₂
       → ext ρ ⨟ (σ₁ , v₁) ⩰ (σ₂ , v₂)
    ext-env {ρ} {σ₁} {σ₂} {v₁}{v₂} v₁≈v₂ prem zero = ret≈ v₁≈v₂
    ext-env {ρ} {σ₁} {σ₂} {v₁}{v₂} v₁≈v₂ prem (suc x) =
        G
        where
        G : ret (⇑ (σ₁ (ρ x))) ≈ ret (⇑ (σ₂ x))
        G rewrite shift-ret (σ₁ (ρ x)) | shift-ret (σ₂ x) = shift≈ (prem x)

≈⇑-Equiv : ∀{ℓ}{A : Set ℓ} {{_ : Equiv A A}} {{_ : Shiftable A}} 
            → Equiv {ℓ}{ℓ} A A
≈⇑-Equiv = record { _≈_ = (λ c c' → c ≈ (⇑ c')) }
  
≈⇑-Relatable : {{_ : Shiftable A}} {{_ : Relatable A A}} {{_ : ShiftId A}}
   → Relatable A A
≈⇑-Relatable = record { eq = ≈⇑-Equiv
                      ; var→val≈ = shift-id 
                      ; shift≈ = λ v₁≈⇑v₂ → shift≈ v₁≈⇑v₂ }
                      
record FoldShift {ℓᵛ ℓᶜ} (V : Set ℓᵛ) (C : Set ℓᶜ)
  {{_ : Equiv V V}} {{_ : Equiv C C}}
  {{_ : Shiftable V}} {{_ : Shiftable C}}
  {{_ : Foldable V C}} 
  : Set (ℓᵛ ⊔ ℓᶜ) where
  field shift-ret : ∀ (v : V) → ret (⇑ v) ≡ ⇑ (ret v)
        op-shift : ∀ {op} {rs↑ rs : Tuple (sig op) (Bind V C)}
          → zip (λ {b} → _⩳_ {{≈⇑-Equiv}}{{≈⇑-Equiv}} {b = b}) rs↑ rs
          → (fold-op op rs↑) ≈ (⇑ (fold-op op rs))
open FoldShift {{...}}
  
≈⇑-Similar : {{_ : Shiftable V}} {{_ : Shiftable C}} {{_ : Foldable V C}}
    {{_ : Equiv C C}} {{_ : Similar V V C C}}
    {{_ : ShiftId V}} {{_ : FoldShift V C}}
  → Similar V V C C {{EqC = ≈⇑-Equiv}}
≈⇑-Similar {V = V} =
    record { rel = ≈⇑-Relatable {A = V} ; ret≈ = return-≈ ; op⩳ = op-shift }
    where
    return-≈ : {v₁ v₂ : V} → v₁ ≈ ⇑ v₂ → (ret v₁) ≈ (⇑ (ret v₂))
    return-≈ {v₁}{v₂} v₁≈⇑v₂ rewrite sym (shift-ret v₂) = ret≈ v₁≈⇑v₂
    
fold-shift : {{_ : Shiftable Vᶠ}} {{_ : Shiftable Cᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
   {{_ : Equiv Cᶠ Cᶠ}} {{_ : Similar Vᶠ Vᶠ Cᶠ Cᶠ}}
   {{_ : ShiftId Vᶠ}} {{_ : FoldShift Vᶠ Cᶠ}}
   (δ δ↑ : GSubst Vᶠ)
   (M : ABT)
   → (∀ x → δ↑ x ≈ ⇑ (δ x))
   → fold δ↑ M ≈ ⇑ (fold δ M)
fold-shift {Vᶠ = Vᶠ}{Cᶠ = Cᶠ} δ δ↑ M δ=shift =
  let S = ≈⇑-Similar {V = Vᶠ}{C = Cᶠ} in
  sim {{EqV = ≈⇑-Equiv}} {{EqC = ≈⇑-Equiv}} {{Sim = S}} M δ=shift

fold-map-fusion : {{_ : Shiftable Vᵐ}} {{_ : Shiftable Vᶠ}} {{_ : Shiftable Cᶠ}}
     {{_ : Foldable Vᶠ Cᶠ}}
     {{_ : Relatable Cᶠ Cᶠ}} {{_ : EquivRel Cᶠ}}
     {{_ : Similar Vᶠ Vᶠ Cᶠ Cᶠ}} {{_ : EquivRel Vᶠ}}
     {{_ : FoldShift Vᶠ Cᶠ}} {{_ : QuoteShift Vᵐ}} {{_ : ShiftId Vᶠ}}
     {σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}
     (M : ABT)
   → σ ⨟ δ ⩰ γ
   → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
         → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
         → fold-op op rs ≈ fold-op op rs′)
   → fold δ (map σ M)  ≈  fold γ M
fold-map-fusion {Vᵐ = Vᵐ}{Vᶠ = Vᶠ}{Cᶠ = Cᶠ} M σ⨟δ≈γ op-cong =
  fold-map-fusion-ext M σ⨟δ≈γ ext-pres op-cong
  where
  ext-pres : ∀{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}{v₁ v₂ : Vᶠ}
      → v₁ ≈ v₂ → σ ⨟ δ ⩰ γ
      → (ext σ) ⨟ (δ , v₁) ⩰ (γ , v₂)
  ext-pres v₁≈v₂ σ⨟δ≈γ zero rewrite quote-var→val{V = Vᵐ} 0 =
      ret≈ v₁≈v₂
  ext-pres {σ}{δ}{γ}{v₁}{v₂} v₁≈v₂ σ⨟δ≈γ (suc x)
      rewrite quote-shift (σ x) | shift-ret (γ x) =
          fold {C = Cᶠ} (δ , v₁) (rename (↑ 1) “ σ x ”)
      ≈⟨ fold-rename-fusion “ σ x ” G op-cong shift-ret ⟩
          fold (⟰ δ) “ σ x ”
      ≈⟨ fold-shift δ (⟰ δ) “ σ x ” (λ x → shift≈ (≈-refl (δ x))) ⟩
          ⇑ (fold δ “ σ x ”)
      ≈⟨ shift≈ (σ⨟δ≈γ x) ⟩
          ⇑ (ret (γ x))
      ≈∎
      where
      G : _⨟_⩰_{Vᵐ = Var}{Vᶠ = Vᶠ}{Cᶠ = Cᶠ} (↑ 1) (δ , v₁) (⟰ δ)
      G x = ret≈ (≈-refl _)

fold-subst-fusion : {{_ : Shiftable Vᶠ}} {{_ : Shiftable Cᶠ}}
     {{_ : Foldable Vᶠ Cᶠ}}
     {{_ : Relatable Cᶠ Cᶠ}} {{_ : EquivRel Cᶠ}}
     {{_ : Similar Vᶠ Vᶠ Cᶠ Cᶠ}} {{_ : EquivRel Vᶠ}}
     {{_ : FoldShift Vᶠ Cᶠ}} {{_ : ShiftId Vᶠ}}
     {σ : Subst}{δ γ : GSubst Vᶠ}
     (M : ABT)
   → σ ⨟ δ ⩰ γ
   → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
         → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
         → fold-op op rs ≈ fold-op op rs′)
   → fold δ (⟪ σ ⟫ M)  ≈ fold γ M
fold-subst-fusion M σ⨟δ≈γ op-cong = fold-map-fusion M σ⨟δ≈γ op-cong
