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
open import Data.Unit.Polymorphic using (⊤; tt)
open import Environment
open import Function using (_∘_)
import Substitution
open import GenericSubstitution
open import ScopedTuple using (Tuple; zip)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var

module FoldMapFusion (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Substitution
open Substitution.ABTOps Op sig
open import Map Op sig using (map; map-arg; map-args)
open import MapFusion Op sig using (QuoteShift; ABT-is-QuoteShift)
open import Fold Op sig
open Shiftable {{...}}
open Env {{...}}
open Quotable {{...}}
open Foldable {{...}}
open QuoteShift {{...}}

_⨟_≈_ : ∀{ℓᶠ ℓᵐ} {Vᵐ Eᵐ : Set ℓᵐ}{Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
    {{_ : Shiftable Vᵐ}} {{_ : Env Eᵐ Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Env Eᶠ Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    → Eᵐ → Eᶠ → Eᶠ → Set ℓᶠ
σ ⨟ δ ≈ γ = ∀ x → fold δ (“ ⟅ σ ⟆ x ”) ≡ ret (⟅ γ ⟆ x)

module RelFold≡ where
  ≡-RelFold : ∀{ℓ}{V : Set ℓ}{C : Set ℓ} → RelFold V V C C
  ≡-RelFold {ℓ} = record { _∼_ = _≡_ ; _≈_ = _≡_ }

module _ where
  open RelFold≡
  instance _ : ∀{ℓ}{V C : Set ℓ} → RelFold V V C C ; _ = ≡-RelFold

  fold-map-fusion-ext : ∀{ℓᵐ ℓᶠ}{Vᵐ Eᵐ : Set ℓᵐ}{ Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
       {{_ : Shiftable Vᵐ}} {{_ : Env Eᵐ Vᵐ}} {{_ : Quotable Vᵐ}}
       {{_ : Shiftable Vᶠ}} {{_ : Env Eᶠ Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
       {σ : Eᵐ}{δ γ : Eᶠ}
       (M : ABT)
     → σ ⨟ δ ≈ γ
     → (∀{σ : Eᵐ}{δ γ : Eᶠ}{v : Vᶠ} → σ ⨟ δ ≈ γ → ext σ ⨟ (δ , v) ≈ (γ , v))
     → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
           → zip (_⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}) rs rs′
           → fold-op op rs ≡ fold-op op rs′)
     → fold δ (map σ M)  ≡ fold γ M
  fold-map-fusion-ext (` x) σ⨟δ≈γ env-ext op-cong = σ⨟δ≈γ x
  fold-map-fusion-ext {Vᵐ = Vᵐ}{Eᵐ}{Vᶠ}{Cᶠ}{Eᶠ}{σ = σ}{δ}{γ} (op ⦅ args ⦆) σ⨟δ≈γ
      env-ext op-cong = op-cong (fuse-args args σ⨟δ≈γ)
      where
      fuse-arg : ∀{b}{σ : Eᵐ}{δ γ : Eᶠ} (arg : Arg b)
         → σ ⨟ δ ≈ γ
         → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ} (fold-arg δ (map-arg σ arg))
                                    (fold-arg γ arg)
      fuse-args : ∀{bs}{σ : Eᵐ}{δ γ : Eᶠ} (args : Args bs)
         → σ ⨟ δ ≈ γ
         → zip (_⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}) (fold-args δ (map-args σ args))
               (fold-args γ args)
      fuse-arg {zero} {σ} {δ} {γ} (ast M) σ⨟δ≈γ =
          fold-map-fusion-ext M σ⨟δ≈γ env-ext op-cong
      fuse-arg {suc b} {σ} {δ} {γ} (bind arg) σ⨟δ≈γ refl =
          fuse-arg {b} arg (env-ext σ⨟δ≈γ)
      fuse-args {[]} {σ} {δ} {γ} nil σ⨟δ≈γ = tt
      fuse-args {b ∷ bs} {σ} {δ} {γ} (cons arg args) σ⨟δ≈γ =
          ⟨ fuse-arg{b}{σ}{δ}{γ} arg σ⨟δ≈γ , fuse-args args σ⨟δ≈γ ⟩

  fold-rename-fusion : ∀ {ℓ : Level}{Vᶠ Eᶠ Cᶠ : Set ℓ}
       {{_ : Shiftable Vᶠ}} {{_ : Env Eᶠ Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
       {{_ : Shiftable Cᶠ}}
       {ρ : Rename}{δ γ : Eᶠ}
       (M : ABT)
     → ρ ⨟ δ ≈ γ
     → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
           → zip (_⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}) rs rs′
           → fold-op op rs ≡ fold-op op rs′)
     → (∀ (v : Vᶠ) → ⇑ (ret v) ≡ ret (⇑ v))
     → fold δ (rename ρ M)  ≡ fold γ M
  fold-rename-fusion {ℓ}{Vᶠ}{Eᶠ} M ρ⨟δ≈γ op-cong shift-ret =
    fold-map-fusion-ext M ρ⨟δ≈γ ext-env op-cong
    where
    ext-env : ∀{ρ : Rename}{σ₁ σ₂ : Eᶠ}{v : Vᶠ} → ρ ⨟ σ₁ ≈ σ₂
       → ext ρ ⨟ (σ₁ , v) ≈ (σ₂ , v)
    ext-env {ρ} {σ₁} {σ₂} {v} prem zero rewrite lookup-0 σ₁ v | lookup-0 σ₂ v =
        refl
    ext-env {ρ} {σ₁} {σ₂} {v} prem (suc x) rewrite lookup-suc σ₂ v x
        | inc-shift ρ x | lookup-suc σ₁ v (⟅ ρ ⟆ x) =
        begin
            ret (⇑ (⟅ σ₁ ⟆ (⟅ ρ ⟆ x)))
        ≡⟨ sym (shift-ret _) ⟩
            ⇑ (ret (⟅ σ₁ ⟆ (⟅ ρ ⟆ x)))
        ≡⟨ cong ⇑ (prem x) ⟩
            ⇑ (ret (⟅ σ₂ ⟆ x))
        ≡⟨ shift-ret _ ⟩
            ret (⇑ (⟅ σ₂ ⟆ x))
        ∎

module _ where
  private
   instance
     ≡⇑-RelFold : ∀{ℓ}{V : Set ℓ}{C : Set ℓ}
        {{_ : Shiftable V}} {{_ : Shiftable C}}
        → RelFold {ℓ}{ℓ} V V C C
     ≡⇑-RelFold {ℓ} = record { _∼_ = (λ v v' → v ≡ ⇑ v')
                             ; _≈_ = (λ c c' → c ≡ ⇑ c') }

  record FoldShift {ℓ} (V : Set ℓ) (C : Set ℓ)
    {{_ : Shiftable V}} {{_ : Shiftable C}} {{_ : Foldable V C}}
    : Set ℓ
    where
    field shift-ret : ∀ (v : V) → ⇑ (ret v) ≡ ret (⇑ v)
          op-shift : ∀ {op} {rs↑ rs : Tuple (sig op) (Bind V C)}
            → zip (_⩳_{ℓ}{ℓ}{V}{V}{C}{C}) rs↑ rs
            → fold-op op rs↑ ≡ ⇑ (fold-op op rs)
  open FoldShift {{...}}
  

  instance
    _ : ∀{ℓ}{V : Set ℓ}{C : Set ℓ} {{_ : Shiftable V}} {{_ : Shiftable C}}
        {{_ : Foldable V C}} {{_ : FoldShift V C}}
      → Similar V V C C
    _ = record { ret≈ = λ { {_}{v} refl → sym (shift-ret v) }
               ; shift∼ = λ { refl → refl } ; op⩳ = op-shift }
   
  fold-shift : ∀ {ℓ : Level}{Vᶠ Eᶠ Cᶠ : Set ℓ}
     {{_ : Shiftable Vᶠ}} {{_ : Env Eᶠ Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
     {{_ : Shiftable Cᶠ}} {{_ : FoldShift Vᶠ Cᶠ}}
     (δ δ↑ : Eᶠ)
     (M : ABT)
     → (∀ x → ⟅ δ↑ ⟆ x ≡ ⇑ (⟅ δ ⟆ x))
     → fold δ↑ M ≡ ⇑ (fold δ M)
  fold-shift δ δ↑ M δ=shift = sim M δ=shift
  

open RelFold≡
instance _ : ∀{ℓ}{V C : Set ℓ} → RelFold V V C C ; _ = ≡-RelFold
open FoldShift {{...}}
  
fold-map-fusion : ∀{ℓᵐ ℓᶠ}{Vᵐ Eᵐ : Set ℓᵐ}{ Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
     {{_ : Shiftable Vᵐ}} {{_ : Env Eᵐ Vᵐ}} {{_ : Quotable Vᵐ}}
     {{_ : Shiftable Vᶠ}} {{_ : Env Eᶠ Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
     {{_ : Shiftable Cᶠ}}
     {{_ : FoldShift Vᶠ Cᶠ}}{{_ : QuoteShift Vᵐ}}
     {σ : Eᵐ}{δ γ : Eᶠ}
     (M : ABT)
   → σ ⨟ δ ≈ γ
   → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
         → zip (_⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}) rs rs′
         → fold-op op rs ≡ fold-op op rs′)
   → fold δ (map σ M)  ≡  fold γ M
fold-map-fusion {ℓᵐ}{ℓᶠ}{Vᵐ}{Eᵐ}{Vᶠ}{Cᶠ}{Eᶠ} M σ⨟δ≈γ op-cong =
  fold-map-fusion-ext M σ⨟δ≈γ ext-pres op-cong
  where
  ext-pres : ∀{σ : Eᵐ}{δ γ : Eᶠ}{v : Vᶠ} → σ ⨟ δ ≈ γ
                → (ext σ) ⨟ (δ , v) ≈ (γ , v)
  ext-pres {σ}{δ}{γ}{v} σ⨟δ≈γ zero rewrite lookup-0 γ v | lookup-0 σ (var→val 0)
      | quote-var→val{ℓᵐ}{Vᵐ} 0 | lookup-0 δ v = refl
  ext-pres {σ}{δ}{γ}{v} σ⨟δ≈γ (suc x) rewrite lookup-suc γ v x
      | lookup-suc σ (var→val 0) x
      | lookup-shift σ x | quote-shift (⟅ σ ⟆ x) =
      begin
          fold (δ , v) (rename (↑ 1) “ ⟅ σ ⟆ x ”)
      ≡⟨ fold-rename-fusion “ ⟅ σ ⟆ x ” G op-cong shift-ret ⟩
          fold (⟰ δ) “ ⟅ σ ⟆ x ”
      ≡⟨ fold-shift δ (⟰ δ) “ ⟅ σ ⟆ x ” (lookup-shift δ) ⟩
          ⇑ (fold δ “ ⟅ σ ⟆ x ”)
      ≡⟨ cong ⇑ (σ⨟δ≈γ x) ⟩
          ⇑ (ret (⟅ γ ⟆ x))
      ≡⟨ shift-ret _ ⟩
          ret (⇑ (⟅ γ ⟆ x))
      ∎
      where
      G : _⨟_≈_{ℓᶠ}{lzero}{Var}{Rename}{Vᶠ}{Cᶠ}{Eᶠ} (↑ 1) (δ , v) (⟰ δ)
      G x rewrite lookup-shift δ x | lookup-suc δ v x = refl

fold-subst-fusion : ∀ {ℓ : Level}{Vᶠ Eᶠ Cᶠ : Set ℓ}
     {{_ : Shiftable Vᶠ}} {{_ : Env Eᶠ Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
     {{_ : Shiftable Cᶠ}} {{_ : FoldShift Vᶠ Cᶠ}}
     {σ : Subst}{δ γ : Eᶠ}
     (M : ABT)
   → σ ⨟ δ ≈ γ
   → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
         → zip (_⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}) rs rs′
         → fold-op op rs ≡ fold-op op rs′)
   → fold δ (⟪ σ ⟫ M)  ≡ fold γ M
fold-subst-fusion {ℓ}{Vᶠ}{Eᶠ} M σ⨟δ≈γ op-cong =
  fold-map-fusion M σ⨟δ≈γ op-cong

