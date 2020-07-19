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

_⨟_⩰_ : ∀{ℓᶠ ℓᵐ} {Vᵐ : Set ℓᵐ}{Vᶠ Cᶠ : Set ℓᶠ}
    {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    → GSubst Vᵐ → GSubst Vᶠ → GSubst Vᶠ → Set ℓᶠ
σ ⨟ δ ⩰ γ = ∀ x → fold δ (“ σ x ”) ≡ ret (γ x)

_⊢_⨟_≈_ : ∀{ℓᶠ ℓᵐ} {Vᵐ : Set ℓᵐ}{Vᶠ Cᶠ : Set ℓᶠ}
    {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    → ABT → GSubst Vᵐ → GSubst Vᶠ → GSubst Vᶠ → Set ℓᶠ
M ⊢ σ ⨟ δ ≈ γ = ∀ x → FV M x → fold δ (“ σ x ”) ≡ ret (γ x)

_⊢ₐ_⨟_≈_ : ∀{ℓᶠ ℓᵐ} {Vᵐ : Set ℓᵐ}{Vᶠ Cᶠ : Set ℓᶠ}
    {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    → {b : Sig} → Arg b → GSubst Vᵐ → GSubst Vᶠ → GSubst Vᶠ → Set ℓᶠ
arg ⊢ₐ σ ⨟ δ ≈ γ = ∀ x → FV-arg arg x → fold δ (“ σ x ”) ≡ ret (γ x)

_⊢₊_⨟_≈_ : ∀{ℓᶠ ℓᵐ} {Vᵐ : Set ℓᵐ}{Vᶠ Cᶠ : Set ℓᶠ}
    {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    → {bs : List Sig} → Args bs → GSubst Vᵐ → GSubst Vᶠ → GSubst Vᶠ → Set ℓᶠ
args ⊢₊ σ ⨟ δ ≈ γ = ∀ x → FV-args args x → fold δ (“ σ x ”) ≡ ret (γ x)


module Equiv≡ where
  ≡-Equiv : ∀{ℓ}{C : Set ℓ} → Equiv C C
  ≡-Equiv {ℓ} = record { _≈_ = _≡_ }

module _ where
  open Equiv≡
  instance _ : ∀{ℓ}{V : Set ℓ} → Equiv V V ; _ = ≡-Equiv

  ⩳-refl : ∀ {b}{ℓ}{V : Set ℓ}{C : Set ℓ}{v : Bind V C b}
     → _⩳_{V₁ = V}{V}{C}{C}{b = b} v  v
  ⩳-refl {■} {v} = refl
  ⩳-refl {ν b} {v} refl = ⩳-refl {b}
  ⩳-refl {∁ b} {v} = ⩳-refl {b}

  fold-map-fusion-ext : ∀{ℓᵐ ℓᶠ}{Vᵐ : Set ℓᵐ}{ Vᶠ Cᶠ : Set ℓᶠ}
       {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
       {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
       {σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}
       (M : ABT)
     → σ ⨟ δ ⩰ γ
     → (∀{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}{v : Vᶠ}
         → σ ⨟ δ ⩰ γ → ext σ ⨟ (δ , v) ⩰ (γ , v))
     → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
           → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
           → fold-op op rs ≡ fold-op op rs′)
     → fold δ (map σ M)  ≡ fold γ M
  fold-map-fusion-ext (` x) σ⨟δ≈γ env-ext op-cong = σ⨟δ≈γ x
  fold-map-fusion-ext {Vᵐ = Vᵐ}{Vᶠ}{Cᶠ}{σ = σ}{δ}{γ} (op ⦅ args ⦆) σ⨟δ≈γ
      env-ext op-cong = op-cong (fuse-args {sig op} args σ⨟δ≈γ)
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
          fold-map-fusion-ext M σ⨟δ≈γ env-ext op-cong
      fuse-arg {ν b} {σ} {δ} {γ} (bind arg) σ⨟δ≈γ refl =
          fuse-arg {b} arg (env-ext σ⨟δ≈γ)
      fuse-arg {∁ b} {σ} {δ} {γ} (clear arg) σ⨟δ≈γ = ⩳-refl {b}
      fuse-args {[]} {σ} {δ} {γ} nil σ⨟δ≈γ = tt
      fuse-args {b ∷ bs} {σ} {δ} {γ} (cons arg args) σ⨟δ≈γ =
          ⟨ fuse-arg{b}{σ}{δ}{γ} arg σ⨟δ≈γ , fuse-args {bs} args σ⨟δ≈γ ⟩

  fold-map-fusion-ext-FV : ∀{ℓᵐ ℓᶠ}{Vᵐ : Set ℓᵐ}{ Vᶠ Cᶠ : Set ℓᶠ}
       {{_ : Shiftable Vᵐ}} {{_ : Quotable Vᵐ}}
       {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
       {σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}
       (M : ABT)
     → M ⊢ σ ⨟ δ ≈ γ
     → (∀{b}{arg : Arg b}{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}{v : Vᶠ}
         → bind arg ⊢ₐ σ ⨟ δ ≈ γ
         → arg ⊢ₐ ext σ ⨟ (δ , v) ≈ (γ , v))
     → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
           → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
           → fold-op op rs ≡ fold-op op rs′)
     → fold δ (map σ M)  ≡ fold γ M
  fold-map-fusion-ext-FV (` x) σ⨟δ≈γ env-ext op-cong = σ⨟δ≈γ x refl
  fold-map-fusion-ext-FV {Vᵐ = Vᵐ}{Vᶠ}{Cᶠ}{σ = σ}{δ}{γ} (op ⦅ args ⦆)
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
          fold-map-fusion-ext-FV M σ⨟δ≈γ (λ{b}{arg} → env-ext{b}{arg}) op-cong
      fuse-arg {ν b} {σ} {δ} {γ} (bind arg) σ⨟δ≈γ refl =
          fuse-arg {b} arg (env-ext{b}{arg} σ⨟δ≈γ)
      fuse-arg {∁ b} {σ} {δ} {γ} (clear arg) σ⨟δ≈γ = ⩳-refl {b}
      fuse-args {[]} {σ} {δ} {γ} nil σ⨟δ≈γ = tt
      fuse-args {b ∷ bs} {σ} {δ} {γ} (cons arg args) σ⨟δ≈γ =
          ⟨ fuse-arg {b}{σ}{δ}{γ} arg G , fuse-args {bs} args H ⟩
          where
          G : arg ⊢ₐ σ ⨟ δ ≈ γ
          G x x∈arg = σ⨟δ≈γ x (inj₁ x∈arg)
          H : args ⊢₊ σ ⨟ δ ≈ γ
          H x x∈args = σ⨟δ≈γ x (inj₂ x∈args)

  fold-rename-fusion : ∀ {ℓ : Level}{Vᶠ Cᶠ : Set ℓ}
       {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}} {{_ : Shiftable Cᶠ}}
       {ρ : Rename}{δ γ : GSubst Vᶠ}
       (M : ABT)
     → ρ ⨟ δ ⩰ γ
     → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
           → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
           → fold-op op rs ≡ fold-op op rs′)
     → (∀ (v : Vᶠ) → ⇑ (ret v) ≡ ret (⇑ v))
     → fold δ (rename ρ M)  ≡ fold γ M
  fold-rename-fusion {ℓ}{Vᶠ}{Eᶠ} M ρ⨟δ≈γ op-cong shift-ret =
    fold-map-fusion-ext M ρ⨟δ≈γ ext-env op-cong
    where
    ext-env : ∀{ρ : Rename}{σ₁ σ₂ : GSubst Vᶠ}{v : Vᶠ} → ρ ⨟ σ₁ ⩰ σ₂
       → ext ρ ⨟ (σ₁ , v) ⩰ (σ₂ , v)
    ext-env {ρ} {σ₁} {σ₂} {v} prem zero = refl
    ext-env {ρ} {σ₁} {σ₂} {v} prem (suc x) =
        begin
            ret (⇑ (σ₁ (ρ x)))
        ≡⟨ sym (shift-ret _) ⟩
            ⇑ (ret (σ₁ (ρ x)))
        ≡⟨ cong ⇑ (prem x) ⟩
            ⇑ (ret (σ₂ x))
        ≡⟨ shift-ret _ ⟩
            ret (⇑ (σ₂ x))
        ∎

module _ where
  private
   instance
     ≡⇑-Equiv : ∀{ℓ}{C : Set ℓ} {{_ : Shiftable C}}
              → Equiv {ℓ}{ℓ} C C
     ≡⇑-Equiv {ℓ} = record { _≈_ = (λ c c' → c ≡ ⇑ c') }

  record FoldShift {ℓ} (V : Set ℓ) (C : Set ℓ)
    {{_ : Shiftable V}} {{_ : Foldable V C}}
    : Set ℓ
    where
    field {{C-is-Shiftable}} : Shiftable C
    field shift-ret : ∀ (v : V) → ⇑ (ret v) ≡ ret (⇑ v)
          op-shift : ∀ {op} {rs↑ rs : Tuple (sig op) (Bind V C)}
            → zip (λ {b} → _⩳_{ℓ}{ℓ}{V}{V}{C}{C}{b}) rs↑ rs
            → fold-op op rs↑ ≡ ⇑ (fold-op op rs)
  open FoldShift {{...}}
  

  instance
    ≡⇑-Relatable : ∀{ℓ}{V : Set ℓ} {{_ : Shiftable V}} {{_ : ShiftId V}}
      → Relatable V V
    ≡⇑-Relatable = record { eq = ≡⇑-Equiv
                   ; var→val≈ = λ x → sym (shift-id x)
                   ; shift≈ = λ { refl → refl } }
    
    ≡⇑-Similar : ∀{ℓ}{V : Set ℓ}{C : Set ℓ} {{_ : Shiftable V}}
        {{_ : Foldable V C}} {{_ : FoldShift V C}} {{_ : ShiftId V}}
      → Similar V V C C
    ≡⇑-Similar {C = C} = record { ret≈ = λ { {_}{v} refl → sym (shift-ret v) }
                         {-; shift≈ = λ { refl → refl } -} ; op⩳ = op-shift } 
   
  fold-shift : ∀ {ℓ : Level}{Vᶠ Cᶠ : Set ℓ}
     {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
     {{_ : FoldShift Vᶠ Cᶠ}} {{_ : ShiftId Vᶠ}}
     (δ δ↑ : GSubst Vᶠ)
     (M : ABT)
     → (∀ x → δ↑ x ≡ ⇑ (δ x))
     → fold δ↑ M ≡ ⇑ (fold δ M)
  fold-shift δ δ↑ M δ=shift = sim M δ=shift
  

open Equiv≡
instance _ : ∀{ℓ}{V : Set ℓ} → Equiv V V ; _ = ≡-Equiv
open FoldShift {{...}} public
  
fold-map-fusion : ∀{ℓᵐ ℓᶠ}{Vᵐ : Set ℓᵐ}{Vᶠ Cᶠ : Set ℓᶠ}
     {{_ : Shiftable Vᵐ}} {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
     {{_ : FoldShift Vᶠ Cᶠ}} {{_ : QuoteShift Vᵐ}} {{_ : ShiftId Vᶠ}}
     {σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}
     (M : ABT)
   → σ ⨟ δ ⩰ γ
   → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
         → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
         → fold-op op rs ≡ fold-op op rs′)
   → fold δ (map σ M)  ≡  fold γ M
fold-map-fusion {ℓᵐ}{ℓᶠ}{Vᵐ}{Vᶠ}{Cᶠ} M σ⨟δ≈γ op-cong =
  fold-map-fusion-ext M σ⨟δ≈γ ext-pres op-cong
  where
  ext-pres : ∀{σ : GSubst Vᵐ}{δ γ : GSubst Vᶠ}{v : Vᶠ} → σ ⨟ δ ⩰ γ
                → (ext σ) ⨟ (δ , v) ⩰ (γ , v)
  ext-pres {σ}{δ}{γ}{v} σ⨟δ≈γ zero rewrite quote-var→val{V = Vᵐ} 0 = refl
  ext-pres {σ}{δ}{γ}{v} σ⨟δ≈γ (suc x) rewrite quote-shift (σ x) =
      begin
          fold (δ , v) (rename (↑ 1) “ σ x ”)
      ≡⟨ fold-rename-fusion “ σ x ” G op-cong shift-ret ⟩
          fold (⟰ δ) “ σ x ”
      ≡⟨ fold-shift δ (⟰ δ) “ σ x ” (λ _ → refl) ⟩
          ⇑ (fold δ “ σ x ”)
      ≡⟨ cong ⇑ (σ⨟δ≈γ x) ⟩
          ⇑ (ret (γ x))
      ≡⟨ shift-ret _ ⟩
          ret (⇑ (γ x))
      ∎
      where
      G : _⨟_⩰_{ℓᶠ}{lzero}{Var}{Vᶠ}{Cᶠ} (↑ 1) (δ , v) (⟰ δ)
      G x = refl

fold-subst-fusion : ∀ {ℓ : Level}{Vᶠ Cᶠ : Set ℓ} 
     {{_ : Shiftable Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}} {{_ : FoldShift Vᶠ Cᶠ}}
     {{_ : ShiftId Vᶠ}}
     {σ : Subst}{δ γ : GSubst Vᶠ}
     (M : ABT)
   → σ ⨟ δ ⩰ γ
   → (∀{op}{rs rs′ : Tuple (sig op) (Bind Vᶠ Cᶠ)}
         → zip (λ {b} → _⩳_{V₁ = Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}{b}) rs rs′
         → fold-op op rs ≡ fold-op op rs′)
   → fold δ (⟪ σ ⟫ M)  ≡ fold γ M
fold-subst-fusion {ℓ}{Vᶠ}{Eᶠ} M σ⨟δ≈γ op-cong =
  fold-map-fusion M σ⨟δ≈γ op-cong

