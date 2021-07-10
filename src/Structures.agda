{-# OPTIONS --without-K  #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality 
    using (_≡_; refl; sym; cong; cong₂; cong-app)
open import ScopedTuple
open import Sig
open import Var

module Structures where


{-

  A Shiftable thing of type V may contain variable occurences (de
  Bruijn indices) that need to be shifted up by one when they go
  underneath a variable binder. Thus, the operations on Shiftable
  things are:

  1. ⇑ v        to shift all the variables in v up by one.
  2. var→val x  to inject the variable x into a V.
  
  Also, we require that incrementing a variable x and then injecting it into
  V is equal to injecting it into V and then shifting the result.

  var→val (suc x) ≡ ⇑ (var→val x)

  Examples of Shiftable things:

     * Variables (shifting increments the variable, injecting is the identity)
     * Terms (shifting applies a renaming to the term, injecting wraps
              the variable in the term constructors for variables)
     * Maybe ℕ (shifting does nothing; variables get mapped to `nothing`)

-}
record Shiftable {ℓ} (V : Set ℓ) : Set ℓ where
  field ⇑ : V → V
        var→val : Var → V
        var→val-suc-shift : ∀{x} → var→val (suc x) ≡ ⇑ (var→val x)
open Shiftable {{...}} public

instance
  Var-is-Shiftable : Shiftable Var
  Var-is-Shiftable = record { var→val = λ x → x ; ⇑ = suc
                            ; var→val-suc-shift = λ {x} → refl }


record Composable {ℓ} (V₁ V₂ V₃ : Set ℓ){{_ : Shiftable V₁}} : Set ℓ where
   field ⌈_⌉ : (Var → V₂) → V₁ → V₃
         val₂₃ : V₂ → V₃
         ⌈⌉-var→val : ∀ σ x → ⌈ σ ⌉ (var→val x) ≡ val₂₃ (σ x)
open Composable {{...}} public

instance
    Var³-Composable : Composable Var Var Var
    Var³-Composable = record { ⌈_⌉ = λ f x → f x ; val₂₃ = λ x → x
                     ; ⌈⌉-var→val = λ σ x → refl }

infixr 5 _⨟_

_⨟_ : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ} {{_ : Shiftable V₁}} {{_ : Composable V₁ V₂ V₃}}
     → (Var → V₁) → (Var → V₂) → (Var → V₃)
(σ₁ ⨟ σ₂) x = ⌈ σ₂ ⌉ (σ₁ x)

record Equiv {ℓ} (V₁ : Set ℓ)(V₂ : Set ℓ) : Set (lsuc ℓ) where
  field _≈_ : V₁ → V₂ → Set ℓ
open Equiv {{...}} public

instance
  ≡-Var-is-Equiv : Equiv Var Var
  ≡-Var-is-Equiv = record { _≈_ = _≡_ }

record EquivRel {ℓ} (V : Set ℓ) {{_ : Equiv {ℓ} V V}} : Set ℓ where
  field ≈-refl : ∀ (v : V) → v ≈ v
        ≈-sym : ∀ {u v : V} → u ≈ v → v ≈ u
        ≈-trans : ∀ {u v w : V} → u ≈ v → v ≈ w → u ≈ w
open EquivRel {{...}} public

infixr 2 _≈⟨⟩_ _≈⟨_⟩_
infix  3 _≈∎

_≈⟨⟩_ : ∀ {ℓ}{A : Set ℓ} {{_ : Equiv{ℓ} A A}} {{_ : EquivRel A}}
    (x : A) {y : A} 
  → x ≡ y
    -----
  → x ≈ y
x ≈⟨⟩ refl  =  ≈-refl x

_≈⟨_⟩_ : ∀ {ℓ}{A : Set ℓ} {{_ : Equiv{ℓ} A A}} {{_ : EquivRel A}}
    (x : A) {y z : A}
  → x ≈ y  →  y ≈ z
    ---------------
  → x ≈ z
x ≈⟨ x≈y ⟩ y≈z  =  ≈-trans x≈y y≈z

_≈∎ : ∀ {ℓ}{A : Set ℓ} {{_ : Equiv{ℓ} A A}} {{_ : EquivRel A}}
    (x : A)
    -------
  → x ≈ x
x ≈∎  =  ≈-refl x

instance
  ≡-Var-is-EquivRel : EquivRel Var
  ≡-Var-is-EquivRel = record { ≈-refl = λ v → refl
      ; ≈-sym = λ { {u}{v} refl → refl }
      ; ≈-trans = λ { {u}{v}{w} refl refl → refl } }

record Relatable {ℓ} (V₁ : Set ℓ) (V₂ : Set ℓ)
    {{_ : Shiftable V₁}} {{_ : Shiftable V₂}} : Set (lsuc ℓ) where
    field {{eq}} : Equiv {ℓ} V₁ V₂
          var→val≈ : ∀ x → (var→val{V = V₁} x) ≈ (var→val{V = V₂} x)
          shift≈ : ∀{v₁ : V₁}{v₂ : V₂} → v₁ ≈ v₂ → (⇑ v₁) ≈ (⇑ v₂)
open Relatable {{...}} public

record ShiftId {ℓ} (V : Set ℓ) {{_ : Equiv{ℓ} V V}} {{S : Shiftable V}} 
    : Set ℓ where
    field shift-id : ∀ x → (var→val{V = V} x) ≈ (⇑ (var→val x))
open ShiftId {{...}} public

{-
Bind : {ℓᵛ ℓᶜ : Level} → Set ℓᵛ → Set ℓᶜ → Sig → Set (ℓᵛ ⊔ ℓᶜ)
Bind {ℓᵛ}{ℓᶜ} V C ■ = Lift ℓᵛ C
Bind V C (ν b) = V → Bind V C b
Bind V C (∁ b) = Bind V C b
-}
Bind : {ℓ : Level} → Set ℓ → Set ℓ → Sig → Set ℓ
Bind V C ■ = C
Bind V C (ν b) = V → Bind V C b
Bind V C (∁ b) = Bind V C b

{-
 Equivalence of Bind's based on equivalence of V's and C's.
 -}

_⩳_  : ∀ {ℓ} {V₁ V₂ : Set ℓ} {C₁ C₂ : Set ℓ}
     {{EqV : Equiv{ℓ} V₁ V₂}} {{EqC : Equiv{ℓ} C₁ C₂}}
   → (Bind V₁ C₁) ✖ (Bind V₂ C₂)
_⩳_ {ℓ}{b = ■} c₁ c₂ = c₁ ≈ c₂
_⩳_ {V₁ = V₁}{V₂}{C₁}{C₂}{{R}}{b = ν b} r₁ r₂ =
  ∀{v₁ : V₁}{v₂ : V₂} → v₁ ≈ v₂ → _⩳_ {b = b} (r₁ v₁) (r₂ v₂)
_⩳_ {b = ∁ b} r₁ r₂ = _⩳_ {b = b} r₁ r₂ 

module WithOpSig (Op : Set) (sig : Op → List Sig) where

  record Foldable {ℓ : Level}(V : Set ℓ)(C : Set ℓ) : Set ℓ
      where
    field ret : V → C
          fold-op : (op : Op) → Tuple {ℓ} (sig op) (Bind V C) → C
  open Foldable {{...}} public

  record Similar {ℓ} (V₁ : Set ℓ)(V₂ : Set ℓ)
    (C₁ : Set ℓ)(C₂ : Set ℓ)
    {{SV1 : Shiftable V₁}} {{SV2 : Shiftable V₂}}
    {{F1 : Foldable V₁ C₁}} {{F2 : Foldable V₂ C₂}}
    {{EqC : Equiv{ℓ} C₁ C₂}}
        : Set (lsuc ℓ) where
    field {{rel}} : Relatable V₁ V₂
    field ret≈ : ∀{v₁ : V₁}{v₂ : V₂} → v₁ ≈ v₂ → (Foldable.ret F1 v₁) ≈ (ret v₂)
    field op⩳ : ∀{op}{rs₁ : Tuple (sig op) (Bind V₁ C₁)}
                     {rs₂ : Tuple (sig op) (Bind V₂ C₂)}
              → zip (λ {b} → _⩳_{V₁ = V₁}{V₂}{C₁}{C₂}{b}) {bs = sig op} rs₁ rs₂
              → fold-op op rs₁ ≈ fold-op op rs₂
  open Similar {{...}} public

  record SyntacticFold {ℓ : Level}(V : Set ℓ)(C : Set ℓ)
    : Set (lsuc ℓ) where
    field {{V-shiftable}} : Shiftable V
          {{foldable}} : Foldable V C
          fvᵛ : V → Var → Set
          fvᶜ : C → Var → Set
          fv-ret : ∀ (v : V) → fvᶜ (ret v) ≡ fvᵛ v
          fv-var→val : ∀ (x y : Var) → fvᵛ (var→val x) y ≡ (x ≡ y)
          fv-shift : ∀ (v : V) (y : Var) → fvᵛ (⇑ v) (suc y) → fvᵛ v y          
  open SyntacticFold {{...}} public

{------------------------------------------------------------------------------}

postulate
  extensionality : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁ }{B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

