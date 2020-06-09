{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Size using (Size)
open import Var
open import experimental.ScopedTuple using (map; map-cong; map-compose)
open import Syntax hiding (⦉_⦊; ext; _⨟ᵣ_)

module experimental.Map (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig

{-------------------------------------------------------------------------------
 Mapping a substitution over an abstract binding tree
 (generalizes renaming and substitution)
 ------------------------------------------------------------------------------}

record Map (V : Set) : Set where
  field S : Substable V
        “_” : V → ABT
  open Substable S public
  module GS = GenericSubst S ; open GS

  map-abt : ∀{s : Size} → Substitution V → Term s → ABT
  map-arg : ∀{s : Size} → Substitution V → (b : ℕ) →  Term s → ABT
  
  map-abt σ (` x) = “ ⧼ σ ⧽ x ”
  map-abt σ (op ⦅ args ⦆) = op ⦅ map (λ {b} → map-arg σ b) args ⦆
  map-arg σ zero M = map-abt σ M
  map-arg σ (suc b) M = map-arg (g-ext σ) b M

{-------------------------------------------------------------------------------
  Fusion of two maps

  fusion : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} (M : Term s)
     → map₂ σ₂ (map₁ σ₁ M) ≡ map₂ (σ₁ ⨟ σ₂) M
 ------------------------------------------------------------------------------}

module ComposeMaps {V₁ V₂ : Set} (M₁ : Map V₁) (M₂ : Map V₂)
   (⌈_⌉ : Substitution V₂ → V₁ → V₂) where
  open GenericSubst (Map.S M₂) using (g-drop)
  {- The following generalizes _⨟ᵣ_ and _⨟_ -}
  infixr 5 _⨟_
  _⨟_ : Substitution V₁ → Substitution V₂ → Substitution V₂
  ↑ k ⨟ σ₂ = g-drop k σ₂
  (v₁ • σ₁) ⨟ σ₂ = ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)


record FusableMap {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂) : Set where
  open Map M₁ using () renaming (map-abt to map₁; map-arg to map-arg₁;
      “_” to “_”₁) public
  open Map.GS M₁ using () renaming (⧼_⧽ to ⧼_⧽₁; g-ext to ext₁) public
  open Map M₂ using () renaming (map-abt to map₂; map-arg to map-arg₂;
      “_” to “_”₂) public
  open Map.GS M₂ using () renaming (⧼_⧽ to ⧼_⧽₂; g-ext to ext₂) public
  
  field ⌈_⌉ : Substitution V₂ → V₁ → V₂
  open ComposeMaps M₁ M₂ ⌈_⌉ public
  field var : ∀ x σ₁ σ₂ → ⌈ σ₂ ⌉ (⧼ σ₁ ⧽₁ x) ≡ ⧼ σ₁ ⨟ σ₂ ⧽₂ x
  field map-quote : ∀ v₁ σ₂ → map₂ σ₂ “ v₁ ”₁ ≡ “ ⌈ σ₂ ⌉ v₁ ”₂
  field compose-ext : ∀ (σ₁ : Substitution V₁) (σ₂ : Substitution V₂)
                    → ext₁ σ₁ ⨟ ext₂ σ₂ ≡ ext₂ (σ₁ ⨟ σ₂)

  fusion : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} (M : Term s)
     → map₂ σ₂ (map₁ σ₁ M) ≡ map₂ (σ₁ ⨟ σ₂) M
     
  fusion-arg : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} {b}
     → (arg : Term s)
     → map-arg₂ σ₂ b (map-arg₁ σ₁ b arg) ≡ map-arg₂ (σ₁ ⨟ σ₂) b arg

  fusion {.(Size.↑ _)} {σ₁} {σ₂} (` x)
      rewrite map-quote (⧼ σ₁ ⧽₁ x) σ₂ | var x σ₁ σ₂  = refl
  fusion {.(Size.↑ _)} {σ₁} {σ₂} (_⦅_⦆ {s} op args) =
      let fa = (λ {b} arg → fusion-arg {_}{σ₁}{σ₂}{b} arg) in
      let mc = map-cong {λ _ → Term s}{λ _ → ABT} (λ{b}→ fa {b}) in
      cong (_⦅_⦆ op) (trans map-compose  mc)
      
  fusion-arg {s} {σ₁} {σ₂} {zero} arg = fusion arg
  fusion-arg {s} {σ₁} {σ₂} {suc b} arg =
    let IH = fusion-arg {s} {ext₁ σ₁} {ext₂ σ₂} {b} arg in
    begin
        map-arg₂ (ext₂ σ₂) b (map-arg₁ (ext₁ σ₁) b arg)
    ≡⟨ IH ⟩
        map-arg₂ (ext₁ σ₁ ⨟ ext₂ σ₂) b arg
    ≡⟨ cong (λ □ → map-arg₂ □ b arg) (compose-ext σ₁ σ₂) ⟩
        map-arg₂ (ext₂ (σ₁ ⨟ σ₂)) b arg
    ∎

{-------------------------------------------------------------------------------
  Congruence of map

  map-cong-abt : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} 
      → σ₁ ≈ σ₂ → (M : Term s) → map₁ σ₁ M ≡ map₂ σ₂ M
 ------------------------------------------------------------------------------}
 
record MapCong {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂) : Set₁ where
  open Map M₁ using () renaming (map-abt to map₁; map-arg to map-arg₁;
      “_” to “_”₁) public
  open Map.GS M₁ using () renaming (⧼_⧽ to ⧼_⧽₁; g-ext to ext₁) public
  open Substable (Map.S M₁) using ()
      renaming (var→val to var→val₁; shift to shift₁)
  open Map M₂ using () renaming (map-abt to map₂; map-arg to map-arg₂;
      “_” to “_”₂) public
  open Map.GS M₂ using () renaming (⧼_⧽ to ⧼_⧽₂; g-ext to ext₂) public
  open Substable (Map.S M₂) using ()
      renaming (var→val to var→val₂; shift to shift₂)
  _∼_ = λ v₁ v₂ → “ v₁ ”₁ ≡ “ v₂ ”₂

  field var→val-quote : (x : ℕ) → “ var→val₁ x ”₁ ≡ “ var→val₂ x ”₂
        shift-quote : ∀{v₁ v₂} → “ v₁ ”₁ ≡ “ v₂ ”₂
                    → “ shift₁ v₁ ”₁ ≡ “ shift₂ v₂ ”₂

  module R = Relate (Map.S M₁) (Map.S M₂) _∼_ var→val-quote shift-quote
  open R renaming (_≊_ to _≈_; g-ext-≊ to ext≈; g-lookup to lookup)

  map-cong-abt : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} 
      → σ₁ ≈ σ₂ → (M : Term s) → map₁ σ₁ M ≡ map₂ σ₂ M

  map-cong-arg : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} {b : ℕ}
      → σ₁ ≈ σ₂ → (arg : Term s) → map-arg₁ σ₁ b arg ≡ map-arg₂ σ₂ b arg

  map-cong-abt {.(Size.↑ _)} {σ₁} {σ₂} σ₁≈σ₂ (` x) = lookup x σ₁≈σ₂
  map-cong-abt {.(Size.↑ _)} {σ₁} {σ₂} σ₁≈σ₂ (_⦅_⦆ {s} op args) =
      cong (_⦅_⦆ op) (map-cong λ {b} M → map-cong-arg {_}{σ₁}{σ₂}{b} σ₁≈σ₂ M)
  map-cong-arg {s} {σ₁} {σ₂} {zero} σ₁≈σ₂ arg = map-cong-abt σ₁≈σ₂ arg
  map-cong-arg {s} {σ₁} {σ₂} {suc b} σ₁≈σ₂ arg =
      map-cong-arg {s} {ext₁ σ₁} {ext₂ σ₂} {b} (ext≈ σ₁≈σ₂) arg

{-------------------------------------------------------------------------------
  Commutativity of map

  map-commute : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} 
      → ...
      → map₁ σ₁ (map₂ σ₂ M) ≡ map₂ σ₂' (map₁ σ₁' M)
 ------------------------------------------------------------------------------}
