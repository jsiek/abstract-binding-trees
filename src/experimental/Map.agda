{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Size using (Size)
open import Var
open import experimental.ScopedTuple
open import Syntax hiding (⦉_⦊; ext)

module experimental.Map (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig

{-------------------------------------------------------------------------------
 Mapping over an abstract binding tree
 (generalizes renaming and substitution)
 ------------------------------------------------------------------------------}

record Map (V : Set) : Set where
  field “_” : V → ABT
        var→val : Var → V
        shift : V → V
        var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x)
        “_”-0 : “_” (var→val 0) ≡ ` 0

  module S = GenericSubst V var→val shift var→val-suc-shift
  open S

  map-abt : ∀{s : Size} → Substitution V → Term s → ABT
  map-arg : ∀{s : Size} → Substitution V → (b : ℕ) →  Term s → ABT
  
  map-abt σ (` x) = “ ⧼ σ ⧽ x ”
  map-abt σ (op ⦅ args ⦆) = op ⦅ map (λ {b} → map-arg σ b) args ⦆
  map-arg σ zero M = map-abt σ M
  map-arg σ (suc b) M = map-arg (g-ext σ) b M

{-------------------------------------------------------------------------------
 Renaming and substitution 
 ------------------------------------------------------------------------------}

RenameIsMap : Map Var 
RenameIsMap = record { “_” = `_ ; var→val = λ x → x ; shift = suc
                     ; var→val-suc-shift = λ {x} → refl
                     ; “_”-0 = refl }
open Map RenameIsMap renaming (map-abt to rename; map-arg to rename-arg)
open Map.S RenameIsMap using ()
    renaming (⧼_⧽ to ⦉_⦊; g-ext to ext; g-inc to inc; g-drop to dropr;
    g-drop-add to dropr-add; g-drop-drop to dropr-dropr;
    g-drop-ext to dropr-ext)

SubstIsMap : Map ABT
SubstIsMap = record { “_” = λ M → M ; var→val = `_ ; shift = rename (↑ 1)
                    ; var→val-suc-shift = refl
                    ; “_”-0 = refl }
open Map SubstIsMap renaming (map-abt to ⟪_⟫; map-arg to ⟪_⟫ₐ; g-ext to exts;
    ⧼_⧽ to ⟦_⟧; g-inc to incs; g-drop to drops; g-drop-inc to drops-incs)

{-------------------------------------------------------------------------------
 Fusion of two maps
 ------------------------------------------------------------------------------}

module ComposeMaps {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂)
   (⌈_⌉ : Substitution V₂ → V₁ → V₂)
   where

  {-
   Examples to generalize from:
    _⨟ᵣ_ : Rename → Rename → Rename
    ↑ k ⨟ᵣ ρ = dropr k ρ
    (x • ρ₁) ⨟ᵣ ρ₂ = ⦉ ρ₂ ⦊ x • (ρ₁ ⨟ᵣ ρ₂)

    _⨟_ : Subst → Subst → Subst
    ↑ k ⨟ τ = drop k τ
    (M • σ) ⨟ τ = ⟪ τ ⟫ M • (σ ⨟ τ)
   -}
  open GenericSubst V₂ (Map.var→val M₂) (Map.shift M₂)
      (Map.var→val-suc-shift M₂) using (g-drop)
   
  infixr 5 _⨟_
  _⨟_ : Substitution V₁ → Substitution V₂ → Substitution V₂
  ↑ k ⨟ σ₂ = g-drop k σ₂
  (v₁ • σ₁) ⨟ σ₂ = ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)

record FusableMap {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂) : Set where
  open Map M₁ using () renaming (map-abt to map₁; map-arg to map-arg₁;
      “_” to “_”₁; “_”-0 to “_”-0₁) public
  open Map.S M₁ using () renaming (⧼_⧽ to ⧼_⧽₁; g-ext to ext₁) public
  open Map M₂ using () renaming (map-abt to map₂; map-arg to map-arg₂;
      “_” to “_”₂; “_”-0 to “_”-0₂;
      shift to shift₂; g-drop-inc to drop-inc₂) public
  open Map.S M₂ using () renaming (⧼_⧽ to ⧼_⧽₂; g-ext to ext₂;
      g-inc to inc₂; g-drop to drop₂) public
  field ⌈_⌉ : Substitution V₂ → V₁ → V₂
  open ComposeMaps M₁ M₂ ⌈_⌉ public
  field var : ∀ x σ₁ σ₂ → ⌈ σ₂ ⌉ (⧼ σ₁ ⧽₁ x) ≡ ⧼ σ₁ ⨟ σ₂ ⧽₂ x
  field map-quote : ∀ v₁ σ₂ → map₂ σ₂ “ v₁ ”₁ ≡ “ ⌈ σ₂ ⌉ v₁ ”₂
  field compose-ext : ∀ (σ₁ : Substitution V₁) (σ₂ : Substitution V₂)
                    → ext₁ σ₁ ⨟ ext₂ σ₂ ≡ ext₂ (σ₁ ⨟ σ₂)

module FuseMaps {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂)
  (FM : FusableMap M₁ M₂) where
  open FusableMap FM

  fusion : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} (M : Term s)
     → map₂ σ₂ (map₁ σ₁ M) ≡ map₂ (σ₁ ⨟ σ₂) M
  fusion-arg : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} {b}
     → (arg : Term s)
     → map-arg₂ σ₂ b (map-arg₁ σ₁ b arg) ≡ map-arg₂ (σ₁ ⨟ σ₂) b arg

  fusion {.(Size.↑ _)} {σ₁} {σ₂} (` x)
      rewrite map-quote (⧼ σ₁ ⧽₁ x) σ₂ | var x σ₁ σ₂  = refl
  fusion {.(Size.↑ _)} {σ₁} {σ₂} (_⦅_⦆ {s} op args) =
      let all-args = all-intro (λ{b}→ P{s}{b})
                 (λ {b} arg → fusion-arg {_}{_}{_}{b} arg) args in
      cong (_⦅_⦆ op) (all→pred (λ{b}→ P{s}{b}) P× L all-args)
      where
      P : ∀{s : Size} → 𝒫 (λ _ → Term s)
      P {s}{b} arg = ∀{σ₁ σ₂}
          → map-arg₂ σ₂ b (map-arg₁ σ₁ b arg) ≡ map-arg₂ (σ₁ ⨟ σ₂) b arg
      P× : ∀{s : Size}{bs : List ℕ} → Tuple bs (λ _ → Term s) → Set
      P× {s}{bs} args = ∀{s : Size}{σ₁ σ₂} → map (λ {b} → map-arg₂ σ₂ b)
                         (map (λ {b} → map-arg₁ σ₁ b) args)
                      ≡ map (λ {b} → map-arg₂ (σ₁ ⨟ σ₂) b) args
      L : ∀{s} → Lift-Pred-Tuple (λ {b} → P{s}{b}) (λ {bs} → P×)
      L = record { base = λ {σ₁} {σ₂} → refl
                 ; step = λ Px Pxs → cong₂ ⟨_,_⟩ Px Pxs }
  fusion-arg {s} {σ₁} {σ₂} {zero} arg = fusion arg
  fusion-arg {s} {σ₁} {σ₂} {suc b} arg =
    let IH = fusion-arg {s} {ext₁ σ₁} {ext₂ σ₂} {b} arg in
    begin
      map-arg₂ σ₂ (suc b) (map-arg₁ σ₁ (suc b) arg)
    ≡⟨⟩
        map-arg₂ (ext₂ σ₂) b (map-arg₁ (ext₁ σ₁) b arg)
    ≡⟨ IH ⟩
        map-arg₂ (ext₁ σ₁ ⨟ ext₂ σ₂) b arg
    ≡⟨ cong (λ □ → map-arg₂ □ b arg) (compose-ext σ₁ σ₂) ⟩
      map-arg₂ (ext₂ (σ₁ ⨟ σ₂)) b arg
    ≡⟨⟩
      map-arg₂ (σ₁ ⨟ σ₂) (suc b) arg
    ∎

{-------------------------------------------------------------------------------
 Compose two renamings
 ------------------------------------------------------------------------------}
module _ where
  open ComposeMaps RenameIsMap RenameIsMap ⦉_⦊

  seq-rename : ∀ ρ₁ ρ₂ x → ⦉ ρ₁ ⨟ ρ₂ ⦊ x ≡ ⦉ ρ₂ ⦊ (⦉ ρ₁ ⦊ x)
  seq-rename (↑ k) ρ₂ x = dropr-add k ρ₂
  seq-rename (x₁ • ρ₁) ρ₂ zero = refl
  seq-rename (x₁ • ρ₁) ρ₂ (suc x) = seq-rename ρ₁ ρ₂ x

  dropr-seq : ∀ k ρ ρ' → dropr k (ρ ⨟ ρ') ≡ (dropr k ρ ⨟ ρ')
  dropr-seq k (↑ k₁) ρ' = sym (dropr-dropr k k₁ ρ')
  dropr-seq zero (x • ρ) ρ' = refl
  dropr-seq (suc k) (x • ρ) ρ' = dropr-seq k ρ ρ'
  
  ren-assoc : ∀ {σ τ θ : Substitution Var}
            → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  ren-assoc {↑ k} {τ} {θ} = sym (dropr-seq k τ θ)
  ren-assoc {x • σ} {τ} {θ}
      rewrite seq-rename τ θ x | ren-assoc {σ}{τ}{θ} = refl
  {-# REWRITE ren-assoc #-}

  inc-seq : ∀ ρ₁ ρ₂ → (inc ρ₁ ⨟ ext ρ₂) ≡ inc (ρ₁ ⨟ ρ₂)
  inc-seq (↑ k) ρ₂ = dropr-ext k ρ₂
  inc-seq (x • ρ₁) ρ₂ rewrite inc-seq ρ₁ ρ₂ | ext-suc ρ₂ x = refl

  compose-ext : ∀{ρ₁ ρ₂ : Rename}
              → (ext ρ₁ ⨟ ext ρ₂) ≡ ext (ρ₁ ⨟ ρ₂)
  compose-ext {ρ₁}{ρ₂} rewrite inc-seq ρ₁ ρ₂ = refl

  RenRenRus : FusableMap RenameIsMap RenameIsMap
  RenRenRus = record { ⌈_⌉ = ⦉_⦊ ; var = λ x ρ₁ ρ₂ → sym (seq-rename ρ₁ ρ₂ x)
                     ; map-quote = λ v₁ ρ₂ → refl
                     ; compose-ext = λ ρ₁ ρ₂ → compose-ext {ρ₁}{ρ₂}}


