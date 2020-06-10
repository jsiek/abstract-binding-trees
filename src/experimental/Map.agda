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
open import GenericSubstitution

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
  open GenericSubst S

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

module ComposeMaps {V₁ V₂ V₃ : Set} (M₁ : Map V₁) (M₂ : Map V₂)
   (⌈_⌉ : Substitution V₂ → V₁ → V₃)
   (val₂₃ : V₂ → V₃) where
  {- The following generalizes _⨟ᵣ_ and _⨟_, as well as compositions
     of renaming and subtitution. -}
  infixr 5 _⨟_
  
  _⨟_ : Substitution V₁ → Substitution V₂ → Substitution V₃
  ↑ k ⨟ σ₂ = g-map-sub val₂₃ (g-drop k σ₂)
  (v₁ • σ₁) ⨟ σ₂ = ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)

record Quotable {V₁ V₂ V₃}
  (M₁ : Map V₁) (M₂ : Map V₂) (M₃ : Map V₃) : Set
  where
  open Map M₁ using () renaming (“_” to “_”₁; var→val to var→val₁)
  open GenericSubst (Map.S M₁) using ()
      renaming (⧼_⧽ to ⧼_⧽₁; g-inc to g-inc₁) 
  open Map M₂ using () renaming (map-abt to map₂;
      “_” to “_”₂; var→val to var→val₂; shift to shift₂) 
  open GenericSubst (Map.S M₂) using () renaming (⧼_⧽ to ⧼_⧽₂; g-inc to g-inc₂) 
  open Map M₃ using () renaming (“_” to “_”₃; var→val to var→val₃;
      shift to shift₃) 
  open GenericSubst (Map.S M₃) using ()
      renaming (⧼_⧽ to ⧼_⧽₃; g-drop-add to g-drop-add₃; g-inc to g-inc₃) 
  
  field ⌈_⌉ : Substitution V₂ → V₁ → V₃
        val₂₃ : V₂ → V₃
        quote-map : ∀ σ₂ v₁ → “ ⌈ σ₂ ⌉ v₁ ”₃ ≡ map₂ σ₂ “ v₁ ”₁
        var→val₂₃ : ∀ x → var→val₃ x ≡ val₂₃ (var→val₂ x)
        quote-val₂₃ : ∀ v₂ → “ val₂₃ v₂ ”₃ ≡ “ v₂ ”₂
        map₂-var→val₁ : ∀ x σ₂ → map₂ σ₂ “ var→val₁ x ”₁ ≡ “ ⧼ σ₂ ⧽₂ x ”₂
        val₂₃-shift : ∀ v₂ → val₂₃ (shift₂ v₂) ≡ shift₃ (val₂₃ v₂)

  
  open ComposeMaps M₁ M₂ ⌈_⌉ val₂₃
  
  g-map-sub-⧼·⧽ : ∀{x} (σ : Substitution V₂)
     → ⧼ g-map-sub val₂₃ σ ⧽₃ x ≡ val₂₃ (⧼ σ ⧽₂ x)
  g-map-sub-⧼·⧽ {x} (↑ k) = var→val₂₃ (k + x)
  g-map-sub-⧼·⧽ {zero} (v₂ • σ) = refl
  g-map-sub-⧼·⧽ {suc x} (v₂ • σ) = g-map-sub-⧼·⧽ {x} σ

  compose-sub : ∀ σ₁ σ₂ x → “ ⧼ σ₁ ⨟ σ₂ ⧽₃ x ”₃ ≡ (map₂ σ₂ “ ⧼ σ₁ ⧽₁ x ”₁)
  compose-sub (↑ k) σ₂ x =
      begin
          “ ⧼ ↑ k ⨟ σ₂ ⧽₃ x ”₃
      ≡⟨⟩
          “ ⧼ g-map-sub val₂₃ (g-drop k σ₂) ⧽₃ x ”₃
      ≡⟨ cong (λ □ → “ ⧼ □ ⧽₃ x ”₃) (g-map-sub-drop σ₂ val₂₃ k) ⟩
          “ ⧼ g-drop k (g-map-sub val₂₃ σ₂) ⧽₃ x ”₃
      ≡⟨ cong “_”₃ (g-drop-add₃ k (g-map-sub val₂₃ σ₂)) ⟩
          “ ⧼ g-map-sub val₂₃ σ₂ ⧽₃ (k + x) ”₃
      ≡⟨ cong “_”₃ (g-map-sub-⧼·⧽ σ₂) ⟩
          “ val₂₃ (⧼ σ₂ ⧽₂ (k + x)) ”₃
      ≡⟨ quote-val₂₃ (⧼ σ₂ ⧽₂ (k + x)) ⟩
          “ ⧼ σ₂ ⧽₂ (k + x) ”₂
      ≡⟨ sym (map₂-var→val₁ (k + x) σ₂) ⟩
          map₂ σ₂ “ var→val₁ (k + x) ”₁
      ≡⟨⟩
          map₂ σ₂ “ ⧼ ↑ k ⧽₁ x ”₁
      ∎
  compose-sub (v₁ • σ₁) σ₂ zero rewrite quote-map σ₂ v₁ = refl
  compose-sub (v₁ • σ₁) σ₂ (suc x) = compose-sub σ₁ σ₂ x

  g-drop-seq : ∀ k σ₁ σ₂ → g-drop k (σ₁ ⨟ σ₂) ≡ (g-drop k σ₁ ⨟ σ₂)
  g-drop-seq k (↑ k₁) σ₂ = {- sym (g-drop-drop k k₁ σ₂) -}
      begin
          g-drop k (↑ k₁ ⨟ σ₂)
      ≡⟨⟩
          g-drop k (g-map-sub val₂₃ (g-drop k₁ σ₂))
      ≡⟨  sym (g-map-sub-drop (g-drop k₁ σ₂) val₂₃ k) ⟩
          g-map-sub val₂₃ (g-drop k (g-drop k₁ σ₂))
      ≡⟨  cong (g-map-sub val₂₃) (sym (g-drop-drop k k₁ σ₂)) ⟩
          g-map-sub val₂₃ (g-drop (k + k₁) σ₂)
      ≡⟨⟩
          ↑ (k + k₁) ⨟ σ₂
      ∎
  g-drop-seq zero (x • σ₁) σ₂ = refl
  g-drop-seq (suc k) (x • σ₁) σ₂ = g-drop-seq k σ₁ σ₂

{-
  g-inc=⨟↑ : ∀ σ → g-inc₁ σ₁ ≡ σ₁ ⨟ ↑ 1
  g-inc=⨟↑ σ = ?
-}

  g-map-sub-inc : ∀ σ₂ →
    g-map-sub val₂₃ (g-inc₂ σ₂) ≡  g-inc₃ (g-map-sub val₂₃ σ₂)
  g-map-sub-inc (↑ k) = refl
  g-map-sub-inc (v₂ • σ₂) = cong₂ _•_ (val₂₃-shift v₂) (g-map-sub-inc σ₂)
  

record FusableMap {V₁ V₂ V₃} (M₁ : Map V₁) (M₂ : Map V₂) (M₃ : Map V₃) : Set
  where
  open Map M₁ using () renaming (map-abt to map₁; map-arg to map-arg₁;
      “_” to “_”₁; var→val to var→val₁) public
  open GenericSubst (Map.S M₁) using ()
      renaming (⧼_⧽ to ⧼_⧽₁; g-ext to ext₁) public
  open Map M₂ using () renaming (map-abt to map₂; map-arg to map-arg₂;
      “_” to “_”₂; var→val to var→val₂) public
  open GenericSubst (Map.S M₂) using ()
      renaming (⧼_⧽ to ⧼_⧽₂; g-ext to ext₂) public
  open Map M₃ using () renaming (map-abt to map₃; map-arg to map-arg₃;
      “_” to “_”₃; var→val to var→val₃) public
  open GenericSubst (Map.S M₃) using ()
      renaming (⧼_⧽ to ⧼_⧽₃; g-ext to ext₃; g-drop-add to g-drop-add₃) public
  
  field Q : Quotable M₁ M₂ M₃
  open Quotable Q
  open ComposeMaps M₁ M₂ ⌈_⌉ val₂₃ public
  field var : ∀ x σ₁ σ₂ → ⌈ σ₂ ⌉ (⧼ σ₁ ⧽₁ x) ≡ ⧼ (σ₁ ⨟ σ₂) ⧽₃ x
        compose-ext : ∀ (σ₁ : Substitution V₁) (σ₂ : Substitution V₂)
                    → ext₁ σ₁ ⨟ ext₂ σ₂ ≡ ext₃ (σ₁ ⨟ σ₂)

  fusion : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} (M : Term s)
     → map₂ σ₂ (map₁ σ₁ M) ≡ map₃ (σ₁ ⨟ σ₂) M
     
  fusion-arg : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} {b}
     → (arg : Term s)
     → map-arg₂ σ₂ b (map-arg₁ σ₁ b arg) ≡ map-arg₃ (σ₁ ⨟ σ₂) b arg

  fusion {.(Size.↑ _)} {σ₁} {σ₂} (` x)
      rewrite sym (quote-map σ₂ (⧼ σ₁ ⧽₁ x)) | var x σ₁ σ₂  = refl
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
        map-arg₃ (ext₁ σ₁ ⨟ ext₂ σ₂) b arg
    ≡⟨ cong (λ □ → map-arg₃ □ b arg) (compose-ext σ₁ σ₂) ⟩
        map-arg₃ (ext₃ (σ₁ ⨟ σ₂)) b arg
    ∎



{-------------------------------------------------------------------------------
  Congruence of map

  map-cong-abt : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} 
      → σ₁ ≈ σ₂ → (M : Term s) → map₁ σ₁ M ≡ map₂ σ₂ M
 ------------------------------------------------------------------------------}
 
record MapCong {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂) : Set₁ where
  open Map M₁ using () renaming (map-abt to map₁; map-arg to map-arg₁;
      “_” to “_”₁) public
  open GenericSubst (Map.S M₁) using ()
      renaming (⧼_⧽ to ⧼_⧽₁; g-ext to ext₁) public
  open Map M₂ using ()
      renaming (map-abt to map₂; map-arg to map-arg₂; “_” to “_”₂) public
  open GenericSubst (Map.S M₂) using ()
      renaming (⧼_⧽ to ⧼_⧽₂; g-ext to ext₂) public

  field _≈_ : Substitution V₁ → Substitution V₂ → Set
        var : ∀ {σ₁ σ₂} x → σ₁ ≈ σ₂ → “ ⧼ σ₁ ⧽₁ x ”₁ ≡ “ ⧼ σ₂ ⧽₂ x ”₂
        ext≈ : ∀ {σ₁ σ₂} → σ₁ ≈ σ₂ → ext₁ σ₁ ≈ ext₂ σ₂
        
  map-cong-abt : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} 
      → σ₁ ≈ σ₂ → (M : Term s) → map₁ σ₁ M ≡ map₂ σ₂ M

  map-cong-arg : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} {b : ℕ}
      → σ₁ ≈ σ₂ → (arg : Term s) → map-arg₁ σ₁ b arg ≡ map-arg₂ σ₂ b arg

  map-cong-abt {.(Size.↑ _)} {σ₁} {σ₂} σ₁≈σ₂ (` x) = var x σ₁≈σ₂
  map-cong-abt {.(Size.↑ _)} {σ₁} {σ₂} σ₁≈σ₂ (_⦅_⦆ {s} op args) =
      cong (_⦅_⦆ op) (map-cong λ {b} M → map-cong-arg {_}{σ₁}{σ₂}{b} σ₁≈σ₂ M)
  map-cong-arg {s} {σ₁} {σ₂} {zero} σ₁≈σ₂ arg = map-cong-abt σ₁≈σ₂ arg
  map-cong-arg {s} {σ₁} {σ₂} {suc b} σ₁≈σ₂ arg =
      map-cong-arg {s} {ext₁ σ₁} {ext₂ σ₂} {b} (ext≈ σ₁≈σ₂) arg


record MapCong≊ {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂) : Set₁ where
  open Map M₁ using () renaming (“_” to “_”₁)
  open Substable (Map.S M₁) using ()
      renaming (var→val to var→val₁; shift to shift₁)
  open Map M₂ using () renaming (“_” to “_”₂) 
  open Substable (Map.S M₂) using ()
      renaming (var→val to var→val₂; shift to shift₂)
      
  _∼_ = λ v₁ v₂ → “ v₁ ”₁ ≡ “ v₂ ”₂
  field var→val-quote : (x : ℕ) → “ var→val₁ x ”₁ ≡ “ var→val₂ x ”₂
        shift-quote : ∀{v₁ v₂} → “ v₁ ”₁ ≡ “ v₂ ”₂
                    → “ shift₁ v₁ ”₁ ≡ “ shift₂ v₂ ”₂
  module R = Relate (Map.S M₁) (Map.S M₂) _∼_ var→val-quote shift-quote
  open R renaming (_≊_ to _≈_; g-ext-≊ to ext≈; g-lookup to lookup)

  MC : MapCong M₁ M₂
  MC = record { _≈_ = _≈_ ; var = lookup ; ext≈ = ext≈ }
  open MapCong MC public

{-------------------------------------------------------------------------------
  Commutativity of map

  map-commute : ∀{s}{σ₁ : Substitution V₁}{σ₂ : Substitution V₂} 
      → ...
      → map₁ σ₁ (map₂ σ₂ M) ≡ map₂ σ₂' (map₁ σ₁' M)
 ------------------------------------------------------------------------------}
