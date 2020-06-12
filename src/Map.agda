open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var
open import ScopedTuple using (map; map-cong; map-compose)
open import GenericSubstitution

module Map (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig

{-------------------------------------------------------------------------------
 Mapping a substitution over an abstract binding tree
 (generalizes renaming and substitution)
 ------------------------------------------------------------------------------}

record Map (V : Set) : Set where
  field S : Substable V
        “_” : V → ABT
  open Substable S 
  open GenericSubst S

  map-abt : GSubst V → ABT → ABT
  map-arg : GSubst V → {b : ℕ} →  Arg b → Arg b
  map-args : GSubst V → {bs : List ℕ} →  Args bs → Args bs
  
  map-abt σ (` x) = “ ⧼ σ ⧽ x ”
  map-abt σ (op ⦅ args ⦆) = op ⦅ map-args σ {sig op} args ⦆
  map-arg σ {zero} (ast M) = ast (map-abt σ M)
  map-arg σ {suc b} (bind M) = bind (map-arg (g-ext σ) M)
  map-args σ {[]} nil = nil
  map-args σ {b ∷ bs} (cons x args) = cons (map-arg σ x) (map-args σ args)

{-------------------------------------------------------------------------------
  Fusion of two maps

  fusion : ∀{s}{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} (M : Term s)
     → map₂ σ₂ (map₁ σ₁ M) ≡ map₂ (σ₁ ⨟ σ₂) M
 ------------------------------------------------------------------------------}

module ComposeMaps {V₁ V₂ V₃ : Set} (M₁ : Map V₁) (M₂ : Map V₂)
   (⌈_⌉ : GSubst V₂ → V₁ → V₃)
   (val₂₃ : V₂ → V₃) where
  {- The following generalizes _⨟ᵣ_ and _⨟_, as well as compositions
     of renaming and subtitution. -}
  infixr 5 _⨟_

  abstract
    _⨟_ : GSubst V₁ → GSubst V₂ → GSubst V₃
    ↑ k ⨟ σ₂ = map-sub val₂₃ (drop k σ₂)
    (v₁ • σ₁) ⨟ σ₂ = ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)

  abstract
    up-seq : ∀ k σ₂ → ↑ k ⨟ σ₂ ≡ map-sub val₂₃ (drop k σ₂)
    up-seq k σ₂ = refl

    cons-seq : ∀ v₁ σ₁ σ₂ → (v₁ • σ₁) ⨟ σ₂ ≡ ⌈ σ₂ ⌉ v₁ • (σ₁ ⨟ σ₂)
    cons-seq  v₁ σ₁ σ₂ = refl

record Quotable {V₁ V₂ V₃}
  (M₁ : Map V₁) (M₂ : Map V₂) (M₃ : Map V₃) : Set
  where
  open Map M₁ using () renaming (“_” to “_”₁)
  open Substable (Map.S M₁) using () renaming (var→val to var→val₁)
  open GenericSubst (Map.S M₁) using ()
      renaming (⧼_⧽ to ⧼_⧽₁; g-inc to g-inc₁) 
  open Map M₂ using () renaming (map-abt to map₂; “_” to “_”₂)
  open Substable (Map.S M₂) using ()
      renaming (var→val to var→val₂; shift to shift₂)
  open GenericSubst (Map.S M₂) using () renaming (⧼_⧽ to ⧼_⧽₂; g-inc to g-inc₂) 
  open Map M₃ using () renaming (“_” to “_”₃) 
  open Substable (Map.S M₃) using ()
    renaming (var→val to var→val₃; shift to shift₃)
  open GenericSubst (Map.S M₃) using ()
      renaming (⧼_⧽ to ⧼_⧽₃; g-drop-add to g-drop-add₃; g-inc to g-inc₃) 
  
  field ⌈_⌉ : GSubst V₂ → V₁ → V₃
        val₂₃ : V₂ → V₃
        quote-map : ∀ σ₂ v₁ → “ ⌈ σ₂ ⌉ v₁ ”₃ ≡ map₂ σ₂ “ v₁ ”₁
        var→val₂₃ : ∀ x → var→val₃ x ≡ val₂₃ (var→val₂ x)
        quote-val₂₃ : ∀ v₂ → “ val₂₃ v₂ ”₃ ≡ “ v₂ ”₂
        map₂-var→val₁ : ∀ x σ₂ → map₂ σ₂ “ var→val₁ x ”₁ ≡ “ ⧼ σ₂ ⧽₂ x ”₂
        val₂₃-shift : ∀ v₂ → val₂₃ (shift₂ v₂) ≡ shift₃ (val₂₃ v₂)

  
  open ComposeMaps M₁ M₂ ⌈_⌉ val₂₃
  
  g-map-sub-⧼·⧽ : ∀{x} (σ : GSubst V₂)
     → ⧼ map-sub val₂₃ σ ⧽₃ x ≡ val₂₃ (⧼ σ ⧽₂ x)
  g-map-sub-⧼·⧽ {x} (↑ k) = var→val₂₃ (k + x)
  g-map-sub-⧼·⧽ {zero} (v₂ • σ) = refl
  g-map-sub-⧼·⧽ {suc x} (v₂ • σ) = g-map-sub-⧼·⧽ {x} σ

  compose-sub : ∀ σ₁ σ₂ x → “ ⧼ σ₁ ⨟ σ₂ ⧽₃ x ”₃ ≡ (map₂ σ₂ “ ⧼ σ₁ ⧽₁ x ”₁)
  compose-sub (↑ k) σ₂ x =                  begin
    “ ⧼ ↑ k ⨟ σ₂ ⧽₃ x ”₃                   ≡⟨ cong (λ □ → “ ⧼ □ ⧽₃ x ”₃)  (up-seq _ _) ⟩
    “ ⧼ map-sub val₂₃ (drop k σ₂) ⧽₃ x ”₃  ≡⟨ cong (λ □ → “ ⧼ □ ⧽₃ x ”₃) (map-sub-drop σ₂ val₂₃ k) ⟩
    “ ⧼ drop k (map-sub val₂₃ σ₂) ⧽₃ x ”₃  ≡⟨ cong “_”₃ (g-drop-add₃ k (map-sub val₂₃ σ₂) x) ⟩
    “ ⧼ map-sub val₂₃ σ₂ ⧽₃ (k + x) ”₃     ≡⟨ cong “_”₃ (g-map-sub-⧼·⧽ σ₂) ⟩
    “ val₂₃ (⧼ σ₂ ⧽₂ (k + x)) ”₃           ≡⟨ quote-val₂₃ (⧼ σ₂ ⧽₂ (k + x)) ⟩
    “ ⧼ σ₂ ⧽₂ (k + x) ”₂                   ≡⟨ sym (map₂-var→val₁ (k + x) σ₂) ⟩
    map₂ σ₂ “ ⧼ ↑ k ⧽₁ x ”₁                ∎
  compose-sub (v₁ • σ₁) σ₂ zero rewrite sym (quote-map σ₂ v₁)
      | cons-seq v₁ σ₁ σ₂ = refl
  compose-sub (v₁ • σ₁) σ₂ (suc x) rewrite cons-seq v₁ σ₁ σ₂
      | compose-sub σ₁ σ₂ x = refl

  g-drop-seq : ∀ k σ₁ σ₂ → drop k (σ₁ ⨟ σ₂) ≡ (drop k σ₁ ⨟ σ₂)
  g-drop-seq k (↑ k₁) σ₂ =               begin
    drop k (↑ k₁ ⨟ σ₂)                    ≡⟨ cong (drop k) (up-seq _ _) ⟩
    drop k (map-sub val₂₃ (drop k₁ σ₂))   ≡⟨  sym (map-sub-drop (drop k₁ σ₂) val₂₃ k) ⟩
    map-sub val₂₃ (drop k (drop k₁ σ₂))   ≡⟨  cong (map-sub val₂₃) (sym (drop-drop k k₁ σ₂)) ⟩
    map-sub val₂₃ (drop (k + k₁) σ₂)      ≡⟨ sym (up-seq _ σ₂) ⟩
    ↑ (k + k₁) ⨟ σ₂                       ∎
  g-drop-seq zero (x • σ₁) σ₂ rewrite cons-seq x σ₁ σ₂ = refl
  g-drop-seq (suc k) (x • σ₁) σ₂ rewrite cons-seq x σ₁ σ₂
      | g-drop-seq k σ₁ σ₂ = refl

  g-map-sub-inc : ∀ σ₂ → map-sub val₂₃ (g-inc₂ σ₂) ≡  g-inc₃ (map-sub val₂₃ σ₂)
  g-map-sub-inc (↑ k) = refl
  g-map-sub-inc (v₂ • σ₂) = cong₂ _•_ (val₂₃-shift v₂) (g-map-sub-inc σ₂)


record FusableMap {V₁ V₂ V₃} (M₁ : Map V₁) (M₂ : Map V₂) (M₃ : Map V₃) : Set
  where
  open Map M₁ using () renaming (
      map-abt to map₁; map-arg to map-arg₁; map-args to map-args₁;
      “_” to “_”₁; var→val to var→val₁) public
  open GenericSubst (Map.S M₁) using ()
      renaming (⧼_⧽ to ⧼_⧽₁; g-ext to ext₁) public
  open Map M₂ using () renaming (
      map-abt to map₂; map-arg to map-arg₂; map-args to map-args₂;
      “_” to “_”₂; var→val to var→val₂) public
  open GenericSubst (Map.S M₂) using ()
      renaming (⧼_⧽ to ⧼_⧽₂; g-ext to ext₂) public
  open Map M₃ using () renaming (
      map-abt to map₃; map-arg to map-arg₃; map-args to map-args₃;
      “_” to “_”₃; var→val to var→val₃) public
  open GenericSubst (Map.S M₃) using ()
      renaming (⧼_⧽ to ⧼_⧽₃; g-ext to ext₃; g-drop-add to g-drop-add₃) public
  
  field Q : Quotable M₁ M₂ M₃
  open Quotable Q
  open ComposeMaps M₁ M₂ ⌈_⌉ val₂₃ public
  field var : ∀ x σ₁ σ₂ → ⌈ σ₂ ⌉ (⧼ σ₁ ⧽₁ x) ≡ ⧼ (σ₁ ⨟ σ₂) ⧽₃ x
        compose-ext : ∀ (σ₁ : GSubst V₁) (σ₂ : GSubst V₂)
                    → ext₁ σ₁ ⨟ ext₂ σ₂ ≡ ext₃ (σ₁ ⨟ σ₂)

  fusion : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} (M : ABT)
     → map₂ σ₂ (map₁ σ₁ M) ≡ map₃ (σ₁ ⨟ σ₂) M
     
  fusion-arg : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} {b} (arg : Arg b)
     → map-arg₂ σ₂ (map-arg₁ σ₁ arg) ≡ map-arg₃ (σ₁ ⨟ σ₂) arg
  fusion-args : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} {bs} (args : Args bs)
     → map-args₂ σ₂ (map-args₁ σ₁ args) ≡ map-args₃ (σ₁ ⨟ σ₂) args

  fusion {σ₁} {σ₂} (` x)
      rewrite sym (quote-map σ₂ (⧼ σ₁ ⧽₁ x)) | var x σ₁ σ₂  = refl
  fusion {σ₁} {σ₂} (op ⦅ args ⦆) =
      cong (_⦅_⦆ op) (fusion-args args)
  fusion-arg {σ₁} {σ₂} {zero} (ast M) = cong ast (fusion M)
  fusion-arg {σ₁} {σ₂} {suc b} (bind arg) =
    cong bind H
    where
    IH = fusion-arg {ext₁ σ₁} {ext₂ σ₂} {b} arg
    H = begin
        map-arg₂ (ext₂ σ₂) (map-arg₁ (ext₁ σ₁) arg)   ≡⟨ IH ⟩
        map-arg₃ (ext₁ σ₁ ⨟ ext₂ σ₂) arg              ≡⟨ cong (λ □ → map-arg₃ □ arg) (compose-ext σ₁ σ₂) ⟩
        map-arg₃ (ext₃ (σ₁ ⨟ σ₂)) arg                 ∎
  fusion-args {σ₁} {σ₂} {[]} nil = refl
  fusion-args {σ₁} {σ₂} {b ∷ bs} (cons arg args) =
      cong₂ cons (fusion-arg arg) (fusion-args args)

{-------------------------------------------------------------------------------
  Congruence of map

  map-cong-abt : ∀{s}{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} 
      → σ₁ ≈ σ₂ → (M : Term s) → map₁ σ₁ M ≡ map₂ σ₂ M
 ------------------------------------------------------------------------------}
 
record MapCong {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂) : Set₁ where
  open Map M₁ using () renaming (map-abt to map₁; map-arg to map-arg₁;
      map-args to map-args₁; “_” to “_”₁) public
  open GenericSubst (Map.S M₁) using ()
      renaming (⧼_⧽ to ⧼_⧽₁; g-ext to ext₁) public
  open Map M₂ using ()
      renaming (map-abt to map₂; map-arg to map-arg₂; map-args to map-args₂;
      “_” to “_”₂) public
  open GenericSubst (Map.S M₂) using ()
      renaming (⧼_⧽ to ⧼_⧽₂; g-ext to ext₂) public

  field _≈_ : GSubst V₁ → GSubst V₂ → Set
        var : ∀ {σ₁ σ₂} x → σ₁ ≈ σ₂ → “ ⧼ σ₁ ⧽₁ x ”₁ ≡ “ ⧼ σ₂ ⧽₂ x ”₂
        ext≈ : ∀ {σ₁ σ₂} → σ₁ ≈ σ₂ → ext₁ σ₁ ≈ ext₂ σ₂
        
  map-cong-abt : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} 
      → σ₁ ≈ σ₂ → (M : ABT) → map₁ σ₁ M ≡ map₂ σ₂ M

  map-cong-arg : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} {b : ℕ}
      → σ₁ ≈ σ₂ → (arg : Arg b) → map-arg₁ σ₁ arg ≡ map-arg₂ σ₂ arg
  map-cong-args : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} {bs : List ℕ}
      → σ₁ ≈ σ₂ → (args : Args bs) → map-args₁ σ₁ args ≡ map-args₂ σ₂ args

  map-cong-abt {σ₁} {σ₂} σ₁≈σ₂ (` x) = var x σ₁≈σ₂
  map-cong-abt {σ₁} {σ₂} σ₁≈σ₂ (op ⦅ args ⦆) =
      cong (_⦅_⦆ op) (map-cong-args σ₁≈σ₂ args)
  map-cong-arg {σ₁} {σ₂} {zero} σ₁≈σ₂ (ast arg) =
      cong ast (map-cong-abt σ₁≈σ₂ arg)
  map-cong-arg {σ₁} {σ₂} {suc b} σ₁≈σ₂ (bind arg) =
      cong  bind (map-cong-arg {ext₁ σ₁} {ext₂ σ₂} {b} (ext≈ σ₁≈σ₂) arg)
  map-cong-args {σ₁} {σ₂} {[]} σ₁≈σ₂ nil = refl
  map-cong-args {σ₁} {σ₂} {b ∷ bs} σ₁≈σ₂ (cons arg args) =
      cong₂ cons (map-cong-arg σ₁≈σ₂ arg) (map-cong-args σ₁≈σ₂ args)


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


