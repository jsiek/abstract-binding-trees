{- OBSOLETE, superceeded by Map2 and additions to GenericSubstitution -}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Environment
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Var
{-
open import ScopedTuple using (map; map-cong; map-compose)
-}
open import GenericSubstitution

module Map (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig

{-------------------------------------------------------------------------------
 Mapping a substitution over an abstract binding tree
 (generalizes renaming and substitution)
 ------------------------------------------------------------------------------}

{- MapEnv is abstract with respect to the environment -}

record MapEnv (E : Set) (V : Set) : Set where
  field is-Env : Env E V
  open Env is-Env public
  field V-is-Quotable : Quotable V
  open Quotable V-is-Quotable public
  
  map-abt : E → ABT → ABT
  map-arg : E → {b : ℕ} →  Arg b → Arg b
  map-args : E → {bs : List ℕ} →  Args bs → Args bs
  
  map-abt σ (` x) = “ lookup σ x ”
  map-abt σ (op ⦅ args ⦆) = op ⦅ map-args σ args ⦆
  map-arg σ {zero} (ast M) = ast (map-abt σ M)
  map-arg σ {suc b} (bind M) = bind (map-arg (ext-env σ) M)
  map-args σ {[]} nil = nil
  map-args σ {b ∷ bs} (cons x args) = cons (map-arg σ x) (map-args σ args)


{- Map instantiates MapEnv using substitutions for the environment -}
record Map (V : Set) : Set where
  field V-is-Quotable : Quotable V
        V-is-Shiftable : Shiftable V

  open GenericSubst V-is-Shiftable using (GSubst-is-Env)
  GSubst-is-MapEnv : MapEnv (GSubst V) V
  GSubst-is-MapEnv = record { is-Env = GSubst-is-Env
                            ;  V-is-Quotable = V-is-Quotable }
  open MapEnv GSubst-is-MapEnv using (map-abt; map-arg; map-args; is-Env) public
  open Env is-Env public {- Why needed? -Jeremy -}

  ⟪_⟫ : GSubst V → ABT → ABT
  ⟪_⟫ = map-abt
  ⟪_⟫ₐ : GSubst V → {b : ℕ} →  Arg b → Arg b
  ⟪_⟫ₐ = map-arg
  ⟪_⟫₊ : GSubst V → {bs : List ℕ} →  Args bs → Args bs
  ⟪_⟫₊ = map-args
  

{-------------------------------------------------------------------------------
  Fusion of two maps into a third

  fusion : ∀{s}{σ₁ : Env₁}{σ₂ : Env₂} {σ₃ : Env₃} (M : ABT)
     → σ₂ ∘ σ₁ ≈ σ₃
     → map₂ σ₂ (map₁ σ₁ M) ≡ map₃ σ₃ M
 ------------------------------------------------------------------------------}

_∘_≈_ : ∀ {V₁}{E₁}{V₂}{E₂}{V₃}{E₃}
        {{M₁ : MapEnv E₁ V₁}} {{M₂ : MapEnv E₂ V₂}} {{M₃ : MapEnv E₃ V₃}}
        (σ₂ : E₂)(σ₁ : E₁)(σ₃ : E₃) → Set
_∘_≈_ {V₁}{E₁}{V₂}{E₂}{V₃}{E₃}{{M₁}}{{M₂}}{{M₃}} σ₂ σ₁ σ₃ =
  ∀ x → map-abt σ₂ “ lookup σ₁ x ” ≡ “ lookup σ₃ x ”
  where 
  open MapEnv {{...}} 
  instance _ : MapEnv E₂ V₂ ; _ = M₂ ; _ : MapEnv E₁ V₁ ; _ = M₁
           _ : MapEnv E₃ V₃ ; _ = M₃

record FuseMapEnvMapEnv {V₁ Env₁ V₂ Env₂ V₃ Env₃}
  (M₁ : MapEnv Env₁ V₁ ) (M₂ : MapEnv Env₂ V₂) (M₃ : MapEnv Env₃ V₃) : Set
  where
  open MapEnv {{...}}
  instance _ : MapEnv Env₁ V₁ ; _ = M₁ ; _ : MapEnv Env₂ V₂ ; _ = M₂
           _ : MapEnv Env₃ V₃ ; _ = M₃

  open Shiftable (MapEnv.V-is-Shiftable M₁)
      using() renaming (var→val to var→val₁) 
  open Shiftable (MapEnv.V-is-Shiftable M₂)
      using() renaming (var→val to var→val₂) 
  open Shiftable (MapEnv.V-is-Shiftable M₃)
      using() renaming (var→val to var→val₃) 

  field compose-ext : ∀{σ₁ : Env₁}{σ₂ : Env₂}{σ₃ : Env₃}
                    → σ₂ ∘ σ₁ ≈ σ₃ → ext-env σ₂ ∘ ext-env σ₁ ≈ ext-env σ₃

  fusion : ∀{σ₁ : Env₁}{σ₂ : Env₂}{σ₃ : Env₃} (M : ABT)
     → σ₂ ∘ σ₁ ≈ σ₃
     → map-abt σ₂ (map-abt σ₁ M) ≡ map-abt σ₃ M
  fusion-arg : ∀{σ₁ : Env₁}{σ₂ : Env₂}{σ₃ : Env₃} {b} (arg : Arg b)
     → σ₂ ∘ σ₁ ≈ σ₃
     → map-arg σ₂ (map-arg σ₁ arg) ≡ map-arg σ₃ arg
  fusion-args : ∀{σ₁ : Env₁}{σ₂ : Env₂}{σ₃ : Env₃} {bs} (args : Args bs)
     → σ₂ ∘ σ₁ ≈ σ₃
     → map-args σ₂ (map-args σ₁ args) ≡ map-args σ₃ args

  fusion (` x) σ₂∘σ₁≈σ₃ = σ₂∘σ₁≈σ₃ x
  fusion (op ⦅ args ⦆) σ₂∘σ₁≈σ₃ = cong (_⦅_⦆ op) (fusion-args args σ₂∘σ₁≈σ₃)
  fusion-arg {b = zero} (ast M) σ₂∘σ₁≈σ₃ = cong ast (fusion M σ₂∘σ₁≈σ₃)
  fusion-arg {b = suc b} (bind arg) σ₂∘σ₁≈σ₃ =
      cong bind (fusion-arg arg (compose-ext σ₂∘σ₁≈σ₃))
  fusion-args {bs = []} nil σ₂∘σ₁≈σ₃ = refl
  fusion-args {bs = b ∷ bs} (cons arg args) σ₂∘σ₁≈σ₃ =
      cong₂ cons (fusion-arg arg σ₂∘σ₁≈σ₃) (fusion-args args σ₂∘σ₁≈σ₃)

  
record ComposableMaps {V₁ V₂ V₃} (M₁ : Map V₁) (M₂ : Map V₂) (M₃ : Map V₃) : Set
  where
  open Map {{...}}
  instance _ : Map V₁ ; _ = M₁ ; _ : Map V₂ ; _ = M₂ ; _ : Map V₃ ; _ = M₃
  open Quotable {{...}}
  instance _ : Quotable V₁ ; _ = V-is-Quotable
           _ : Quotable V₂ ; _ = V-is-Quotable
           _ : Quotable V₃ ; _ = V-is-Quotable
  open Shiftable (Map.V-is-Shiftable M₁) using() renaming (var→val to var→val₁) 

  field ⌈_⌉ : GSubst V₂ → V₁ → V₃
        val₂₃ : V₂ → V₃
        quote-map : ∀ σ₂ v₁ → “ ⌈ σ₂ ⌉ v₁ ” ≡ map-abt σ₂ “ v₁ ”
        var→val₂₃ : ∀ x → var→val x ≡ val₂₃ (var→val x)
        quote-val₂₃ : ∀ (v₂ : V₂) → “ val₂₃ v₂ ” ≡ “ v₂ ”
        quote-var→val₁ : ∀ x → “ var→val₁ x ” ≡ ` x
        val₂₃-shift : ∀ (v₂ : V₂) → val₂₃ (shift v₂) ≡ shift (val₂₃ v₂)

  open GSubstAux {{...}}
  instance _ : GSubstAux (Map.V-is-Shiftable M₁) ; _ = record { }
  instance _ : GSubstAux (Map.V-is-Shiftable M₂) ; _ = record { }
  instance _ : GSubstAux (Map.V-is-Shiftable M₃) ; _ = record { }
  open ComposeGSubst ⌈_⌉ val₂₃

  g-map-sub-⧼·⧽ : ∀{x : Var} (σ : GSubst V₂)
     → ⧼ map-sub val₂₃ σ ⧽ x ≡ val₂₃ (⧼ σ ⧽ x)
  g-map-sub-⧼·⧽ {x} (↑ k) = var→val₂₃ (k + x)
  g-map-sub-⧼·⧽ {zero} (v₂ • σ) = refl
  g-map-sub-⧼·⧽ {suc x} (v₂ • σ) = g-map-sub-⧼·⧽ {x} σ
  
  compose-sub : ∀ σ₁ σ₂ x → “ ⧼ σ₁ ⨟ σ₂ ⧽ x ” ≡ (map-abt σ₂ “ ⧼ σ₁ ⧽ x ”)
  compose-sub (↑ k) σ₂ x = begin
    “ ⧼ ↑ k ⨟ σ₂ ⧽ x ”                ≡⟨ cong (λ □ → “ ⧼ □ ⧽ x ”)  (up-seq _ _) ⟩
    “ ⧼ map-sub val₂₃ (drop k σ₂) ⧽ x ”
                         ≡⟨ cong (λ □ → “ ⧼ □ ⧽ x ”) (map-sub-drop σ₂ val₂₃ k) ⟩
    “ ⧼ drop k (map-sub val₂₃ σ₂) ⧽ x ”
                              ≡⟨ cong “_” (g-drop-add k (map-sub val₂₃ σ₂) x) ⟩
    “ ⧼ map-sub val₂₃ σ₂ ⧽ (k + x) ”            ≡⟨ cong “_” (g-map-sub-⧼·⧽ σ₂) ⟩
    “ val₂₃ (⧼ σ₂ ⧽ (k + x)) ”                 ≡⟨ quote-val₂₃ (⧼ σ₂ ⧽ (k + x)) ⟩
    “ ⧼ σ₂ ⧽ (k + x) ”                                                       ≡⟨⟩
    map-abt σ₂ (` (k + x))
                         ≡⟨ cong (map-abt σ₂) (sym (quote-var→val₁ (k + x)) ) ⟩
    map-abt σ₂ “ ⧼ ↑ k ⧽ x ”
    ∎
  compose-sub (v₁ • σ₁) σ₂ zero rewrite sym (quote-map σ₂ v₁)
      | cons-seq v₁ σ₁ σ₂ = refl
  compose-sub (v₁ • σ₁) σ₂ (suc x) rewrite cons-seq v₁ σ₁ σ₂
      | compose-sub σ₁ σ₂ x = refl

  g-drop-seq : ∀ k σ₁ σ₂ → drop k (σ₁ ⨟ σ₂) ≡ (drop k σ₁ ⨟ σ₂)
  g-drop-seq k (↑ k₁) σ₂ = begin
    drop k (↑ k₁ ⨟ σ₂)                    ≡⟨ cong (drop k) (up-seq _ _) ⟩
    drop k (map-sub val₂₃ (drop k₁ σ₂))
                                   ≡⟨  sym (map-sub-drop (drop k₁ σ₂) val₂₃ k) ⟩
    map-sub val₂₃ (drop k (drop k₁ σ₂))
                            ≡⟨  cong (map-sub val₂₃) (sym (drop-drop k k₁ σ₂)) ⟩
    map-sub val₂₃ (drop (k + k₁) σ₂)      ≡⟨ sym (up-seq _ σ₂) ⟩
    ↑ (k + k₁) ⨟ σ₂                       ∎
  g-drop-seq zero (x • σ₁) σ₂ rewrite cons-seq x σ₁ σ₂ = refl
  g-drop-seq (suc k) (x • σ₁) σ₂ rewrite cons-seq x σ₁ σ₂
      | g-drop-seq k σ₁ σ₂ = refl

  g-map-sub-inc : ∀ σ₂ → map-sub val₂₃ (g-inc σ₂) ≡  g-inc (map-sub val₂₃ σ₂)
  g-map-sub-inc (↑ k) = refl
  g-map-sub-inc (v₂ • σ₂) = cong₂ _•_ (val₂₃-shift v₂) (g-map-sub-inc σ₂)


{-------------------------------------------------------------------------------
  Fusion of two maps

  fusion : ∀{s}{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} (M : ABT)
     → map₂ σ₂ (map₁ σ₁ M) ≡ map₂ (σ₁ ⨟ σ₂) M
 ------------------------------------------------------------------------------}

record FuseMapMap {V₁ V₂ V₃} (M₁ : Map V₁) (M₂ : Map V₂) (M₃ : Map V₃) : Set
  where
  open Map {{...}}
  instance _ : Map V₁ ; _ = M₁ ; _ : Map V₂ ; _ = M₂ ; _ : Map V₃ ; _ = M₃
  
  field CompMap : ComposableMaps M₁ M₂ M₃
  open ComposableMaps CompMap
  open ComposeGSubst ⌈_⌉ val₂₃ public
  open GSubstAux {{...}}
  instance _ : GSubstAux (Map.V-is-Shiftable M₁) ; _ = record { }
           _ : GSubstAux (Map.V-is-Shiftable M₂) ; _ = record { }
           _ : GSubstAux (Map.V-is-Shiftable M₃) ; _ = record { }
  field var : ∀ x σ₁ σ₂ → ⌈ σ₂ ⌉ (⧼ σ₁ ⧽ x) ≡ ⧼ (σ₁ ⨟ σ₂) ⧽ x
        compose-ext : ∀ (σ₁ : GSubst V₁) (σ₂ : GSubst V₂)
                    → g-ext σ₁ ⨟ g-ext σ₂ ≡ g-ext (σ₁ ⨟ σ₂)

  fusion : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} (M : ABT)
     → map-abt σ₂ (map-abt σ₁ M) ≡ map-abt (σ₁ ⨟ σ₂) M
     
  fusion-arg : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} {b} (arg : Arg b)
     → map-arg σ₂ (map-arg σ₁ arg) ≡ map-arg (σ₁ ⨟ σ₂) arg
  fusion-args : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} {bs} (args : Args bs)
     → map-args σ₂ (map-args σ₁ args) ≡ map-args (σ₁ ⨟ σ₂) args

  fusion {σ₁} {σ₂} (` x)
      rewrite sym (quote-map σ₂ (⧼ σ₁ ⧽ x)) | var x σ₁ σ₂  = refl
  fusion {σ₁} {σ₂} (op ⦅ args ⦆) =
      cong (_⦅_⦆ op) (fusion-args args)
  fusion-arg {σ₁} {σ₂} {zero} (ast M) = cong ast (fusion M)
  fusion-arg {σ₁} {σ₂} {suc b} (bind arg) =
    cong bind H
    where
    IH = fusion-arg {g-ext σ₁} {g-ext σ₂} {b} arg
    H = begin
        map-arg (ext-env σ₂) (map-arg (ext-env σ₁) arg)
          ≡⟨ cong (λ □ → map-arg □ (map-arg (ext-env σ₁) arg))
                  (ext-env-g-ext σ₂) ⟩
        map-arg (g-ext σ₂) (map-arg (ext-env σ₁) arg)
          ≡⟨ cong (λ □ → map-arg (g-ext σ₂) (map-arg □ arg)) (ext-env-g-ext σ₁)⟩
        map-arg (g-ext σ₂) (map-arg (g-ext σ₁) arg)   ≡⟨ IH ⟩
        map-arg (g-ext σ₁ ⨟ g-ext σ₂) arg
                            ≡⟨ cong (λ □ → map-arg □ arg) (compose-ext σ₁ σ₂) ⟩
        map-arg (g-ext (σ₁ ⨟ σ₂)) arg
            ≡⟨ cong (λ □ → map-arg □ arg) (sym (ext-env-g-ext _)) ⟩
        map-arg (ext-env (σ₁ ⨟ σ₂)) arg                 ∎
  fusion-args {σ₁} {σ₂} {[]} nil = refl
  fusion-args {σ₁} {σ₂} {b ∷ bs} (cons arg args) =
      cong₂ cons (fusion-arg arg) (fusion-args args)

{-------------------------------------------------------------------------------
  Congruence of map

  map-cong-abt : ∀{s}{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} 
      → σ₁ ≈ σ₂ → (M : Term s) → map₁ σ₁ M ≡ map₂ σ₂ M

  todo: generalize to simulation of maps
 ------------------------------------------------------------------------------}
 
record MapCong {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂) : Set₁ where
  open Map {{...}}
  instance _ : Map V₁ ; _ = M₁ ; _ : Map V₂ ; _ = M₂
  open Quotable {{...}}
  instance _ : Quotable V₁ ; _ = V-is-Quotable
           _ : Quotable V₂ ; _ = V-is-Quotable
  open GSubstAux {{...}}
  instance _ : GSubstAux (Map.V-is-Shiftable M₁) ; _ = record { }
           _ : GSubstAux (Map.V-is-Shiftable M₂) ; _ = record { }

  field _≈_ : GSubst V₁ → GSubst V₂ → Set
        var : ∀ {σ₁ σ₂} x → σ₁ ≈ σ₂ → “ ⧼ σ₁ ⧽ x ” ≡ “ ⧼ σ₂ ⧽ x ”
        ext≈ : ∀ {σ₁ σ₂} → σ₁ ≈ σ₂ → g-ext σ₁ ≈ g-ext σ₂
        
  map-cong-abt : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} 
      → σ₁ ≈ σ₂ → (M : ABT) → map-abt σ₁ M ≡ map-abt σ₂ M

  map-cong-arg : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} {b : ℕ}
      → σ₁ ≈ σ₂ → (arg : Arg b) → map-arg σ₁ arg ≡ map-arg σ₂ arg
  map-cong-args : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} {bs : List ℕ}
      → σ₁ ≈ σ₂ → (args : Args bs) → map-args σ₁ args ≡ map-args σ₂ args

  map-cong-abt {σ₁} {σ₂} σ₁≈σ₂ (` x) = var x σ₁≈σ₂
  map-cong-abt {σ₁} {σ₂} σ₁≈σ₂ (op ⦅ args ⦆) =
      cong (_⦅_⦆ op) (map-cong-args σ₁≈σ₂ args)
  map-cong-arg {σ₁} {σ₂} {zero} σ₁≈σ₂ (ast arg) =
      cong ast (map-cong-abt σ₁≈σ₂ arg)
  map-cong-arg {σ₁} {σ₂} {suc b} σ₁≈σ₂ (bind arg) 
      with (map-cong-arg {g-ext σ₁} {g-ext σ₂} {b} (ext≈ σ₁≈σ₂) arg)
  ... | IH rewrite sym (ext-env-g-ext σ₁) | sym (ext-env-g-ext σ₂) =
      cong bind IH
  map-cong-args {σ₁} {σ₂} {[]} σ₁≈σ₂ nil = refl
  map-cong-args {σ₁} {σ₂} {b ∷ bs} σ₁≈σ₂ (cons arg args) =
      cong₂ cons (map-cong-arg σ₁≈σ₂ arg) (map-cong-args σ₁≈σ₂ args)


record MapCong≊ {V₁ V₂} (M₁ : Map V₁) (M₂ : Map V₂) : Set₁ where
  open Map {{...}}
  instance _ : Map V₁ ; _ = M₁ ; _ : Map V₂ ; _ = M₂
  open Quotable {{...}}
  instance _ : Quotable V₁ ; _ = V-is-Quotable
           _ : Quotable V₂ ; _ = V-is-Quotable

  _∼_ = λ (v₁ : V₁) (v₂ : V₂) → “ v₁ ” ≡ “ v₂ ”
  field var→val-quote : (x : ℕ) → “ var→val x ” ≡ “ var→val x ”
        shift-quote : ∀{v₁ : V₁}{v₂ : V₂} → “ v₁ ” ≡ “ v₂ ”
                    → “ shift v₁ ” ≡ “ shift v₂ ”
  module R = Relate {V₁}{V₂} (Map.V-is-Shiftable M₁) (Map.V-is-Shiftable M₂)
      _∼_ var→val-quote shift-quote
  open R renaming (_≊_ to _≈_; g-ext-≊ to ext≈; g-lookup to lookup-≡)

  MC : MapCong M₁ M₂
  MC = record { _≈_ = _≈_ ; var = lookup-≡ ; ext≈ = ext≈ }
  open MapCong MC public


