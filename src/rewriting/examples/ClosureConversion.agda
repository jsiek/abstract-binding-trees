{-# OPTIONS --without-K --rewriting #-}
{-
  This is a language without lexical scoping, but otherwise similar to the lambda calculus.
-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Sig
open import Var
open import rewriting.examples.Denot
open import rewriting.examples.Gamma
  renaming (Term to Term₁; $ to $₁; _·_ to _·₁_;
            ⟨_,_⟩ to ⟨_,_⟩₁; fst to fst₁; snd to snd₁;
            ⟦_⟧ to ⟦_⟧₁)
open import rewriting.examples.Delta
  using (δ)
  renaming (Term to Term₂; $ to $₂; _·_ to _·₂_;
            ⟨_,_⟩ to ⟨_,_⟩₂; fst to fst₂; snd to snd₂;
            `_ to `₂_; ⟦_⟧ to ⟦_⟧₂)
{-
open import Data.List.Membership.DecPropositional _≟_
-}

module rewriting.examples.ClosureConversion where

{- Closure Conversion -}
C : Term₁ → Term₂
C (` x) = `₂ x
C ($₁ k) = $₂ k
C (γ N M) = ⟨ δ (C N) , C M ⟩₂
C (L ·₁ M) = ((fst₂ (C L)) ·₂ snd₂ (C L)) ·₂ (C M)
C ⟨ L , M ⟩₁ = ⟨ C L , C M ⟩₂
C (fst₁ L) = fst₂ (C L)
C (snd₁ L) = snd₂ (C L)

continuous₂ : ∀ N {D ρ d} → ⟦ N ⟧₂ (D ∷ ρ) d → ∃[ V ] ⟦ N ⟧₂ ((_∈ V) ∷ ρ) d
continuous₂ N {D}{ρ}{d} = {!!}

data _≈_ : List Val → List Val → Set

data _∼_ : Val → Val → Set where
  lit-rel : ∀ {k}
     → lit k ∼ lit k
  fun-rel : ∀ {V V′ V″ w w′ F}
     → w ∼ w′
     → V ≈ V″
     → V′ ↦ (V″ ↦ w′) ∈ F
     → (V ↦ w) ∼ pair F V′

data _≈_ where
  ≈-nil : [] ≈ []
  ≈-cons : ∀ {v w}{vs ws}
    → v ∼ w
    → vs ≈ ws
    → (v ∷ vs) ≈ (w ∷ ws)
  
C-fwd : ∀ M ρ d₁ → ⟦ M ⟧₁ ρ d₁ → ∃[ d₂ ] ⟦ C M ⟧₂ ρ d₂ × d₁ ∼ d₂
C-fwd (` x) ρ d₁ d₁∈M = {!!} , ({!!} , {!!})
C-fwd ($₁ k) ρ d₁ refl = (lit k) , refl , {!!}
C-fwd (γ N M) ρ (V ↦ w) ((d , d∈M) , w∈⟦N⟧) 
    with C-fwd M ρ d d∈M
... | d′ , d′∈CM , ∼d′
    with C-fwd N (⟦ M ⟧₁ ρ ∷ (_∈ V) ∷ []) w w∈⟦N⟧
... | d₂ , d₂∈CN , ∼d₂
    with continuous₂ (C N) d₂∈CN
... | V′ , d₂∈CN′ = 
    (pair ({!!} ↦ ({!!} ↦ d₂) ∷ []) {!!}) ,
      (({!!} , {!!}) , fun-rel ∼d₂ {!!} (here refl))
C-fwd (L ·₁ M) ρ w ((v , v∈M) , (V , (Vw∈L , v∈V→v∈M)))
    with C-fwd L ρ (V ↦ w) Vw∈L
... | d′ , d′∈CL , fun-rel {F = F} w∼w′ V≈V″ ∈F =
    w′ , (neCM , (V′ , ((({!!} , ({!!} , ({!!} , (d′∈CL , {!!})))) ,
         ({!!} , (({!!} , ({!!} , (d′∈CL , {!!}))) , {!!}))) , {!!}))) ,
         w∼w′
{-    
    w′ , ((neCM , V′ , ((neπ₂CL , V″ , VVw∈π₁CL , V″⊆π₂CL) , V′⊆CM)) , w∼w′)
-}
    where
     neCM : ∃[ v ] ⟦ (C M) ⟧₂ ρ v
     neCM = {!!}

     V′ : List Val
     V′ = {!!}
     
     w′ : Val
     w′ = {!!}

     V′⊆CM : ∀ v₁ → v₁ ∈ V′ → ⟦ C M ⟧₂ ρ v₁
     V′⊆CM = {!!}

     neπ₂CL : ∃[ v ] π₂ (⟦ C L ⟧₂ ρ) v
     neπ₂CL = _ , (_ , {!!})

     V″ : List Val
     V″ = {!!}

     p₂ : Val
     p₂ = {!!}

     ∈CL : ⟦ C L ⟧₂ ρ (pair F _)
     ∈CL = d′∈CL

     VVw∈π₁CL : π₁ (⟦ C L ⟧₂ ρ) (V″ ↦ (V′ ↦ w′))
     VVw∈π₁CL = {!!} , {!!}

     V″⊆π₂CL : ∀ v₁ → v₁ ∈ V″ → π₂ (⟦ C L ⟧₂ ρ) v₁
     V″⊆π₂CL v₁ v₁∈V″ = {!!} , {!!}

C-fwd ⟨ L , M ⟩₁ ρ d₁ d₁∈M = {!!}
C-fwd (fst₁ L) ρ d₁ d₁∈M = {!!}
C-fwd (snd₁ L) ρ d₁ d₁∈M = {!!}
