{-# OPTIONS --without-K #-}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _≟_)
open import Sig

module Map3 (Op : Set) (sig : Op → List Sig) where

open import Var
open import AbstractBindingTree Op sig
open import GSubst using (GSubst; _•_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)

record Syntactic {ℓ} (V : Set ℓ) : Set ℓ where
  field ⇑ : V → V
        trm : V → ABT
        ze : V
        trm_ze : trm ze ≡ ` 0
open Syntactic {{...}} public

instance
  Var-is-Syntactic : Syntactic Var
  Var-is-Syntactic = record { ⇑ = suc ; trm = `_ ; ze = 0 ; trm_ze = refl }


map : ∀{ℓ}{V : Set ℓ}{{_ : Syntactic V}}
   → GSubst V → ABT → ABT
map-arg : ∀{ℓ}{V : Set ℓ}{{_ : Syntactic V}}
   → GSubst V → {b : Sig} →  Arg b → Arg b
map-args : ∀{ℓ}{V : Set ℓ}{{_ : Syntactic V}}
   → GSubst V → {bs : List Sig} →  Args bs → Args bs

map σ (` x) = trm (σ x)
map {V} σ (op ⦅ args ⦆) = op ⦅ map-args σ args ⦆
map-arg σ (ast M) = ast (map σ M)
map-arg σ (bind M) = bind (map-arg (ze • λ x → ⇑ (σ x)) M)
map-arg σ (clear M) = clear M
map-args σ {[]} nil = nil
map-args σ {b ∷ bs} (cons x args) = cons (map-arg σ x) (map-args σ args)

instance
  ABT-is-Syntactic : Syntactic ABT
  ABT-is-Syntactic = record {⇑ = map suc ; trm = λ M → M ; ze = ` 0
                            ; trm_ze = refl}


map-cong : ∀{ℓ}{V : Set ℓ} {{_ : Syntactic V}}
  (σ₁ σ₂ : GSubst V)
  → (M : ABT)
  → (∀ x → σ₁ x ≡ σ₂ x)
  → map σ₁ M ≡ map σ₂ M

map-cong-arg : ∀{ℓ}{V : Set ℓ}{b}
  {{_ : Syntactic V}}
  (σ₁ σ₂ : GSubst V)
  → (arg : Arg b)
  → (∀ x → σ₁ x ≡ σ₂ x)
  → map-arg σ₁ arg ≡ map-arg σ₂ arg

map-cong-args : ∀{ℓ}{V : Set ℓ}{bs}
  {{_ : Syntactic V}}
  (σ₁ σ₂ : GSubst V)
  → (args : Args bs)
  → (∀ x → σ₁ x ≡ σ₂ x)
  → map-args σ₁ args ≡ map-args σ₂ args

map-cong σ₁ σ₂ (` x) eq = cong trm (eq x)  
map-cong σ₁ σ₂ (op ⦅ args ⦆) eq =
   cong (_⦅_⦆ op) (map-cong-args σ₁ σ₂ args eq)  

map-cong-arg σ₁ σ₂ (ast M) eq = cong ast (map-cong σ₁ σ₂ M eq)
map-cong-arg σ₁ σ₂ (bind arg) eq =
  cong bind IH
  where
   σ₁′ = (ze • λ x → ⇑ (σ₁ x)) 
   σ₂′ = (ze • λ x → ⇑ (σ₂ x))
   σ₁′≡σ₂′ : (x : Var) → σ₁′ x ≡ σ₂′ x
   σ₁′≡σ₂′ zero = refl
   σ₁′≡σ₂′ (suc x) = cong ⇑ (eq x)
   IH : map-arg σ₁′ arg ≡ map-arg σ₂′ arg
   IH = map-cong-arg σ₁′ σ₂′ arg σ₁′≡σ₂′
map-cong-arg σ₁ σ₂ (clear arg) eq = refl

map-cong-args σ₁ σ₂ nil eq = refl  
map-cong-args σ₁ σ₂ (cons arg args) eq =
   cong₂ cons (map-cong-arg σ₁ σ₂ arg eq) (map-cong-args σ₁ σ₂ args eq)  

{-
trm_shift :
  trm (⇑ v) = map suc (trm v)
-}
rename-map-fusion : ∀{ℓ}{V : Set ℓ}{{_ : Syntactic V}} 
     (σ : GSubst V)
   → (M : ABT)
   → map suc (map σ M) ≡ map (λ x → trm (⇑ (σ x))) M
rename-map-fusion σ M = {!!}  

map-map-fusion : ∀{ℓ}{V₁ V₂ : Set ℓ}
  {{_ : Syntactic V₁}} {{_ : Syntactic V₂}}
  (σ₁ : GSubst V₁)(σ₂ : GSubst V₂)
   → (M : ABT)
  → map σ₂ (map σ₁ M) ≡ map (λ x → map σ₂ (trm (σ₁ x))) M

map-map-fusion-arg : ∀{ℓ}{V₁ V₂ : Set ℓ}{b}
  {{_ : Syntactic V₁}} {{_ : Syntactic V₂}}
  (σ₁ : GSubst V₁)(σ₂ : GSubst V₂)
   → (arg : Arg b)
  → map-arg σ₂ (map-arg σ₁ arg) ≡ map-arg (λ x → map σ₂ (trm (σ₁ x))) arg

map-map-fusion-args : ∀{ℓ}{V₁ V₂ : Set ℓ}{bs}
  {{_ : Syntactic V₁}} {{_ : Syntactic V₂}}
  (σ₁ : GSubst V₁)(σ₂ : GSubst V₂)
   → (args : Args bs)
  → map-args σ₂ (map-args σ₁ args) ≡ map-args (λ x → map σ₂ (trm (σ₁ x))) args

map-map-fusion σ₁ σ₂ (` x) = refl  
map-map-fusion σ₁ σ₂ (op ⦅ args ⦆) =
   cong (_⦅_⦆ op) (map-map-fusion-args σ₁ σ₂ args) 

map-map-fusion-arg σ₁ σ₂ (ast M) = cong ast (map-map-fusion σ₁ σ₂ M) 
map-map-fusion-arg{ℓ}{V₁}{V₂} {{S₁}}{{S₂}} σ₁ σ₂ (bind arg) =
   cong bind (trans IH NTS)
   where
   σ₁′ = (ze • λ x → ⇑ (σ₁ x)) 
   σ₂′ = (ze • λ x → ⇑ (σ₂ x)) 
   IH : map-arg σ₂′ (map-arg σ₁′ arg)
      ≡ map-arg (λ x → map σ₂′ (trm (σ₁′ x))) arg
   IH = map-map-fusion-arg σ₁′ σ₂′ arg

   Goal : (x : Var) → map σ₂′ (trm (σ₁′ x))
                    ≡ ((` 0) • (λ x₁ → map suc (map σ₂ (trm (σ₁ x₁))))) x
   Goal zero = G
       where
       G : map σ₂′ (Syntactic.trm S₁ (Syntactic.ze S₁)) ≡ ` 0
       G rewrite Syntactic.trm_ze S₁ | Syntactic.trm_ze S₂ = refl
   Goal (suc x) =
     let IH : map σ₂′ (trm (σ₁′ x))
               ≡ ((` 0) • (λ x₁ → map suc (map σ₂ (trm (σ₁ x₁))))) x
         IH = Goal x in
     let
         EQ = sym (rename-map-fusion σ₂ (trm (⇑ (σ₁ x))))
     in
     {!!}
     where
     
     H : map σ₂′ (trm (⇑ (σ₁ x)))
         ≡ map suc (map σ₂ (trm (σ₁ x)))
     H = {!!}
{-
     map suc (map σ₂ (trm v₁))
         ≡ map (ze • λ x → ⇑ (σ₂ x)) (trm (⇑ v₁))
-}

   NTS : map-arg (λ x → map σ₂′ (trm (σ₁′ x))) arg
       ≡ map-arg ((` 0) • (λ x → map suc (map σ₂ (trm (σ₁ x))))) arg
   NTS = map-cong-arg (λ x → map σ₂′ (trm (σ₁′ x)))
          (((` 0) • (λ x₁ → map suc (map σ₂ (trm (σ₁ x₁)))))) arg Goal

map-map-fusion-arg σ₁ σ₂ (clear arg) = refl

map-map-fusion-args σ₁ σ₂ nil = refl
map-map-fusion-args σ₁ σ₂ (cons arg args) =
   cong₂ cons (map-map-fusion-arg σ₁ σ₂ arg) (map-map-fusion-args σ₁ σ₂ args)
