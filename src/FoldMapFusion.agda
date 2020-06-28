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
open import Renaming
open Renaming.WithOpSig Op sig
open import Map Op sig using (map; map-arg; map-args)
open import Fold Op sig
open Shiftable {{...}}
open Env {{...}}
open Quotable {{...}}
open Foldable {{...}}

{-------------------- Fusion of fold and map   ---------------------}

_⨟_≈_ : ∀{ℓᶠ ℓᵐ} {Vᵐ Eᵐ : Set ℓᵐ}{Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
    {{_ : Shiftable Vᵐ}} {{_ : Env Eᵐ Vᵐ}} {{_ : Quotable Vᵐ}}
    {{_ : Shiftable Vᶠ}} {{_ : Env Eᶠ Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
    → Eᵐ → Eᶠ → Eᶠ → Set ℓᶠ
σ ⨟ δ ≈ γ = ∀ x → fold δ (“ ⟅ σ ⟆ x ”) ≡ ret (⟅ γ ⟆ x)

module _ where
  private
   instance
     ≡-RelFold : ∀{ℓ}{V : Set ℓ}{C : Set ℓ} → RelFold V V C C
     ≡-RelFold {ℓ} = record { _∼_ = _≡_ ; _≈_ = _≡_ }

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
        → RelFold V V C C
     ≡⇑-RelFold {ℓ} = record { _∼_ = (λ v v' → v ≡ ⇑ v')
                             ; _≈_ = (λ c c' → c ≡ ⇑ c') }

  fold-shift : ∀ {ℓ : Level}{Vᶠ Eᶠ Cᶠ : Set ℓ}
     {{_ : Shiftable Vᶠ}} {{_ : Env Eᶠ Vᶠ}} {{_ : Foldable Vᶠ Cᶠ}}
     {{_ : Shiftable Cᶠ}}
     (δ δ↑ : Eᶠ)
     (M : ABT)
     → (∀ x → ⟅ δ↑ ⟆ x ≡ ⇑ (⟅ δ ⟆ x))
     → (∀ op {rs↑ rs : Tuple (sig op) (Bind Vᶠ Cᶠ)}
          → zip (_⩳_{ℓ}{ℓ}{Vᶠ}{Vᶠ}{Cᶠ}{Cᶠ}) rs↑ rs
          → fold-op op rs↑ ≡ ⇑ (fold-op op rs))
     → (∀ (v : Vᶠ) → ⇑ (ret v) ≡ ret (⇑ v))
     → fold δ↑ M ≡ ⇑ (fold δ M)
  fold-shift δ δ↑ (` x) δ=shift op-shift shift-ret rewrite (δ=shift x)
      | shift-ret (⟅ δ ⟆ x) = refl
  fold-shift{ℓ}{Vᶠ}{Eᶠ}{Cᶠ} δ δ↑ (op ⦅ args ⦆) δ=shift op-shift shift-ret =
      op-shift op (fold-shift-args δ δ↑ args δ=shift)
      where
      fold-shift-arg : ∀ (δ δ↑ : Eᶠ) {b} (arg : Arg b)
          → (∀ x → ⟅ δ↑ ⟆ x ≡ ⇑ (⟅ δ ⟆ x))
          → fold-arg δ↑ arg ⩳ fold-arg δ arg
      fold-shift-args : ∀ (δ δ↑ : Eᶠ) {bs} (args : Args bs)
          → (∀ x → ⟅ δ↑ ⟆ x ≡ ⇑ (⟅ δ ⟆ x))
          → zip _⩳_ (fold-args δ↑ args) (fold-args δ args)
      fold-shift-arg δ δ↑ (ast M) δ=shift =
          fold-shift δ δ↑ M δ=shift op-shift shift-ret
      fold-shift-arg δ δ↑ (bind arg) δ=shift {_}{v} refl =
          fold-shift-arg (δ , v) (δ↑ , ⇑ v) arg G 
          where
          G : ∀ x → ⟅ δ↑ , ⇑ v ⟆ x ≡ ⇑ (⟅ δ , v ⟆ x)
          G zero rewrite lookup-0 δ↑ (⇑ v) | lookup-0 δ v = refl
          G (suc x) rewrite lookup-suc δ v x | lookup-suc δ↑ (⇑ v) x =
              cong ⇑ (δ=shift x)
      fold-shift-args δ δ↑ nil δ=shift = tt
      fold-shift-args δ δ↑ (cons arg args) δ=shift =
          ⟨ fold-shift-arg δ δ↑ arg δ=shift ,
            fold-shift-args δ δ↑ args δ=shift ⟩


{-
record FuseFoldEnvMapEnv  {Vᵐ Vᶠ Envᵐ Eᶠ : Set} {ℓ : Level}{Cᶠ : Set ℓ}
  (M : MapEnv Envᵐ Vᵐ) (F : FoldEnv Eᶠ Vᶠ Cᶠ) : Set (lsuc ℓ)
  where
  open MapEnv {{...}} renaming (lookup to lookupᵐ; ext-env to ext-envᵐ)
  open FoldEnv {{...}} renaming (_,_ to _,ᶠ_) 
  instance _ : MapEnv Envᵐ Vᵐ ; _ = M ; _ : FoldEnv Eᶠ Vᶠ Cᶠ ; _ = F
           
  open RelBind {ℓ}{Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ} _≡_ _≡_

  _⨟_≈_ : Envᵐ → Eᶠ → Eᶠ → Set ℓ
  σ ⨟ δ ≈ γ = ∀ x → fold δ (“ lookupᵐ σ x ”) ≡ ret (lookup γ x)

  field op-cong : ∀ op rs rs' → zip _⩳_ rs rs' → fold-op op rs ≡ fold-op op rs'
        ext-pres : ∀{σ : Envᵐ}{δ γ : Eᶠ}{v : Vᶠ} → σ ⨟ δ ≈ γ
                → (ext-envᵐ σ) ⨟ (δ ,ᶠ v) ≈ (γ ,ᶠ v)

  fusion : ∀{σ δ γ} (M : ABT)
     → σ ⨟ δ ≈ γ
     → fold δ (map-abt σ M)  ≡ fold γ M

  fuse-arg : ∀{b}{arg : Arg b}{σ δ γ}
     → σ ⨟ δ ≈ γ
     → fold-arg δ (map-arg σ arg) ⩳ fold-arg γ arg
  fuse-args : ∀{bs}{args : Args bs}{σ δ γ}
     → σ ⨟ δ ≈ γ
     → zip _⩳_ (fold-args δ (map-args σ args)) (fold-args γ args)
  fusion {σ} {δ} {γ} (` x) σ⨟δ≈γ = σ⨟δ≈γ x
  fusion {σ} {δ} {γ} (op ⦅ args ⦆) σ⨟δ≈γ =
      let mpf = (fuse-args {sig op}{args}{σ}{δ}{γ} σ⨟δ≈γ) in
      op-cong op (fold-args δ (map-args σ args)) (fold-args γ args) mpf
  fuse-arg {zero} {ast M} {σ} {δ} {γ} σ⨟δ≈γ =
      fusion M σ⨟δ≈γ
  fuse-arg {suc b} {bind arg} {σ} {δ} {γ} σ⨟δ≈γ refl =
      fuse-arg {b}{arg} (ext-pres σ⨟δ≈γ)
  fuse-args {[]} {nil} {σ} {δ} {γ} σ⨟δ≈γ = tt
  fuse-args {b ∷ bs} {cons arg args} {σ} {δ} {γ} σ⨟δ≈γ =
      ⟨ fuse-arg{b}{arg}{σ}{δ}{γ} σ⨟δ≈γ , fuse-args σ⨟δ≈γ ⟩

{-------------------- Fuse FoldEnv and Rename ---------------------}

record FuseFoldEnvRename {Env V : Set} {ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Env V C) : Set (lsuc ℓ) where
  open FoldEnv F
  open GenericSubst Var-is-Shiftable using (GSubst-is-Env; g-inc-shift)
  open Substitution using (Rename; ⟅_⟆; ext; ext-0; ext-suc)
  open Substitution.ABTOps Op sig
      using (rename; ren-arg; ren-args; Rename-is-Map)

  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_
  field op-eq : ∀ op rs rs' → zip _⩳_ rs rs' → fold-op op rs ≡ fold-op op rs'
        shiftᶜ : C → C
        shift-ret : ∀ v → shiftᶜ (ret v) ≡ ret (shift v)

  _⨟_≈_ : Rename → Env → Env → Set ℓ
  ρ ⨟ σ₁ ≈ σ₂ = ∀ x → fold σ₁ (` (⟅ ρ ⟆ x)) ≡ ret (lookup σ₂ x)
  
  ext-pres : ∀{ρ σ₁ σ₂ v} → ρ ⨟ σ₁ ≈ σ₂ → Env.ext-env GSubst-is-Env ρ ⨟ (σ₁ , v) ≈ (σ₂ , v)
  ext-pres {ρ} {σ₁} {σ₂} {v} prem zero rewrite ext-0 ρ
      | lookup-0 σ₁ v | lookup-0 σ₂ v = refl
  ext-pres {ρ} {σ₁} {σ₂} {v} prem (suc x) rewrite lookup-suc σ₂ v x
      | g-inc-shift ρ x | lookup-suc σ₁ v (⟅ ρ ⟆ x) =
      begin
          ret (shift (lookup σ₁ (⟅ ρ ⟆ x)))
      ≡⟨ sym (shift-ret _) ⟩
          shiftᶜ (ret (lookup σ₁ (⟅ ρ ⟆ x)))
      ≡⟨ cong shiftᶜ (prem x) ⟩
          shiftᶜ (ret (lookup σ₂ x))
      ≡⟨ shift-ret _ ⟩
          ret (shift (lookup σ₂ x))
      ∎

  MEPFE : FuseFoldEnvMapEnv{Var}{V}{ℓ = ℓ}{Cᶠ = C} (Map.GSubst-is-MapEnv Rename-is-Map) F
  MEPFE = record { op-cong = op-eq ; ext-pres = ext-pres }
  open FuseFoldEnvMapEnv MEPFE using ()
    renaming (fusion to rename-fold;
              fuse-arg to rf-arg; fuse-args to rf-args) public


{-------------------- Fuse Fold and Rename ---------------------}

record FuseFoldRename {V : Set} {ℓ : Level}{C : Set ℓ} (F : Fold V C) : Set (lsuc ℓ)
  where
  open Fold F
  
  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_
  field op-eq : ∀ op rs rs' → zip _⩳_ rs rs' → fold-op op rs ≡ fold-op op rs'
        ret-inj : ∀ {v v' : V} → ret v ≡ ret v' → v ≡ v'
        shiftᶜ : C → C
        shift-ret : ∀ v → shiftᶜ (ret v) ≡ ret (shift v)

  RPFE : FuseFoldEnvRename GSubst-is-FoldEnv
  RPFE = record { op-eq = op-eq ; shiftᶜ = shiftᶜ ; shift-ret = shift-ret }
  open FuseFoldEnvRename RPFE public


{-------------------- Fuse FoldEnv and Map ---------------------}

{- 
   example: Fold is denotational semantics, V₂ = Value, C₂ = Value → Set
            Map is substitution, V₁ = ABT

       Env = Var → Value
       Denotation : Env → Value → Set

  _`⊢_↓_ : Env → Subst → Env → Set
  _`⊢_↓_ δ σ γ = (∀ (x : Var) → ℰ (⟦ σ ⟧ x) δ (γ x))

    subst-pres : ∀ {v} {γ : Env} {δ : Env} {M : Term}
      → (σ : Subst)  →  δ `⊢ σ ↓ γ  →  ℰ M γ v
      → ℰ (⟪ σ ⟫ M) δ v

-}

{-
  Can FoldShift be proved via simulation?
-}
record FoldShift {Eᶠ Vᶠ : Set}{ℓ : Level}{Cᶠ : Set ℓ}
  (F : FoldEnv Eᶠ Vᶠ Cᶠ) : Set (lsuc ℓ) where
  open FoldEnv F

  field shiftᶜ : Cᶠ → Cᶠ
        shift-ret : ∀ vᶠ → shiftᶜ (ret vᶠ) ≡ ret (shift vᶠ)
        
  open RelBind {ℓ}{Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ}
           (λ v v' → v ≡ shift v') (λ c c' → c ≡ shiftᶜ c')
  
  field op-shift : ∀ op {rs↑ rs} → zip _⩳_ rs↑ rs
                 → fold-op op rs↑ ≡ shiftᶜ (fold-op op rs)

  fold-shift : ∀ δ δ↑ M
      → (∀ x → lookup δ↑ x ≡ shift (lookup δ x))
      → fold δ↑ M ≡ shiftᶜ (fold δ M)
  fold-shift-arg : ∀ δ δ↑ {b} (arg : Arg b)
      → (∀ x → lookup δ↑ x ≡ shift (lookup δ x))
      → fold-arg δ↑ arg ⩳ fold-arg δ arg
  fold-shift-args : ∀ (δ : Eᶠ) (δ↑ : Eᶠ) {bs} (args : Args bs)
      → (∀ x → lookup δ↑ x ≡ shift (lookup δ x))
      → zip _⩳_ (fold-args δ↑ args) (fold-args δ args)

  fold-shift δ δ↑ (` x) δ=shift rewrite (δ=shift x)
      | shift-ret (lookup δ x) = refl
  fold-shift δ δ↑ (op ⦅ args ⦆) δ=shift =
      op-shift op (fold-shift-args δ δ↑ args δ=shift)
  fold-shift-arg δ δ↑ (ast M) δ=shift = fold-shift δ δ↑ M δ=shift
  fold-shift-arg δ δ↑ (bind arg) δ=shift {_}{vᶠ} refl =
      fold-shift-arg (δ , vᶠ) (δ↑ , shift vᶠ) arg G
      where
      G : ∀ x → lookup (δ↑ , shift vᶠ) x ≡ shift (lookup (δ , vᶠ) x)
      G zero rewrite lookup-0 δ↑ (shift vᶠ) | lookup-0 δ vᶠ = refl
      G (suc x) rewrite lookup-suc δ vᶠ x | lookup-suc δ↑ (shift vᶠ) x =
          cong shift (δ=shift x)
  fold-shift-args δ δ↑ nil δ=shift = tt
  fold-shift-args δ δ↑ (cons arg args) δ=shift =
      ⟨ fold-shift-arg δ δ↑ arg δ=shift , fold-shift-args δ δ↑ args δ=shift ⟩


record FuseFoldEnvMap {Eᶠ Vᵐ Vᶠ : Set}{ℓ : Level}{Cᶠ : Set ℓ}
  (M : Map Vᵐ) (F : FoldEnv Eᶠ Vᶠ Cᶠ) : Set (lsuc ℓ) where
  open Map {{...}} using (V-is-Quotable; GSubst-is-MapEnv; ext-env)
  open FoldEnv {{...}} using (fold; ret; fold-op; lookup; lookup-0; lookup-suc;
      _,_; shift-env; lookup-shift)
  open Shiftable {{...}}
  open Quotable {{...}}
  instance _ : Map Vᵐ ; _ = M ; _ : FoldEnv Eᶠ Vᶠ Cᶠ ; _ = F
           _ : Shiftable Vᶠ ; _ = (FoldEnv.V-is-Shiftable F)
           _ : Shiftable Vᵐ ; _ = (Map.V-is-Shiftable M)
           _ : Quotable Vᵐ ; _ = V-is-Quotable
  open Shiftable (Map.V-is-Shiftable M) using () renaming (var→val to var→valᵐ) 
  
  open Substitution.ABTOps Op sig
      using (rename; ren-arg; ren-args; Rename-is-Map)

  field shiftᶜ : Cᶠ → Cᶠ

  open RelBind {ℓ}{Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ} _≡_ _≡_ renaming (_⩳_ to _⩳ᶠ_)
  open RelBind {ℓ}{Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ}
           (λ (v v' : Vᶠ) → v ≡ shift v') (λ c c' → c ≡ shiftᶜ c') public
           
  field op-cong : ∀ op rs rs' → zip _⩳ᶠ_ rs rs'
                → fold-op op rs ≡ fold-op op rs'
        var→val-“” : ∀ x → “ var→valᵐ x ” ≡ ` x
        shift-“” : ∀ (vᵐ : Vᵐ) → “ shift vᵐ ” ≡ rename (↑ 1) “ vᵐ ”
        shift-ret : ∀ (vᶠ : Vᶠ) → shiftᶜ (ret vᶠ) ≡ ret (shift vᶠ)
        op-shift : ∀ op {rs↑ rs} → zip _⩳_ rs↑ rs
                 → fold-op op rs↑ ≡ shiftᶜ (fold-op op rs)

  FS : FoldShift F
  FS = record { shiftᶜ = shiftᶜ ; shift-ret = shift-ret ; op-shift = op-shift }
  open FoldShift FS using (fold-shift)  

  RPF : FuseFoldEnvRename F
  RPF = record { op-eq = op-cong ; shiftᶜ = shiftᶜ ; shift-ret = shift-ret }
  open FuseFoldEnvRename RPF using (rename-fold)

  open GSubstAux {{...}}
  instance _ : GSubstAux {Vᵐ} (Map.V-is-Shiftable M) ; _ = record {}

  _⨟_≈_ : GSubst Vᵐ → Eᶠ → Eᶠ → Set ℓ
  σ ⨟ δ ≈ γ = ∀ x → fold δ (“ ⧼ σ ⧽ x ”) ≡ ret (lookup γ x)

  ext-pres : ∀{σ : GSubst Vᵐ}{δ γ : Eᶠ}{v : Vᶠ} → σ ⨟ δ ≈ γ
                → (ext-env σ) ⨟ (δ , v) ≈ (γ , v)
  ext-pres {σ}{δ}{γ}{v} σ⨟δ≈γ zero rewrite lookup-0 γ v
      | g-ext-def σ | var→val-“” 0 | lookup-0 δ v = refl
  ext-pres {σ}{δ}{γ}{v} σ⨟δ≈γ (suc x) rewrite lookup-suc γ v x
      | g-ext-def σ | g-inc-shift σ x | shift-“” (⧼ σ ⧽ x) =
      begin
          fold (δ , v) (rename (↑ 1) “ ⧼ σ ⧽ x ”)
      ≡⟨ rename-fold “ ⧼ σ ⧽ x ” G ⟩
          fold (shift-env δ) “ ⧼ σ ⧽ x ”
      ≡⟨ fold-shift δ (shift-env δ) “ ⧼ σ ⧽ x ” (lookup-shift δ) ⟩
          shiftᶜ (fold δ “ ⧼ σ ⧽ x ”)
      ≡⟨ cong shiftᶜ (σ⨟δ≈γ x) ⟩
          shiftᶜ (ret (lookup γ x))
      ≡⟨ shift-ret _ ⟩
          ret (shift (lookup γ x))
      ∎
      where
      G : (FuseFoldEnvRename.MEPFE RPF FuseFoldEnvMapEnv.⨟ ↑ 1
          ≈ (δ , v)) (shift-env δ)
      G x rewrite lookup-shift δ x | lookup-suc δ v x = refl

  MEPFE : FuseFoldEnvMapEnv GSubst-is-MapEnv F
  MEPFE = record { op-cong = op-cong ; ext-pres = ext-pres }
  open FuseFoldEnvMapEnv MEPFE public hiding (_⨟_≈_; ext-pres)


{-------------------- Fuse FoldEnv and Subst ---------------------}

{- The following too much junk for too little benefit.
   Is there an idiom that would streamline this? -}

record FuseFoldEnvSubst {Env V : Set} {ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Env V C) : Set (lsuc ℓ) where
  open FoldEnv F
  open Substitution.ABTOps Op sig using (Subst-is-Map)

  field shiftᶜ : C → C
  
  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_ renaming (_⩳_ to _⩳ᶠ_)
  open RelBind {ℓ}{V}{C}{V}{C}
           (λ v v' → v ≡ shift v') (λ c c' → c ≡ shiftᶜ c') public

  field op-cong : ∀ op rs rs' → zip _⩳ᶠ_ rs rs'
                → fold-op op rs ≡ fold-op op rs'
        shift-ret : ∀ vᶠ → shiftᶜ (ret vᶠ) ≡ ret (shift vᶠ)
        op-shift : ∀ op {rs↑ rs} → zip _⩳_ rs↑ rs
                 → fold-op op rs↑ ≡ shiftᶜ (fold-op op rs)

  MPFE : FuseFoldEnvMap Subst-is-Map F
  MPFE = record
           { shiftᶜ = shiftᶜ
           ; op-cong = op-cong
           ; var→val-“” = λ x → refl
           ; shift-“” = λ vᵐ → refl
           ; shift-ret = shift-ret
           ; op-shift = op-shift
           }
  open FuseFoldEnvMap MPFE hiding (_⩳_) public

{-------------------- Fuse Fold and Map ---------------------}

record FuseFoldMap  {Vᵐ Vᶠ : Set} {ℓ : Level}{Cᶠ : Set ℓ}
  (M : Map Vᵐ) (F : Fold Vᶠ Cᶠ) : Set (lsuc ℓ) where
  open Map {{...}} ; open Fold {{...}} using (ret; fold-op; GSubst-is-FoldEnv)
  open Quotable {{...}}
  instance _ : Map Vᵐ ; _ = M ; _ : Fold Vᶠ Cᶠ ; _ = F
           _ : Quotable Vᵐ ; _ = V-is-Quotable
  open Shiftable (Map.V-is-Shiftable M) using () renaming (var→val to var→valᵐ)
  open Shiftable (Fold.V-is-Shiftable F) using () renaming (shift to shiftᶠ)

  open Substitution.ABTOps Op sig using (rename)

  field var→val-“” : ∀ x → “ var→valᵐ x ” ≡ ` x
        shiftᶜ : Cᶠ → Cᶠ
        shift-ret : ∀ (vᶠ : Vᶠ) → shiftᶜ (ret vᶠ) ≡ ret (shiftᶠ vᶠ)
        shift-“” : ∀ (vᵐ : Vᵐ) → “ shift vᵐ ” ≡ rename (↑ 1) “ vᵐ ”
  open RelBind {ℓ}{Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ}
           (λ v v' → v ≡ shiftᶠ v') (λ c c' → c ≡ shiftᶜ c') public
  open RelBind {ℓ}{Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ} _≡_ _≡_ renaming (_⩳_ to _⩳ᶠ_)
           
  field op-shift : ∀ op {rs↑ rs} → zip _⩳_ rs↑ rs
                 → fold-op op rs↑ ≡ shiftᶜ (fold-op op rs)
        op-eq : ∀ op rs rs' → zip _⩳ᶠ_ rs rs' → fold-op op rs ≡ fold-op op rs'

  MPFE : FuseFoldEnvMap M GSubst-is-FoldEnv
  MPFE = record { shiftᶜ = shiftᶜ ; op-cong = op-eq ; var→val-“” = var→val-“”
           ; shift-“” = shift-“” ; shift-ret = shift-ret
           ; op-shift = op-shift }
  open FuseFoldEnvMap MPFE

-}

