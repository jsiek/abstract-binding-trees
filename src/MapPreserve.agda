import ABTPredicate
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Environment
open import Function using (_∘_)
import Substitution
open import GenericSubstitution
open import ScopedTuple
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var

module MapPreserve (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Fold Op sig
open import Map Op sig

{-------------------- MapEnv Preserves ABTPred ---------------------}

record MapEnvPreserveABTPred {V E I : Set} (M : MapEnv E V) : Set₁ where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        _⊢v_⦂_ : List I → V → I → Set

  open MapEnv M
  open Quotable V-is-Quotable
  open ABTPredicate Op sig 𝑉 𝑃 public
 
  𝐴 : List I → V → I → Set
  𝐴 Γ M A = ⊤

  _⦂_⇒_ : E → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v lookup σ x ⦂ A
  
  field quote-⊢v : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A
        ext-pres : ∀{σ Γ Δ A} → σ ⦂ Γ ⇒ Δ → ext-env σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)

  preserve-map : ∀{M σ Γ Δ A}
        → Γ ⊢ M ⦂ A
        → σ ⦂ Γ ⇒ Δ
        → Δ ⊢ map-abt σ M ⦂ A
        
  pres-arg : ∀{b Γ Δ}{arg : Arg b}{A σ Bs}
        → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A → σ ⦂ Γ ⇒ Δ
        → b ∣ Δ ∣ Bs ⊢ₐ map-arg σ {b} arg ⦂ A
  pres-args : ∀{bs Γ Δ}{args : Args bs}{As σ Bss}
        → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As → σ ⦂ Γ ⇒ Δ
        → bs ∣ Δ ∣ Bss ⊢₊ map-args σ {bs} args ⦂ As
  preserve-map {` x}{σ} (var-p ∋x 𝑉x) σ⦂ = quote-⊢v (σ⦂ ∋x)
  preserve-map {op ⦅ args ⦆} (op-p ⊢args Pop) σ⦂ =
      op-p (pres-args ⊢args σ⦂) Pop
  pres-arg {zero} {arg = ast M} (ast-p ⊢M) σ⦂ = ast-p (preserve-map ⊢M σ⦂)
  pres-arg {suc b} {arg = bind arg} (bind-p {B = B}{A = A} ⊢arg) σ⦂ =
      bind-p (pres-arg ⊢arg (ext-pres σ⦂))
  pres-args {[]} {args = nil} nil-p σ⦂ = nil-p
  pres-args {b ∷ bs} {args = cons arg args} (cons-p ⊢arg ⊢args) σ⦂ =
    cons-p (pres-arg ⊢arg σ⦂) (pres-args ⊢args σ⦂)


{-------------------- Map Preserves ABTPred ---------------------}

record MapPreserveABTPred {V I : Set} (M : Map V) : Set₁ where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        _⊢v_⦂_ : List I → V → I → Set

  open Map M ; open Shiftable (Map.V-is-Shiftable M)
  open Quotable V-is-Quotable
  open ABTPredicate Op sig 𝑉 𝑃 
 
  field shift-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
        quote-⊢v : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A
        ⊢v0 : ∀{B Δ} → (B ∷ Δ) ⊢v var→val 0 ⦂ B
                    
  open GSubstPred (Map.V-is-Shiftable M) _⊢v_⦂_ 
  open GenericSubst (Map.V-is-Shiftable M)

  ext-pres : ∀{σ Γ Δ A} → σ ⦂ Γ ⇒ Δ → g-ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-pres {σ} {Γ} {Δ} {A} σ⦂ {zero} {B} refl rewrite g-ext-def σ = ⊢v0
  ext-pres {σ} {Γ} {Δ} {A} σ⦂ {suc x} {B} ∋x
      rewrite g-ext-def σ | g-inc-shift σ x = shift-⊢v (σ⦂ {x}{B} ∋x)

  PME : MapEnvPreserveABTPred GSubst-is-MapEnv
  PME = record { 𝑉 = 𝑉 ; 𝑃 = 𝑃 ; _⊢v_⦂_ = _⊢v_⦂_ ; quote-⊢v = quote-⊢v
               ; ext-pres = ext-pres }
  open MapEnvPreserveABTPred PME hiding (ext-pres) public

{-------------------- MapEnv Preserves FoldEnv ---------------------}

record MapEnvPreserveFoldEnv  {Vᵐ Vᶠ Envᵐ Envᶠ : Set} {ℓ : Level}{Cᶠ : Set ℓ}
  (M : MapEnv Envᵐ Vᵐ) (F : FoldEnv Envᶠ Vᶠ Cᶠ) : Set (lsuc ℓ)
  where
  open MapEnv {{...}} renaming (lookup to lookupᵐ; ext-env to ext-envᵐ)
  open FoldEnv {{...}} renaming (_,_ to _,ᶠ_); open Quotable {{...}}
  instance _ : MapEnv Envᵐ Vᵐ ; _ = M ; _ : FoldEnv Envᶠ Vᶠ Cᶠ ; _ = F
           _ : Quotable Vᵐ ; _ = V-is-Quotable
           
  open RelBind {ℓ}{Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ} _≡_ _≡_

  _⨟_≈_ : Envᵐ → Envᶠ → Envᶠ → Set ℓ
  σ ⨟ δ ≈ γ = ∀ x → fold δ (“ lookupᵐ σ x ”) ≡ ret (lookup γ x)

  field op-cong : ∀ op rs rs' → zip _⩳_ rs rs' → fold-op op rs ≡ fold-op op rs'
        ext-pres : ∀{σ : Envᵐ}{δ γ : Envᶠ}{v : Vᶠ} → σ ⨟ δ ≈ γ
                → (ext-envᵐ σ) ⨟ (δ ,ᶠ v) ≈ (γ ,ᶠ v)

  map-preserve-fold : ∀{σ δ γ} (M : ABT)
     → σ ⨟ δ ≈ γ
     → fold δ (map-abt σ M)  ≡ fold γ M

  mpf-arg : ∀{b}{arg : Arg b}{σ δ γ}
     → σ ⨟ δ ≈ γ
     → fold-arg δ (map-arg σ arg) ⩳ fold-arg γ arg
  mpf-args : ∀{bs}{args : Args bs}{σ δ γ}
     → σ ⨟ δ ≈ γ
     → zip _⩳_ (fold-args δ (map-args σ args)) (fold-args γ args)
  map-preserve-fold {σ} {δ} {γ} (` x) σ⨟δ≈γ = σ⨟δ≈γ x
  map-preserve-fold {σ} {δ} {γ} (op ⦅ args ⦆) σ⨟δ≈γ =
      let mpf = (mpf-args {sig op}{args}{σ}{δ}{γ} σ⨟δ≈γ) in
      op-cong op (fold-args δ (map-args σ args)) (fold-args γ args) mpf
  mpf-arg {zero} {ast M} {σ} {δ} {γ} σ⨟δ≈γ =
      map-preserve-fold M σ⨟δ≈γ
  mpf-arg {suc b} {bind arg} {σ} {δ} {γ} σ⨟δ≈γ refl =
      mpf-arg {b}{arg} (ext-pres σ⨟δ≈γ)
  mpf-args {[]} {nil} {σ} {δ} {γ} σ⨟δ≈γ = tt
  mpf-args {b ∷ bs} {cons arg args} {σ} {δ} {γ} σ⨟δ≈γ =
      ⟨ mpf-arg{b}{arg}{σ}{δ}{γ} σ⨟δ≈γ , mpf-args σ⨟δ≈γ ⟩

{-------------------- Rename Preserves FoldEnv ---------------------}

record RenamePreserveFoldEnv {Env V : Set} {ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Env V C) : Set (lsuc ℓ) where
  open FoldEnv F ; open Shiftable V-is-Shiftable
  open Substitution using (Rename; ⦉_⦊; ext; ext-0; ext-suc)
  open Substitution.ABTOps Op sig
      using (rename; ren-arg; ren-args; Rename-is-Map)

  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_
  field op-eq : ∀ op rs rs' → zip _⩳_ rs rs' → fold-op op rs ≡ fold-op op rs'
        shiftᶜ : C → C
        shift-ret : ∀ v → shiftᶜ (ret v) ≡ ret (shift v)

  _⨟_≈_ : Rename → Env → Env → Set ℓ
  ρ ⨟ σ₁ ≈ σ₂ = ∀ x → fold σ₁ (` (⦉ ρ ⦊ x)) ≡ ret (lookup σ₂ x)
  
  ext-pres : ∀{ρ σ₁ σ₂ v} → ρ ⨟ σ₁ ≈ σ₂ → ext ρ ⨟ (σ₁ , v) ≈ (σ₂ , v)
  ext-pres {ρ} {σ₁} {σ₂} {v} prem zero rewrite ext-0 ρ
      | lookup-0 σ₁ v | lookup-0 σ₂ v = refl
  ext-pres {ρ} {σ₁} {σ₂} {v} prem (suc x) rewrite ext-suc ρ x
      | lookup-suc σ₁ v (⦉ ρ ⦊ x) | lookup-suc σ₂ v x =
      begin
          ret (shift (lookup σ₁ (⦉ ρ ⦊ x)))
      ≡⟨ sym (shift-ret _) ⟩
          shiftᶜ (ret (lookup σ₁ (⦉ ρ ⦊ x)))
      ≡⟨ cong shiftᶜ (prem x) ⟩
          shiftᶜ (ret (lookup σ₂ x))
      ≡⟨ shift-ret _ ⟩
          ret (shift (lookup σ₂ x))
      ∎

  MEPFE : MapEnvPreserveFoldEnv{Var}{V}{ℓ = ℓ}{Cᶠ = C} (Map.GSubst-is-MapEnv Rename-is-Map) F
  MEPFE = record { op-cong = op-eq ; ext-pres = ext-pres }
  open MapEnvPreserveFoldEnv MEPFE using ()
    renaming (map-preserve-fold to rename-fold;
              mpf-arg to rf-arg; mpf-args to rf-args) public


{-------------------- Rename Preserves Fold ---------------------}

record RenamePreserveFold {V : Set} {ℓ : Level}{C : Set ℓ} (F : Fold V C) : Set (lsuc ℓ)
  where
  open Fold F ; open Shiftable V-is-Shiftable
  
  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_
  field op-eq : ∀ op rs rs' → zip _⩳_ rs rs' → fold-op op rs ≡ fold-op op rs'
        ret-inj : ∀ {v v' : V} → ret v ≡ ret v' → v ≡ v'
        shiftᶜ : C → C
        shift-ret : ∀ v → shiftᶜ (ret v) ≡ ret (shift v)

  RPFE : RenamePreserveFoldEnv GSubst-is-FoldEnv
  RPFE = record { op-eq = op-eq ; shiftᶜ = shiftᶜ ; shift-ret = shift-ret }
  open RenamePreserveFoldEnv RPFE public


{-------------------- Map Preserves FoldEnv ---------------------}

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

record FoldShift {Envᶠ Vᶠ : Set}{ℓ : Level}{Cᶠ : Set ℓ}
  (F : FoldEnv Envᶠ Vᶠ Cᶠ) : Set (lsuc ℓ) where
  open FoldEnv F ; open Shiftable V-is-Shiftable

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
  fold-shift-args : ∀ (δ : Envᶠ) (δ↑ : Envᶠ) {bs} (args : Args bs)
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
      G : ∀ x → lookup (δ↑ , (shift vᶠ)) x
                ≡ shift (lookup (δ , vᶠ) x)
      G zero rewrite lookup-0 δ↑ (shift vᶠ) | lookup-0 δ vᶠ = refl
      G (suc x) rewrite lookup-suc δ vᶠ x | lookup-suc δ↑ (shift vᶠ) x =
          cong shift (δ=shift x)
  fold-shift-args δ δ↑ nil δ=shift = tt
  fold-shift-args δ δ↑ (cons arg args) δ=shift =
      ⟨ fold-shift-arg δ δ↑ arg δ=shift , fold-shift-args δ δ↑ args δ=shift ⟩


record MapPreserveFoldEnv {Envᶠ Vᵐ Vᶠ : Set}{ℓ : Level}{Cᶠ : Set ℓ}
  (M : Map Vᵐ) (F : FoldEnv Envᶠ Vᶠ Cᶠ) : Set (lsuc ℓ) where
  open Map {{...}} using (V-is-Quotable; GSubst-is-MapEnv; ext-env)
  open FoldEnv {{...}} using (fold; ret; fold-op; lookup; lookup-0; lookup-suc;
      _,_; shift-env; lookup-shift)
  open Shiftable {{...}}
  open Quotable {{...}}
  instance _ : Map Vᵐ ; _ = M ; _ : FoldEnv Envᶠ Vᶠ Cᶠ ; _ = F
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

  RPF : RenamePreserveFoldEnv F
  RPF = record { op-eq = op-cong ; shiftᶜ = shiftᶜ ; shift-ret = shift-ret }
  open RenamePreserveFoldEnv RPF using (rename-fold)

  open GSubstAux {{...}}
  instance _ : GSubstAux {Vᵐ} (Map.V-is-Shiftable M) ; _ = record {}

  _⨟_≈_ : GSubst Vᵐ → Envᶠ → Envᶠ → Set ℓ
  σ ⨟ δ ≈ γ = ∀ x → fold δ (“ ⧼ σ ⧽ x ”) ≡ ret (lookup γ x)

  ext-pres : ∀{σ : GSubst Vᵐ}{δ γ : Envᶠ}{v : Vᶠ} → σ ⨟ δ ≈ γ
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
      G : (RenamePreserveFoldEnv.MEPFE RPF MapEnvPreserveFoldEnv.⨟ ↑ 1
          ≈ (δ , v)) (shift-env δ)
      G x rewrite lookup-shift δ x | lookup-suc δ v x = refl

  MEPFE : MapEnvPreserveFoldEnv GSubst-is-MapEnv F
  MEPFE = record { op-cong = op-cong ; ext-pres = ext-pres }
  open MapEnvPreserveFoldEnv MEPFE public hiding (_⨟_≈_; ext-pres)


{-------------------- Subst Preserves FoldEnv ---------------------}

{- The following too much junk for too little benefit.
   Is there an idiom that would streamline this? -}

record SubstPreserveFoldEnv {Env V : Set} {ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Env V C) : Set (lsuc ℓ) where
  open FoldEnv F ; open Shiftable V-is-Shiftable
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

  MPFE : MapPreserveFoldEnv Subst-is-Map F
  MPFE = record
           { shiftᶜ = shiftᶜ
           ; op-cong = op-cong
           ; var→val-“” = λ x → refl
           ; shift-“” = λ vᵐ → refl
           ; shift-ret = shift-ret
           ; op-shift = op-shift
           }

{-------------------- Map Preserves Fold ---------------------}

record MapPreserveFold  {Vᵐ Vᶠ : Set} {ℓ : Level}{Cᶠ : Set ℓ}
  (M : Map Vᵐ) (F : Fold Vᶠ Cᶠ) : Set (lsuc ℓ) where
  open Map {{...}} ; open Fold {{...}} using (ret; fold-op; GSubst-is-FoldEnv)
  open Shiftable {{...}} ; open Quotable {{...}}
  instance _ : Map Vᵐ ; _ = M ; _ : Fold Vᶠ Cᶠ ; _ = F
           _ : Quotable Vᵐ ; _ = V-is-Quotable
           _ : Shiftable Vᵐ ; _ = (Map.V-is-Shiftable M)
           _ : Shiftable Vᶠ ; _ = (Fold.V-is-Shiftable F)
  open Shiftable (Map.V-is-Shiftable M) using () renaming (var→val to var→valᵐ)

  open Substitution.ABTOps Op sig using (rename)

  field var→val-“” : ∀ x → “ var→valᵐ x ” ≡ ` x
        shiftᶜ : Cᶠ → Cᶠ
        shift-ret : ∀ (vᶠ : Vᶠ) → shiftᶜ (ret vᶠ) ≡ ret (shift vᶠ)
        shift-“” : ∀ (vᵐ : Vᵐ) → “ shift vᵐ ” ≡ rename (↑ 1) “ vᵐ ”
  open RelBind {ℓ}{Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ}
           (λ v v' → v ≡ shift v') (λ c c' → c ≡ shiftᶜ c') public
  open RelBind {ℓ}{Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ} _≡_ _≡_ renaming (_⩳_ to _⩳ᶠ_)
           
  field op-shift : ∀ op {rs↑ rs} → zip _⩳_ rs↑ rs
                 → fold-op op rs↑ ≡ shiftᶜ (fold-op op rs)
        op-eq : ∀ op rs rs' → zip _⩳ᶠ_ rs rs' → fold-op op rs ≡ fold-op op rs'

  MPFE : MapPreserveFoldEnv M GSubst-is-FoldEnv
  MPFE = record { shiftᶜ = shiftᶜ ; op-cong = op-eq ; var→val-“” = var→val-“”
           ; shift-“” = shift-“” ; shift-ret = shift-ret
           ; op-shift = op-shift }
  open MapPreserveFoldEnv MPFE

