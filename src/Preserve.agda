{---------------------------

  Preservation of a predicate

      Let "I" be the kind for type-like things.

      A : I
      Γ Δ : List I

  preserve-fold : ∀{M σ Γ Δ A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢c M ↝ fold σ M ⦂ A

  preserve-map : ∀{M σ Γ Δ A}
     → Γ ⊢ M ⦂ A
     → σ ⦂ Γ ⇒ Δ
     → Δ ⊢ map-abt σ M ⦂ A

 ---------------------------}

import ABTPredicate
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (_∘_)
import Substitution

module Preserve (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import GenericSubstitution
open import Data.Empty using (⊥)
open import Fold Op sig
open import Map Op sig
open import ScopedTuple
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var

module ABTPred {I : Set}
  (𝑉 : List I → Var → I → Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set) where

  open ABTPredicate Op sig 𝑉 𝑃 public

open import MapPreserve Op sig public

{----- Predicate on result of fold (e.g. type system for values) -----}

module FoldPred {I : Set}{V : Set}{ℓ : Level}{C : Set ℓ}
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set)
  (𝐴 : List I → V → I → Set)
  (_⊢v_⦂_ : List I → V → I → Set) (_⊢c_⦂_ : List I → C → I → Set)
  where

  data _∣_∣_⊢ᵣ_⦂_ : (b : ℕ) → List I → BType I b → Bind V C b → I → Set where
    ast-r : ∀{Δ}{c}{A}  →  Δ ⊢c c ⦂ A  →  0 ∣ Δ ∣ tt ⊢ᵣ c ⦂ A
    bind-r : ∀{b A B Bs Δ f}
          → (∀{v} → (B ∷ Δ) ⊢v v ⦂ B → 𝐴 (B ∷ Δ) v B
                  → b ∣ (B ∷ Δ) ∣ Bs ⊢ᵣ (f v) ⦂ A)
          → (suc b) ∣ Δ ∣ ⟨ B , Bs ⟩ ⊢ᵣ f ⦂ A

  ⊢ᵣ→⊢c : ∀{Δ}{Bs}{c}{A}  →  0 ∣ Δ ∣ Bs ⊢ᵣ c ⦂ A  →  Δ ⊢c c ⦂ A
  ⊢ᵣ→⊢c {Δ}{Bs}{c}{A} (ast-r ⊢cc) = ⊢cc

  data _∣_∣_⊢ᵣ₊_⦂_ : ∀(bs : List ℕ) → List I → BTypes I bs
                → Tuple bs (Bind V C) → Vec I (length bs) → Set where
    nil-r : ∀{Δ} → [] ∣ Δ ∣ tt ⊢ᵣ₊ tt ⦂ []̌ 
    cons-r : ∀{b bs r rs Δ A As Bs Bss} → b ∣ Δ ∣ Bs ⊢ᵣ r ⦂ A
        → bs ∣ Δ ∣ Bss ⊢ᵣ₊ rs ⦂ As
        → (b ∷ bs) ∣ Δ ∣ ⟨ Bs , Bss ⟩ ⊢ᵣ₊ ⟨ r , rs ⟩ ⦂ (A ∷̌ As)

{-------------------- FoldEnv Preserves ABTPred ---------------------}

record FoldEnvPreserveABTPred {V Env I : Set}{ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Env V C) : Set (lsuc ℓ) where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        𝐴 : List I → V → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        _⊢c_⦂_ : List I → C → I → Set

  open FoldEnv F
  open ABTPredicate Op sig 𝑉 𝑃 public ; open FoldPred 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_ public

  _⦂_⇒_ : Env → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v lookup σ x ⦂ A
  
  field ext-pres : ∀{v σ Γ Δ A} → (A ∷ Δ) ⊢v v ⦂ A → 𝐴 (A ∷ Δ) v A
                → σ ⦂ Γ ⇒ Δ → (σ , v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
        ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c ret v ⦂ A
        op-pres : ∀ {op}{Rs}{Δ}{A : I}{As : Vec I (length (sig op))}{Bs}
             → sig op ∣ Δ ∣ Bs ⊢ᵣ₊ Rs ⦂ As
             → 𝑃 op As Bs A
             → Δ ⊢c (fold-op op Rs) ⦂ A

  preserve-fold : ∀{M σ Γ Δ A} → Γ ⊢ M ⦂ A → σ ⦂ Γ ⇒ Δ → Δ ⊢c fold σ M ⦂ A
  pres-arg : ∀{b Γ Δ}{arg : Arg b}{A σ Bs} → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A → σ ⦂ Γ ⇒ Δ
     → b ∣ Δ ∣ Bs ⊢ᵣ fold-arg  σ {b} arg ⦂ A
  pres-args : ∀{bs Γ Δ}{args : Args bs}{As σ Bss} → bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As
     → σ ⦂ Γ ⇒ Δ  →  bs ∣ Δ ∣ Bss ⊢ᵣ₊ fold-args σ args ⦂ As
  preserve-fold {` x} {σ} {Γ} {Δ} {A} (var-p ∋x 𝑉x) σ⦂ = ret-pres (σ⦂ ∋x)
  preserve-fold {op ⦅ args ⦆} {σ} {Γ} {Δ} {A} (op-p ⊢args 𝑃op) σΓΔ =
      op-pres  (pres-args  ⊢args σΓΔ) 𝑃op
  pres-arg {zero}{Γ}{Δ}{ast M}{A}{σ} (ast-p ⊢arg) σΓΔ =
      ast-r (preserve-fold ⊢arg σΓΔ)
  pres-arg {suc b}{Γ}{Δ}{bind arg}{A}{σ}{⟨ B , Bs ⟩} (bind-p {b}{B} ⊢arg)
      σΓΔ = bind-r G
      where G : ∀{v} → (B ∷ Δ) ⊢v v ⦂ B
               → 𝐴 (B ∷ Δ) v B
               → b ∣ B ∷ Δ ∣ Bs ⊢ᵣ fold-arg σ (bind arg) v ⦂ A
            G {v} ⊢v⦂B 𝐴Mv =
                pres-arg ⊢arg (λ {x} → ext-pres {v}{σ}{Γ} ⊢v⦂B 𝐴Mv σΓΔ {x})
  pres-args {[]} {Γ} {Δ} {nil} {[]̌} ⊢args σΓΔ = nil-r 
  pres-args {b ∷ bs} {Γ} {Δ} {cons arg args} {A ∷̌ As}
      (cons-p ⊢arg ⊢args) σΓΔ =
      cons-r  (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)


record FunEnvPredExt {V I : Set} (_⊢v_⦂_ : List I → V → I → Set)
  (𝐴 : List I → V → I → Set) (S : Shiftable V) : Set where
  
  open Shiftable S
  field shift-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
  
  Env = Var → V
  open import Env S
  open EnvI FunIsEnv

  _⦂_⇒_ : Env → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v lookup σ x ⦂ A

  ext-pres : ∀{v σ Γ Δ A}
          → (A ∷ Δ) ⊢v v ⦂ A   →   𝐴 (A ∷ Δ) v A
          → σ ⦂ Γ ⇒ Δ
          → (σ , v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-pres ⊢v⦂ Av σ⦂ {zero} {B} refl = ⊢v⦂
  ext-pres {v}{σ}{Γ}{Δ}{A} ⊢v⦂ Av σ⦂ {suc x} {B} ∋x = shift-⊢v (σ⦂ ∋x)


{-------------------- Fold Preserves ABTPred ---------------------}

record FoldPreserveABTPred {V I : Set} {ℓ : Level}{C : Set ℓ}
  (F : Fold V C) : Set (lsuc ℓ) where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        𝐴 : List I → V → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        _⊢c_⦂_ : List I → C → I → Set

  open Fold F ; open Shiftable S ; open GenericSubst S 
  open ABTPredicate Op sig 𝑉 𝑃 public ; open FoldPred 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_ public
  open GSubstPred S _⊢v_⦂_ public

  field shift-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
        ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c ret v ⦂ A
        op-pres : ∀ {op}{Rs}{Δ}{A : I}{As : Vec I (length (sig op))}{Bs}
             → sig op ∣ Δ ∣ Bs ⊢ᵣ₊ Rs ⦂ As
             → 𝑃 op As Bs A
             → Δ ⊢c (fold-op op Rs) ⦂ A

  ext-pres : ∀{v σ Γ Δ A} → (A ∷ Δ) ⊢v v ⦂ A → 𝐴 (A ∷ Δ) v A
           → σ ⦂ Γ ⇒ Δ → (g-extend v σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-pres {v} {σ} {Γ} {Δ} {A} ⊢v⦂ Av σ⦂ {zero} {B} refl = ⊢v⦂
  ext-pres {v} {σ} {Γ} {Δ} {A} ⊢v⦂ Av σ⦂ {suc x} {B} ∋x
      rewrite g-inc-shift σ x = shift-⊢v (σ⦂ {x}{B} ∋x)

  FEPP : FoldEnvPreserveABTPred FE
  FEPP = record { 𝑉 = 𝑉 ; 𝑃 = 𝑃 ; 𝐴 = 𝐴 ; _⊢v_⦂_ = _⊢v_⦂_ ; _⊢c_⦂_ = _⊢c_⦂_
           ; ext-pres = ext-pres ; ret-pres = ret-pres ; op-pres = op-pres }
  open FoldEnvPreserveABTPred FEPP
     using (preserve-fold; pres-arg; pres-args) public


{-------------------- FoldEnv(ABT) Preserves FoldEnv ---------------------}

{-
  Example: 
     F is a compilation pass from language Lˢ to Lᵗ
     Fˢ is the denotational semantics Lˢ
     Fᵗ is the denotational semantics of Lᵗ

    Lˢ
    | \         
    F  \_Fˢ_
    |       \__   
    V          V
    Lᵗ - Fᵗ -> C


 -}

record FoldEnvPreserveFoldEnv {Vᶠ Envᶠ : Set}{V Env : Set}{ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Envᶠ Vᶠ ABT)
  (Fˢ : FoldEnv Env V C) (Fᵗ : FoldEnv Env V C) : Set (lsuc ℓ)
  where
  open FoldEnv F using (fold; fold-arg; fold-args; ret; fold-op; lookup; _,_;
      lookup-0; lookup-suc)
  open Shiftable (FoldEnv.S F) using (var→val; shift)
  open FoldEnv Fˢ using ()
    renaming (fold to foldˢ; fold-arg to fold-argˢ; fold-args to fold-argsˢ;
    fold-op to fold-opˢ; ret to retˢ; lookup to lookupˢ; _,_ to _,ˢ_;
    lookup-0 to lookup-0ˢ; lookup-suc to lookup-sucˢ)
  open Shiftable (FoldEnv.S Fˢ) using () renaming (shift to shiftˢ)    
  open FoldEnv Fᵗ using ()
    renaming (fold to foldᵗ; fold-arg to fold-argᵗ; fold-args to fold-argsᵗ;
    fold-op to fold-opᵗ; ret to retᵗ; lookup to lookupᵗ; _,_ to _,ᵗ_;
    lookup-0 to lookup-0ᵗ; lookup-suc to lookup-sucᵗ; shift-env to shift-envᵗ;
    lookup-shift to lookup-shiftᵗ)
  open Shiftable (FoldEnv.S Fᵗ) using () renaming (shift to shiftᵗ)
  open Substitution.ABTOps Op sig using (rename)

  field ret-var→val : ∀ x → ret (var→val x) ≡ ` x
        retᵗ-retˢ : ∀ v → retᵗ v ≡ retˢ v
        shiftᶜ : C → C
        shift-retˢ : ∀ v → shiftᶜ (retˢ v) ≡ retˢ (shiftˢ v)
        shift-retᵗ : ∀ v → shiftᶜ (retᵗ v) ≡ retᵗ (shiftᵗ v)
        ret-shift : ∀ v → ret (shift v) ≡ rename (↑ 1) (ret v)

  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_
  open Reify {lzero} Vᶠ ⊤ var→val using (reify-arg; reify-args)

  field op-congᵗ : ∀ op rs rs' → zip _⩳_ rs rs'
                 → fold-opᵗ op rs ≡ fold-opᵗ op rs'
        op-cong : ∀ op rs rsˢ τ → zip _⩳_ (fold-argsᵗ τ (reify-args rs)) rsˢ
                → foldᵗ τ (fold-op op rs) ≡ fold-opˢ op rsˢ

  open RelBind {ℓ}{V}{C}{V}{C}
           (λ v v' → v ≡ shiftᵗ v') (λ c c' → c ≡ shiftᶜ c')
           renaming (_⩳_ to _⩳ᵗ_)

  field op-shiftᵗ : ∀ op {rs↑ rs} → zip _⩳ᵗ_ rs↑ rs
                 → fold-opᵗ op rs↑ ≡ shiftᶜ (fold-opᵗ op rs)

  _⨟_≈_ : Envᶠ → Env → Env → Set ℓ
  γ ⨟ τ ≈ σ = ∀ x → foldᵗ τ (ret (lookup γ x)) ≡ retˢ (lookupˢ σ x)

  preserve : ∀{γ σ τ } (M : ABT)
    → γ ⨟ τ ≈ σ
    → foldᵗ τ (fold γ M) ≡ foldˢ σ M

  pres-arg : ∀{γ σ τ}{b : ℕ} (arg : Arg b)
    → γ ⨟ τ ≈ σ
    → fold-argᵗ τ (reify-arg (fold-arg γ arg)) ⩳ fold-argˢ σ arg

  pres-args : ∀{γ σ τ}{bs : List ℕ} (args : Args bs)
    → γ ⨟ τ ≈ σ
    → zip _⩳_ (fold-argsᵗ τ (reify-args (fold-args γ args)))
              (fold-argsˢ σ args)

  FS : FoldShift Fᵗ
  FS = record { shiftᶜ = shiftᶜ ; shift-ret = shift-retᵗ ; op-shift = op-shiftᵗ}
  open FoldShift FS using (fold-shift)  

  RPF : RenamePreserveFoldEnv Fᵗ
  RPF = record { op-eq = op-congᵗ ; shiftᶜ = shiftᶜ ; shift-ret = shift-retᵗ }
  open RenamePreserveFoldEnv RPF using (rename-fold)

  ext-pres : ∀{γ τ σ v} → γ ⨟ τ ≈ σ  →  (γ , var→val 0) ⨟ τ ,ᵗ v ≈ (σ ,ˢ v)
  ext-pres {γ} {τ} {σ} {v} γ⨟τ≈σ zero rewrite lookup-0 γ (var→val 0)
      | lookup-0ˢ σ v | ret-var→val 0 | lookup-0ᵗ τ v = retᵗ-retˢ v
  ext-pres {γ} {τ} {σ} {v} γ⨟τ≈σ (suc x) rewrite lookup-suc γ (var→val 0) x
      | lookup-sucˢ σ v x =
      begin
      foldᵗ (τ ,ᵗ v) (ret (shift (lookup γ x)))
          ≡⟨ cong (foldᵗ (τ ,ᵗ v)) (ret-shift (lookup γ x)) ⟩
      foldᵗ (τ ,ᵗ v) (rename (↑ 1) (ret (lookup γ x)))
          ≡⟨ rename-fold (ret (lookup γ x)) G ⟩
      foldᵗ (shift-envᵗ τ) (ret (lookup γ x))
          ≡⟨ fold-shift τ (shift-envᵗ τ) (ret (lookup γ x)) (lookup-shiftᵗ τ) ⟩
      shiftᶜ (foldᵗ τ (ret (lookup γ x)))
          ≡⟨ cong shiftᶜ (γ⨟τ≈σ x) ⟩
      shiftᶜ (retˢ (lookupˢ σ x))
          ≡⟨ shift-retˢ (lookupˢ σ x) ⟩
      retˢ (shiftˢ (lookupˢ σ x))
      ∎
      where
      G : (RenamePreserveFoldEnv.MEPFE RPF MapEnvPreserveFoldEnv.⨟ ↑ 1
            ≈ (τ ,ᵗ v)) (shift-envᵗ τ)
      G zero rewrite lookup-shiftᵗ τ 0 | lookup-sucᵗ τ v 0 = refl
      G (suc x) rewrite lookup-shiftᵗ τ (suc x)
          | lookup-sucᵗ τ v (suc x) = cong retᵗ refl

  preserve {γ}{σ}{τ} (` x) γ⨟τ≈σ = γ⨟τ≈σ x
  preserve {γ}{σ}{τ} (op ⦅ args ⦆) γ⨟τ≈σ =
     let pa = pres-args args γ⨟τ≈σ in
     op-cong op (fold-args γ args) (fold-argsˢ σ args) τ pa
  pres-arg {γ} {σ} {τ} (ast M) γ⨟τ≈σ = preserve M γ⨟τ≈σ
  pres-arg {γ} {σ} {τ} (bind arg) γ⨟τ≈σ refl = pres-arg arg (ext-pres γ⨟τ≈σ)
  pres-args {γ} {σ} {τ} nil γ⨟τ≈σ = tt
  pres-args {γ} {σ} {τ}{b ∷ bs} (cons arg args) γ⨟τ≈σ =
      ⟨ pres-arg {b = b} arg γ⨟τ≈σ , pres-args {bs = bs} args γ⨟τ≈σ ⟩


