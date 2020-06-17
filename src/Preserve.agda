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

open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
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
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var

_∋_⦂_ : ∀{I : Set} → List I → Var → I → Set
_∋_⦂_ {I} [] x A = ⊥
_∋_⦂_ {I} (B ∷ Γ) zero A = A ≡ B
_∋_⦂_ {I} (B ∷ Γ) (suc x) A = Γ ∋ x ⦂ A

∋x→< : ∀{I : Set}{Γ : List I}{x A} → Γ ∋ x ⦂ A → x < (length Γ)
∋x→< {I}{B ∷ Γ} {zero} {A} ∋x = s≤s z≤n
∋x→< {I}{B ∷ Γ} {suc x} {A} ∋x = s≤s (∋x→< {I}{Γ} ∋x)

<→∋x : ∀{I : Set}{Γ : List ⊤}{x A} → x < (length Γ) → Γ ∋ x ⦂ A
<→∋x {I}{B ∷ Γ} {zero} {A} x<Γ = refl
<→∋x {I}{B ∷ Γ} {suc x} {A} (s≤s x<Γ) = <→∋x {I}{Γ}{x}{A} x<Γ

∋++ : ∀{I}{Γ Δ : List I}{x A} →  Γ ∋ x ⦂ A  → (Δ ++ Γ) ∋ (length Δ + x) ⦂ A  
∋++ {I}{Γ} {[]} {x} {A} ∋ΔΓ = ∋ΔΓ
∋++ {I}{Γ} {B ∷ Δ} {x} {A} ∋ΔΓ = ∋++ {I}{Γ}{Δ}{x}{A} ∋ΔΓ

{--- types for bound variables ---}

BType : Set → ℕ → Set
BType I zero = ⊤
BType I (suc b) = I × BType I b

BTypes : Set → List ℕ → Set
BTypes I [] = ⊤
BTypes I (b ∷ bs) = BType I b × BTypes I bs

{----- Predicate on ABT's (e.g. type system for expressions) -----}

module ABTPred {I : Set}
  (𝑉 : List I → Var → I → Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set) where

  data _⊢_⦂_ : List I → ABT → I → Set
  data _∣_∣_⊢ₐ_⦂_ : (b : ℕ) → List I → BType I b → Arg b → I → Set 
  data _∣_∣_⊢₊_⦂_ : (bs : List ℕ) → List I → BTypes I bs → Args bs
                  → Vec I (length bs) → Set
  
  data _⊢_⦂_ where
    var-p : ∀{Γ x A}
       → Γ ∋ x ⦂ A  →  𝑉 Γ x A
       → Γ ⊢ ` x ⦂ A
    op-p : ∀{Γ op}{args : Args (sig op)}{A}{As : Vec I (length (sig op))}
             {Bs : BTypes I (sig op)}
       → (sig op) ∣ Γ ∣ Bs ⊢₊ args ⦂ As
       → 𝑃 op As Bs A
       → Γ ⊢ op ⦅ args ⦆ ⦂ A

  data _∣_∣_⊢ₐ_⦂_ where
    ast-p : ∀{Γ}{M}{A}  →  Γ ⊢ M ⦂ A  →  0 ∣ Γ ∣ tt ⊢ₐ ast M ⦂ A
       
    bind-p : ∀{b}{B Bs Γ arg A} → b ∣ (B ∷ Γ) ∣ Bs ⊢ₐ arg ⦂ A
       → (suc b) ∣ Γ ∣ ⟨ B , Bs ⟩ ⊢ₐ bind arg ⦂ A

  data _∣_∣_⊢₊_⦂_ where
    nil-p : ∀{Γ} → [] ∣ Γ ∣ tt ⊢₊ nil ⦂ []̌ 
    cons-p : ∀{b bs}{arg args}{Γ}{A}{As}{Bs}{Bss}
       → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A  →  bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As
       → (b ∷ bs) ∣ Γ ∣ ⟨ Bs , Bss ⟩ ⊢₊ cons arg args ⦂ (A ∷̌ As)

{----- Predicate on result of fold (e.g. type system for values) -----}

module FoldPred {I : Set}{V C : Set}
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

module GSubstPred {V I : Set} (S : Shiftable V)
  (_⊢v_⦂_ : List I → V → I → Set) where
  open GenericSubst S
  
  _⦂_⇒_ : GSubst V → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v ⧼ σ ⧽ x ⦂ A
  
{-------------------- FoldEnv Preserves ABTPred ---------------------}

record PreserveFoldEnv {V C Env I : Set} (F : FoldEnv Env V C) : Set₁ where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        𝐴 : List I → V → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        _⊢c_⦂_ : List I → C → I → Set

  open FoldEnv F
  open ABTPred 𝑉 𝑃 public ; open FoldPred 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_ public

  _⦂_⇒_ : Env → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v lookup σ x ⦂ A
  
  field ext-env : ∀{v σ Γ Δ A} → (A ∷ Δ) ⊢v v ⦂ A → 𝐴 (A ∷ Δ) v A
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
                pres-arg ⊢arg (λ {x} → ext-env {v}{σ}{Γ} ⊢v⦂B 𝐴Mv σΓΔ {x})
  pres-args {[]} {Γ} {Δ} {nil} {[]̌} ⊢args σΓΔ = nil-r 
  pres-args {b ∷ bs} {Γ} {Δ} {cons arg args} {A ∷̌ As}
      (cons-p ⊢arg ⊢args) σΓΔ =
      cons-r  (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)


record FunEnvPredExt {V I : Set} (_⊢v_⦂_ : List I → V → I → Set)
  (𝐴 : List I → V → I → Set) (S : Shiftable V) : Set where
  
  open Shiftable S
  field ext-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
  
  Env = Var → V
  open import Env V

  open FunIsEnv S
  open EnvI FunIsEnv

  _⦂_⇒_ : Env → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v lookup σ x ⦂ A

  ext-env : ∀{v σ Γ Δ A}
          → (A ∷ Δ) ⊢v v ⦂ A   →   𝐴 (A ∷ Δ) v A
          → σ ⦂ Γ ⇒ Δ
          → (σ , v) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-env ⊢v⦂ Av σ⦂ {zero} {B} refl = ⊢v⦂
  ext-env {v}{σ}{Γ}{Δ}{A} ⊢v⦂ Av σ⦂ {suc x} {B} ∋x = ext-⊢v (σ⦂ ∋x)



{-------------------- Fold Preserves ABTPred ---------------------}

record PreserveFold {V C I : Set} (F : Fold V C) : Set₁ where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        𝐴 : List I → V → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        _⊢c_⦂_ : List I → C → I → Set

  open Fold F ; open Shiftable S ; open GenericSubst S 
  open ABTPred 𝑉 𝑃 public ; open FoldPred 𝑃 𝐴 _⊢v_⦂_ _⊢c_⦂_ public
  open GSubstPred S _⊢v_⦂_ public

  field ext-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
        ret-pres : ∀{v}{Δ}{A} → Δ ⊢v v ⦂ A → Δ ⊢c ret v ⦂ A
        op-pres : ∀ {op}{Rs}{Δ}{A : I}{As : Vec I (length (sig op))}{Bs}
             → sig op ∣ Δ ∣ Bs ⊢ᵣ₊ Rs ⦂ As
             → 𝑃 op As Bs A
             → Δ ⊢c (fold-op op Rs) ⦂ A

  ext-env : ∀{v σ Γ Δ A} → (A ∷ Δ) ⊢v v ⦂ A → 𝐴 (A ∷ Δ) v A
           → σ ⦂ Γ ⇒ Δ → (g-extend v σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-env {v} {σ} {Γ} {Δ} {A} ⊢v⦂ Av σ⦂ {zero} {B} refl = ⊢v⦂
  ext-env {v} {σ} {Γ} {Δ} {A} ⊢v⦂ Av σ⦂ {suc x} {B} ∋x
      rewrite g-inc-shift σ x = ext-⊢v (σ⦂ {x}{B} ∋x)
  
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
                pres-arg ⊢arg (λ {x} → ext-env {v}{σ}{Γ} ⊢v⦂B 𝐴Mv σΓΔ {x})
  pres-args {[]} {Γ} {Δ} {nil} {[]̌} ⊢args σΓΔ = nil-r 
  pres-args {b ∷ bs} {Γ} {Δ} {cons arg args} {A ∷̌ As}
      (cons-p ⊢arg ⊢args) σΓΔ =
      cons-r  (pres-arg {b} ⊢arg σΓΔ) (pres-args ⊢args σΓΔ)

{-------------------- MapEnv Preserves ABTPred ---------------------}

record PreserveMapEnv {V Env I : Set} (M : MapEnv V Env) : Set₁ where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        _⊢v_⦂_ : List I → V → I → Set

  open MapEnv M
  open ABTPred 𝑉 𝑃 public
 
  𝐴 : List I → V → I → Set
  𝐴 Γ M A = ⊤

  _⦂_⇒_ : Env → List I → List I → Set
  σ ⦂ Γ ⇒ Δ = ∀{x A} → Γ ∋ x ⦂ A  →  Δ ⊢v lookup σ x ⦂ A
  
  field ⊢v→⊢ : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A
        ext-env : ∀{σ Γ Δ A} → σ ⦂ Γ ⇒ Δ → ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)

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
  preserve-map {` x}{σ} (var-p ∋x 𝑉x) σ⦂ = ⊢v→⊢ (σ⦂ ∋x)
  preserve-map {op ⦅ args ⦆} (op-p ⊢args Pop) σ⦂ =
      op-p (pres-args ⊢args σ⦂) Pop
  pres-arg {zero} {arg = ast M} (ast-p ⊢M) σ⦂ = ast-p (preserve-map ⊢M σ⦂)
  pres-arg {suc b} {arg = bind arg} (bind-p {B = B}{A = A} ⊢arg) σ⦂ =
      bind-p (pres-arg ⊢arg (ext-env σ⦂))
  pres-args {[]} {args = nil} nil-p σ⦂ = nil-p
  pres-args {b ∷ bs} {args = cons arg args} (cons-p ⊢arg ⊢args) σ⦂ =
    cons-p (pres-arg ⊢arg σ⦂) (pres-args ⊢args σ⦂)


{-------------------- Map Preserves ABTPred ---------------------}

record PreserveMap {V I : Set} (M : Map V) : Set₁ where
  field 𝑉 : List I → Var → I → Set
        𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set
        _⊢v_⦂_ : List I → V → I → Set
        ∋→⊢v-var→val : ∀{Γ x A} → Γ ∋ x ⦂ A
                     → Γ ⊢v Shiftable.var→val (Map.S M) x ⦂ A

  open Map M ; open GenericSubst S
  open ABTPred 𝑉 𝑃 public
 
  field ext-⊢v : ∀{A B Δ v} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
        ⊢v→⊢ : ∀{Γ v A} → Γ ⊢v v ⦂ A → Γ ⊢ “ v ” ⦂ A
        ⊢v0 : ∀{B Δ} → (B ∷ Δ) ⊢v var→val 0 ⦂ B
                    
  𝐴 : List I → V → I → Set
  𝐴 Γ M A = ⊤

  open FoldPred {I}{V}{V} 𝑃 𝐴 _⊢v_⦂_ _⊢v_⦂_ public
  open GSubstPred S _⊢v_⦂_ public
  
  ext-env : ∀{σ Γ Δ A} → σ ⦂ Γ ⇒ Δ → (g-ext σ) ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  ext-env {σ} {Γ} {Δ} {A} σ⦂ {zero} {B} refl rewrite g-ext-def σ = ⊢v0
  ext-env {σ} {Γ} {Δ} {A} σ⦂ {suc x} {B} ∋x
      rewrite g-ext-def σ | g-inc-shift σ x = ext-⊢v (σ⦂ {x}{B} ∋x)

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
  preserve-map {` x}{σ} (var-p ∋x 𝑉x) σ⦂ = ⊢v→⊢ (σ⦂ ∋x)
  preserve-map {op ⦅ args ⦆} (op-p ⊢args Pop) σ⦂ =
      op-p (pres-args ⊢args σ⦂) Pop
  pres-arg {zero} {arg = ast M} (ast-p ⊢M) σ⦂ = ast-p (preserve-map ⊢M σ⦂)
  pres-arg {suc b} {arg = bind arg} (bind-p {B = B}{A = A} ⊢arg) σ⦂ =
      bind-p (pres-arg ⊢arg (ext-env σ⦂))
  pres-args {[]} {args = nil} nil-p σ⦂ = nil-p
  pres-args {b ∷ bs} {args = cons arg args} (cons-p ⊢arg ⊢args) σ⦂ =
    cons-p (pres-arg ⊢arg σ⦂) (pres-args ⊢args σ⦂)

{-------------------- Rename Preserves Fold ---------------------}

record RenamePreserveFold {V C : Set} (F : Fold V C) : Set₁ where
  open Fold F
  open Shiftable (Fold.S F)
  open GenericSubst (Fold.S F)
  open Substitution using (Rename; ⦉_⦊; ext; ext-0; ext-suc)
  open Substitution.ABTOps Op sig using (rename; ren-arg; ren-args)

  open RelBind {V}{C}{V}{C} _≡_ _≡_
  field op-eq : ∀ op rs rs' → zip _⩳_ rs rs' → fold-op op rs ≡ fold-op op rs'

  _⨟_≈_ : Rename → GSubst V → GSubst V → Set
  ρ ⨟ σ₁ ≈ σ₂ = ∀ x → ⧼ σ₁ ⧽ (⦉ ρ ⦊ x) ≡ ⧼ σ₂ ⧽ x

  ext-⨟≈ : ∀{ρ σ₁ σ₂ v} → ρ ⨟ σ₁ ≈ σ₂
         → ext ρ ⨟ v • g-inc σ₁ ≈ (v • g-inc σ₂)
  ext-⨟≈ {ρ} {σ₁} {σ₂} {v} ρ⨟σ₁≈σ₂ zero rewrite ext-0 ρ = refl
  ext-⨟≈ {ρ} {σ₁} {σ₂} {v} ρ⨟σ₁≈σ₂ (suc x) rewrite ext-suc ρ x
      | g-inc-shift σ₁ (⦉ ρ ⦊ x) | g-inc-shift σ₂ x = cong shift (ρ⨟σ₁≈σ₂ x)

  rename-fold : ∀{ρ σ₁ σ₂} (M : ABT)
    → ρ ⨟ σ₁ ≈ σ₂
    → fold σ₁ (rename ρ M) ≡ fold σ₂ M

  rf-arg : ∀{b}{ρ σ₁ σ₂} (arg : Arg b)
     → ρ ⨟ σ₁ ≈ σ₂
     → fold-arg σ₁ (ren-arg ρ arg) ⩳ fold-arg σ₂ arg
  rf-args : ∀{bs}{ρ σ₁ σ₂} (args : Args bs)
     → ρ ⨟ σ₁ ≈ σ₂
     → zip _⩳_ (fold-args σ₁ (ren-args ρ args)) (fold-args σ₂ args)
  rename-fold {ρ} {σ₁} {σ₂} (` x) σ₁∘ρ=σ₂ = cong ret (σ₁∘ρ=σ₂ x)
  rename-fold {ρ} {σ₁} {σ₂} (op ⦅ args ⦆) σ₁∘ρ=σ₂ =
      op-eq op (fold-args σ₁ (ren-args ρ args)) (fold-args σ₂ args)
               (rf-args args σ₁∘ρ=σ₂)
  rf-arg {zero} {ρ} {σ₁} {σ₂} (ast M) ρ⨟σ₁≈σ₂ = rename-fold M ρ⨟σ₁≈σ₂
  rf-arg {suc b} {ρ} {σ₁} {σ₂} (bind arg) ρ⨟σ₁≈σ₂ refl = 
      rf-arg {b} arg (ext-⨟≈ ρ⨟σ₁≈σ₂)
  rf-args {[]} {ρ} {σ₁} {σ₂} nil ρ⨟σ₁≈σ₂ = tt
  rf-args {b ∷ bs} {ρ} {σ₁} {σ₂} (cons arg args) ρ⨟σ₁≈σ₂ =
      ⟨ rf-arg arg ρ⨟σ₁≈σ₂ , rf-args args ρ⨟σ₁≈σ₂ ⟩

{-------------------- MapEnv Preserves FoldEnv ---------------------}

record MapEnvPreserveFoldEnv  {Vᵐ Vᶠ Cᶠ Envᵐ Envᶠ I : Set} (M : MapEnv Vᵐ Envᵐ)
  (F : FoldEnv Envᶠ Vᶠ Cᶠ)
  : Set₁
  where
  open MapEnv M renaming (lookup to lookupᵐ; “_” to “_”ᵐ; ext to extᵐ)
  open FoldEnv F renaming (lookup to lookupᶠ; _,_ to _,ᶠ_)
  open RelBind {Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ} _≡_ _≡_

  _⨟_≈_ : Envᵐ → Envᶠ → Envᶠ → Set
  σ ⨟ δ ≈ γ = ∀ x → fold δ (“ lookupᵐ σ x ”ᵐ) ≡ ret (lookupᶠ γ x)

  field op-cong : ∀ op rs rs' → zip _⩳_ rs rs' → fold-op op rs ≡ fold-op op rs'
        ext-env : ∀{σ : Envᵐ}{δ γ : Envᶠ}{v : Vᶠ} → σ ⨟ δ ≈ γ
                → (extᵐ σ) ⨟ (δ ,ᶠ v) ≈ (γ ,ᶠ v)

  map-preserve-fold : ∀{M σ δ γ}
     → σ ⨟ δ ≈ γ
     → fold δ (map-abt σ M)  ≡ fold γ M

  mpf-arg : ∀{b}{arg : Arg b}{σ δ γ}
     → σ ⨟ δ ≈ γ
     → fold-arg δ (map-arg σ arg) ⩳ fold-arg γ arg
  mpf-args : ∀{bs}{args : Args bs}{σ δ γ}
     → σ ⨟ δ ≈ γ
     → zip _⩳_ (fold-args δ (map-args σ args)) (fold-args γ args)
  map-preserve-fold {` x} {σ} {δ} {γ} σ⨟δ≈γ = σ⨟δ≈γ x
  map-preserve-fold {op ⦅ args ⦆} {σ} {δ} {γ} σ⨟δ≈γ =
      let mpf = (mpf-args {sig op}{args}{σ}{δ}{γ} σ⨟δ≈γ) in
      op-cong op (fold-args δ (map-args σ args)) (fold-args γ args) mpf
  mpf-arg {zero} {ast M} {σ} {δ} {γ} σ⨟δ≈γ =
      map-preserve-fold {M} σ⨟δ≈γ
  mpf-arg {suc b} {bind arg} {σ} {δ} {γ} σ⨟δ≈γ refl =
      mpf-arg {b}{arg} (ext-env σ⨟δ≈γ)
  mpf-args {[]} {nil} {σ} {δ} {γ} σ⨟δ≈γ = tt
  mpf-args {b ∷ bs} {cons arg args} {σ} {δ} {γ} σ⨟δ≈γ =
      ⟨ mpf-arg{b}{arg}{σ}{δ}{γ} σ⨟δ≈γ , mpf-args σ⨟δ≈γ ⟩


{-------------------- Map Preserves Fold ---------------------}

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


module BindShift (V₂ C₂ : Set) (shift₂ : V₂ → V₂) (shiftᶜ : C₂ → C₂) where

  bind-shiftᶜ : ∀{b} → Bind V₂ C₂ b → Bind V₂ C₂ b
  bind-shiftᶜ {zero} c₂ = shiftᶜ c₂
  bind-shiftᶜ {suc b} f v₂ = bind-shiftᶜ {b} (f v₂)
  
record MapPreserveFold  {Vᵐ Vᶠ Cᶠ I : Set} (M : Map Vᵐ) (F : Fold Vᶠ Cᶠ)
  : Set₁
  where
  open Map M ; open Fold F
  open Shiftable (Map.S M) using ()
      renaming (shift to shiftᵐ; var→val to var→valᵐ)
  open Shiftable (Fold.S F) using () renaming (shift to shiftᶠ)
  open GenericSubst (Map.S M)
      using (g-ext-def) renaming (⧼_⧽ to ⧼_⧽ᵐ; g-ext to extᵐ;
      g-inc-shift to g-inc-shiftᵐ; g-inc to g-incᵐ)
  open GenericSubst (Fold.S F)
      using (g-extend; g-inc) renaming (⧼_⧽ to ⧼_⧽ᶠ; g-ext to extᶠ;
      g-inc-shift to g-inc-shiftᶠ)
  open Substitution.ABTOps Op sig using (rename)

  field var→val-“” : ∀ x → “ var→valᵐ x ” ≡ ` x
        shiftᶜ : Cᶠ → Cᶠ
        shift-ret : ∀ vᶠ → shiftᶜ (ret vᶠ) ≡ ret (shiftᶠ vᶠ)
        shift-“” : ∀ vᵐ → “ shiftᵐ vᵐ ” ≡ rename (↑ 1) “ vᵐ ”
  open RelBind {Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ}
           (λ v v' → v ≡ shiftᶠ v') (λ c c' → c ≡ shiftᶜ c') public
  open RelBind {Vᶠ}{Cᶠ}{Vᶠ}{Cᶠ} _≡_ _≡_ renaming (_⩳_ to _⩳ᶠ_)
           
  field op-shift : ∀ op {rs↑ rs} → zip _⩳_ rs↑ rs
                 → fold-op op rs↑ ≡ shiftᶜ (fold-op op rs)
        op-eq : ∀ op rs rs' → zip _⩳ᶠ_ rs rs' → fold-op op rs ≡ fold-op op rs'

  _⨟_≈_ : GSubst Vᵐ → GSubst Vᶠ → GSubst Vᶠ → Set
  σ ⨟ δ ≈ γ = ∀ x → fold δ “ ⧼ σ ⧽ᵐ x ” ≡ ret (⧼ γ ⧽ᶠ x)

  RPF : RenamePreserveFold F
  RPF = record { op-eq = op-eq }
  open RenamePreserveFold RPF using (rename-fold)

  fold-inc : ∀ δ δ↑ M
      → (∀ x → ⧼ δ↑ ⧽ᶠ x ≡ shiftᶠ (⧼ δ ⧽ᶠ x))
      → fold δ↑ M ≡ shiftᶜ (fold δ M)
  fold-inc-arg : ∀ δ δ↑ {b} (arg : Arg b)
      → (∀ x → ⧼ δ↑ ⧽ᶠ x ≡ shiftᶠ (⧼ δ ⧽ᶠ x))
      → fold-arg δ↑ arg ⩳ fold-arg δ arg
  fold-inc-args : ∀ (δ : GSubst Vᶠ) (δ↑ : GSubst Vᶠ) {bs} (args : Args bs)
      → (∀ x → ⧼ δ↑ ⧽ᶠ x ≡ shiftᶠ (⧼ δ ⧽ᶠ x))
      → zip _⩳_ (fold-args δ↑ args) (fold-args δ args)

  fold-inc δ δ↑ (` x) δ=shift rewrite (δ=shift x)| shift-ret (⧼ δ ⧽ᶠ x) = refl
  fold-inc δ δ↑ (op ⦅ args ⦆) δ=shift =
      op-shift op (fold-inc-args δ δ↑ args δ=shift)
  fold-inc-arg δ δ↑ (ast M) δ=shift = fold-inc δ δ↑ M δ=shift
  fold-inc-arg δ δ↑ (bind arg) δ=shift {_}{vᶠ} refl =
      fold-inc-arg (g-extend vᶠ δ) (g-extend (shiftᶠ vᶠ) δ↑) arg G
      where
      G : ∀ x → ⧼ g-extend (shiftᶠ vᶠ) δ↑ ⧽ᶠ x ≡ shiftᶠ (⧼ g-extend vᶠ δ ⧽ᶠ x)
      G zero = refl
      G (suc x) =
          begin
          ⧼ g-inc δ↑ ⧽ᶠ x           ≡⟨ g-inc-shiftᶠ δ↑ x ⟩
          shiftᶠ (⧼ δ↑ ⧽ᶠ x)        ≡⟨ cong shiftᶠ (δ=shift x) ⟩
          shiftᶠ (shiftᶠ (⧼ δ ⧽ᶠ x)) ≡⟨ cong shiftᶠ (sym (g-inc-shiftᶠ δ x)) ⟩
          shiftᶠ (⧼ g-inc δ ⧽ᶠ x)
          ∎
  fold-inc-args δ δ↑ nil δ=shift = tt
  fold-inc-args δ δ↑ (cons arg args) δ=shift =
      ⟨ fold-inc-arg δ δ↑ arg δ=shift , fold-inc-args δ δ↑ args δ=shift ⟩

  exts : ∀{σ δ γ}{v : Vᶠ} → σ ⨟ δ ≈ γ
     → extᵐ σ ⨟ g-extend v δ ≈ g-extend v γ
  exts {σ} {δ} {γ} {v} σ⨟δ≈γ zero rewrite g-ext-def σ | var→val-“” 0 = refl
  exts {σ} {δ} {γ} {v} σ⨟δ≈γ (suc x) rewrite g-inc-shiftᶠ γ x
      | g-ext-def σ | g-inc-shiftᵐ σ x | sym (shift-ret (⧼ γ ⧽ᶠ x))
      | shift-“” (⧼ σ ⧽ᵐ x) =
       begin
           fold (v • g-inc δ) (rename (↑ 1) “ ⧼ σ ⧽ᵐ x ”)
       ≡⟨ RF ⟩
           fold (g-inc δ) “ ⧼ σ ⧽ᵐ x ”
       ≡⟨ fold-inc δ (g-inc δ) “ ⧼ σ ⧽ᵐ x ” (g-inc-shiftᶠ δ) ⟩
           shiftᶜ (fold δ “ ⧼ σ ⧽ᵐ x ”)
       ≡⟨ cong shiftᶜ (σ⨟δ≈γ x) ⟩
           shiftᶜ (ret (⧼ γ ⧽ᶠ x))
       ∎
      where
      G : (RenamePreserveFold._⨟_≈_ RPF (↑ 1) (v • g-inc δ) (g-inc δ))
      G x rewrite g-inc-shiftᶠ δ x = refl
      RF : fold (v • g-inc δ) (rename (↑ 1) “ ⧼ σ ⧽ᵐ x ”)
         ≡ fold (g-inc δ) “ ⧼ σ ⧽ᵐ x ”
      RF = rename-fold {↑ 1}{v • g-inc δ}{g-inc δ} “ ⧼ σ ⧽ᵐ x ” G 

  map-preserve-fold : ∀{M σ δ γ}
     → σ ⨟ δ ≈ γ
     → fold δ (map-abt σ M)  ≡ fold γ M

  mpf-arg : ∀{b}{arg : Arg b}{σ δ γ}
     → σ ⨟ δ ≈ γ
     → fold-arg δ (map-arg σ arg) ⩳ᶠ fold-arg γ arg
  mpf-args : ∀{bs}{args : Args bs}{σ δ γ}
     → σ ⨟ δ ≈ γ
     → zip _⩳ᶠ_ (fold-args δ (map-args σ args)) (fold-args γ args)
  map-preserve-fold {` x} {σ} {δ} {γ} σ⨟δ≈γ = σ⨟δ≈γ x
  map-preserve-fold {op ⦅ args ⦆} {σ} {δ} {γ} σ⨟δ≈γ =
      let mpf = (mpf-args {sig op}{args}{σ}{δ}{γ} σ⨟δ≈γ) in
      op-eq op (fold-args δ (map-args σ args)) (fold-args γ args) mpf
  mpf-arg {zero} {ast M} {σ} {δ} {γ} σ⨟δ≈γ =
      map-preserve-fold {M} σ⨟δ≈γ
  mpf-arg {suc b} {bind arg} {σ} {δ} {γ} σ⨟δ≈γ refl =
      mpf-arg {b}{arg} (exts σ⨟δ≈γ)
  mpf-args {[]} {nil} {σ} {δ} {γ} σ⨟δ≈γ = tt
  mpf-args {b ∷ bs} {cons arg args} {σ} {δ} {γ} σ⨟δ≈γ =
      ⟨ mpf-arg{b}{arg}{σ}{δ}{γ} σ⨟δ≈γ , mpf-args σ⨟δ≈γ ⟩
