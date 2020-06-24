import ABTPredicate
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Environment
open import Function using (_∘_)
import Substitution

module FoldFoldFusion (Op : Set) (sig : Op → List ℕ) where

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


{-------------------- Fuse FoldEnv(ABT) and FoldEnv ---------------------}
{- aka. fusion of two folds -}

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

{- 
   TODO: don't require ABT output from F.
   Instead, require quote from Cᶠ to ABT.
-}

module ReifyArg {Vᶠ}{Cᶠ}
  (Vᶠ-is-Shiftable : Shiftable Vᶠ)
  (Cᶠ-is-Quotable : Quotable Cᶠ) where
  open Shiftable {{...}} ; open Quotable {{...}}
  instance _ : Shiftable Vᶠ ; _ = Vᶠ-is-Shiftable
           _ : Quotable Cᶠ ; _ = Cᶠ-is-Quotable
  
  reify-arg : {b : ℕ} → Bind Vᶠ Cᶠ b → Arg b
  reify-arg {zero} c = ast “ c ”
  reify-arg {suc b} f = bind (reify-arg {b} (f (var→val 0)))

  reify-args : {bs : List ℕ} → Tuple bs (Bind Vᶠ Cᶠ) → Args bs
  reify-args {[]} tt = nil
  reify-args {b ∷ bs} ⟨ r , rs ⟩ = cons (reify-arg r) (reify-args rs)


record FuseFoldFoldAux
  {Vᶠ Cᶠ Envᶠ : Set}
  {V Envˢ Envᵗ : Set}{ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Envᶠ Vᶠ Cᶠ)
  (Fˢ : FoldEnv Envˢ V C) (Fᵗ : FoldEnv Envᵗ V C)
  (Cᶠ-is-Quotable : Quotable Cᶠ)
  : Set (lsuc ℓ)
  where
  open FoldEnv {{...}} ; open Quotable {{...}}
  instance _ : FoldEnv Envᶠ Vᶠ Cᶠ ; _ = F
           _ : FoldEnv Envˢ V C ; _ = Fˢ
           _ : FoldEnv Envᵗ V C ; _ = Fᵗ
           _ : Quotable Cᶠ ; _ = Cᶠ-is-Quotable
  open FoldEnv F using () renaming (ret to retᶠ)
  open FoldEnv Fˢ using () renaming (ret to retˢ; fold-op to fold-opˢ;
      lookup-0 to lookup-0ˢ; lookup-suc to lookup-sucˢ)
  open FoldEnv Fᵗ using () renaming (ret to retᵗ; fold-op to fold-opᵗ;
      lookup-0 to lookup-0ᵗ; lookup-suc to lookup-sucᵗ;
      lookup-shift to lookup-shiftᵗ; shift to shiftᵗ)
  open Substitution.ABTOps Op sig using (rename)
  
  field retᵗ-retˢ : ∀ (v : V) → retᵗ v ≡ retˢ v
        ret-var→val : ∀ x → “ ret (var→val x) ” ≡ ` x
        shiftᶜ : C → C
        shift-retˢ : ∀ (v : V) → shiftᶜ (retˢ v) ≡ retˢ (shift v)
        shift-retᵗ : ∀ (v : V) → shiftᶜ (retᵗ v) ≡ retᵗ (shiftᵗ v)
        ret-shift : ∀ (vᶠ : Vᶠ) → “ ret (shift vᶠ) ” ≡ rename (↑ 1) “ ret vᶠ ”
  field argᶠ : (op : Op) → ℕ → Tuple (sig op) (Bind Vᶠ Cᶠ) → Vᶠ
        argˢ : (op : Op) → ℕ → Tuple (sig op) (Bind V C) → V
  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_
  field op-congᵗ : ∀ op rs rs' → zip _⩳_ rs rs'
                 → fold-opᵗ op rs ≡ fold-opᵗ op rs'
        
  open RelBind {ℓ}{V}{C}{V}{C}
           (λ v v' → v ≡ shiftᵗ v') (λ c c' → c ≡ shiftᶜ c')
           renaming (_⩳_ to _⩳ᵗ_)

  field op-shiftᵗ : ∀ op {rs↑ rs} → zip _⩳ᵗ_ rs↑ rs
                 → fold-opᵗ op rs↑ ≡ shiftᶜ (fold-opᵗ op rs)

  _⨟_≈_ : Envᶠ → Envᵗ → Envˢ → Set ℓ
  γ ⨟ τ ≈ σ = ∀ x → fold τ “ ret (lookup γ x) ” ≡ retˢ (lookup σ x)

  {- need to tell argᶠ which argument place its working on -}

  {- would be nice to remove γ ⨟ τ ≈ σ premise from ind-hyp -}

  ind-hyp : ∀ k op (b : ℕ)(arg : Arg b)
       (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
       (rsˢ : Tuple (sig op) (Bind V C))
       (γ : Envᶠ) (τ : Envᵗ) (σ : Envˢ) → Set ℓ
  ind-hyp k op zero (ast M) rsᶠ rsˢ γ τ σ =
      γ ⨟ τ ≈ σ → fold τ “ fold γ M ” ≡ fold σ M
  ind-hyp k op (suc b) (bind arg) rsᶠ rsˢ γ τ σ =
      ind-hyp k op b arg rsᶠ rsˢ (γ , argᶠ op k rsᶠ) (τ , argˢ op k rsˢ)
              (σ , argˢ op k rsˢ)
       
  ind-hyps : ∀ k op (bs : List ℕ)(args : Args bs) 
       (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
       (rsˢ : Tuple (sig op) (Bind V C))
       (γ : Envᶠ) (τ : Envᵗ) (σ : Envˢ) → Set ℓ
  ind-hyps k op [] args rsᶠ rsˢ γ τ σ = ⊤
  ind-hyps k op (b ∷ bs) (cons arg args) rsᶠ rsˢ γ τ σ =
    ind-hyp k op b arg rsᶠ rsˢ γ τ σ × ind-hyps (suc k) op bs args rsᶠ rsˢ γ τ σ

  open import FoldMapFusion Op sig

  FS : FoldShift Fᵗ
  FS = record { shiftᶜ = shiftᶜ ; shift-ret = shift-retᵗ ; op-shift = op-shiftᵗ}
  open FoldShift FS using (fold-shift)  

  RPF : FuseFoldEnvRename Fᵗ
  RPF = record { op-eq = op-congᵗ ; shiftᶜ = shiftᶜ ; shift-ret = shift-retᵗ }
  open FuseFoldEnvRename RPF using (rename-fold)

  {- need to update this and use it! -}
  ext-pres : ∀{γ : Envᶠ}{σ : Envˢ}{τ : Envᵗ}{v : V}
     → γ ⨟ τ ≈ σ  →  (γ , var→val 0) ⨟ τ , v ≈ (σ , v)
  ext-pres {γ} {σ} {τ} {v} γ⨟τ≈σ zero rewrite lookup-0 γ (var→val 0)
      | lookup-0ˢ σ v | ret-var→val 0 | lookup-0ᵗ τ v = retᵗ-retˢ v
  ext-pres {γ} {σ} {τ} {v} γ⨟τ≈σ (suc x) rewrite lookup-suc γ (var→val 0) x
      | lookup-sucˢ σ v x = begin
      fold (τ , v) “ ret (shift (lookup γ x)) ”
         ≡⟨ cong (fold (τ , v)) (ret-shift (lookup γ x)) ⟩
      fold (τ , v) (rename (↑ 1) “ ret (lookup γ x) ”)
         ≡⟨ rename-fold “ ret (lookup γ x) ” G ⟩
      fold (shift-env τ) “ ret (lookup γ x) ”
         ≡⟨ fold-shift τ (shift-env τ) “ ret (lookup γ x) ” (lookup-shiftᵗ τ) ⟩
      shiftᶜ (fold τ “ ret (lookup γ x) ”)
         ≡⟨ cong shiftᶜ (γ⨟τ≈σ x) ⟩
      shiftᶜ (retˢ (lookup σ x))
         ≡⟨ shift-retˢ (lookup σ x) ⟩
      retˢ (shift (lookup σ x))
      ∎
      where
      G : (FuseFoldEnvRename.MEPFE RPF FuseFoldEnvMapEnv.⨟ ↑ 1
            ≈ (τ , v)) (shift-env τ)
      G zero rewrite lookup-shiftᵗ τ 0 | lookup-sucᵗ τ v 0 = refl
      G (suc x) rewrite lookup-shiftᵗ τ (suc x)
          | lookup-sucᵗ τ v (suc x) = cong retᵗ refl



record FuseFoldEnvFoldEnv {Vᶠ Cᶠ Envᶠ : Set}
  {V Envˢ Envᵗ : Set}{ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Envᶠ Vᶠ Cᶠ)
  (Fˢ : FoldEnv Envˢ V C) (Fᵗ : FoldEnv Envᵗ V C)
  (Cᶠ-is-Quotable : Quotable Cᶠ)
  : Set (lsuc ℓ)
  where
  open FoldEnv {{...}} ; open Quotable {{...}}
  instance _ : FoldEnv Envᶠ Vᶠ Cᶠ ; _ = F
           _ : FoldEnv Envˢ V C ; _ = Fˢ
           _ : FoldEnv Envᵗ V C ; _ = Fᵗ
           _ : Quotable Cᶠ ; _ = Cᶠ-is-Quotable
  open FoldEnv F using () renaming (ret to retᶠ)
  open FoldEnv Fˢ using () renaming (ret to retˢ; fold-op to fold-opˢ;
      lookup-0 to lookup-0ˢ; lookup-suc to lookup-sucˢ)
  open FoldEnv Fᵗ using () renaming (ret to retᵗ; fold-op to fold-opᵗ;
      lookup-0 to lookup-0ᵗ; lookup-suc to lookup-sucᵗ;
      lookup-shift to lookup-shiftᵗ)
  open Shiftable (FoldEnv.V-is-Shiftable Fᵗ) using() renaming (shift to shiftᵗ)
  open Substitution.ABTOps Op sig using (rename)

  field retᵗ-retˢ : ∀ (v : V) → retᵗ v ≡ retˢ v
        ret-var→val : ∀ x → “ ret (var→val x) ” ≡ ` x
        shiftᶜ : C → C
        shift-retˢ : ∀ (v : V) → shiftᶜ (retˢ v) ≡ retˢ (shift v)
        shift-retᵗ : ∀ (v : V) → shiftᶜ (retᵗ v) ≡ retᵗ (shiftᵗ v)
        ret-shift : ∀ (vᶠ : Vᶠ) → “ ret (shift vᶠ) ” ≡ rename (↑ 1) “ ret vᶠ ”
  field argᶠ : (op : Op) → ℕ → Tuple (sig op) (Bind Vᶠ Cᶠ) → Vᶠ
        argˢ : (op : Op) → ℕ → Tuple (sig op) (Bind V C) → V


  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_
  field op-congᵗ : ∀ op rs rs' → zip _⩳_ rs rs'
                 → fold-opᵗ op rs ≡ fold-opᵗ op rs'
  open RelBind {ℓ}{V}{C}{V}{C}
           (λ v v' → v ≡ shiftᵗ v') (λ c c' → c ≡ shiftᶜ c')
           renaming (_⩳_ to _⩳ᵗ_)

  field op-shiftᵗ : ∀ op {rs↑ rs} → zip _⩳ᵗ_ rs↑ rs
                 → fold-opᵗ op rs↑ ≡ shiftᶜ (fold-opᵗ op rs)
  
  open ReifyArg {Vᶠ}{Cᶠ} V-is-Shiftable Cᶠ-is-Quotable
  FFFAux : FuseFoldFoldAux F Fˢ Fᵗ Cᶠ-is-Quotable
  FFFAux = record
             { retᵗ-retˢ = retᵗ-retˢ
             ; ret-var→val = ret-var→val
             ; shiftᶜ = shiftᶜ
             ; shift-retˢ = shift-retˢ
             ; shift-retᵗ = shift-retᵗ
             ; ret-shift = ret-shift
             ; argᶠ = argᶠ
             ; argˢ = argˢ
             ; op-congᵗ = op-congᵗ
             ; op-shiftᵗ = op-shiftᵗ
             }
  open FuseFoldFoldAux FFFAux hiding (argᶠ; argˢ)
  
{-
        op-cong : ∀ op rs rsˢ (τ : Envᵗ)
                → zip _⩳_ (fold-args τ (reify-args rs)) rsˢ
                → fold τ “ fold-op op rs ” ≡ fold-opˢ op rsˢ
-}
{-
        Need to ditch reify-args to get the right induction hypothesis
        to the client, but how? 
        Need environments extended in the right way depending on each
        fold and op!
-}
{-      This one uses reify a la Safe Universes.
        op-cong : ∀ op (args : Args (sig op)) (γ : Envᶠ) (τ : Envᵗ) (σ : Envˢ)
                → zip _⩳_ (fold-args τ (reify-args (fold-args γ args)))
                          (fold-args σ args)
                → fold τ “ fold γ (op ⦅ args ⦆) ” ≡ fold σ (op ⦅ args ⦆)
-}
  field op-cong : ∀ op (args : Args (sig op)) (γ : Envᶠ) (τ : Envᵗ) (σ : Envˢ)
                → γ ⨟ τ ≈ σ
                → ind-hyps 0 op (sig op) args (fold-args γ args)
                             (fold-args σ args) γ τ σ
                → fold τ “ fold γ (op ⦅ args ⦆) ” ≡ fold σ (op ⦅ args ⦆)


       
  fusion : ∀{γ : Envᶠ}{σ : Envˢ}{τ : Envᵗ} (M : ABT)
    → γ ⨟ τ ≈ σ
    → fold τ “ fold γ M ” ≡ fold σ M

{-
  fuse-arg : ∀{γ : Envᶠ}{σ : Envˢ}{τ : Envᵗ}{b : ℕ} (arg : Arg b)
    → γ ⨟ τ ≈ σ
    → fold-arg τ (reify-arg (fold-arg γ arg)) ⩳ fold-arg σ arg
  fuse-args : ∀{γ : Envᶠ}{σ : Envˢ}{τ : Envᵗ}{bs : List ℕ} (args : Args bs)
    → γ ⨟ τ ≈ σ
    → zip _⩳_ (fold-args τ (reify-args (fold-args γ args)))
              (fold-args σ args)
  fusion {γ}{σ}{τ} (` x) γ⨟τ≈σ = γ⨟τ≈σ x
  fusion {γ}{σ}{τ} (op ⦅ args ⦆) γ⨟τ≈σ =
     let pa = fuse-args args γ⨟τ≈σ in
     op-cong op args γ τ σ pa
  fuse-arg {γ} {σ} {τ} (ast M) γ⨟τ≈σ = fusion M γ⨟τ≈σ
  fuse-arg {γ} {σ} {τ} (bind arg) γ⨟τ≈σ refl = fuse-arg arg (ext-pres γ⨟τ≈σ)
  fuse-args {γ} {σ} {τ} nil γ⨟τ≈σ = tt
  fuse-args {γ} {σ} {τ}{b ∷ bs} (cons arg args) γ⨟τ≈σ =
      ⟨ fuse-arg {b = b} arg γ⨟τ≈σ , fuse-args {bs = bs} args γ⨟τ≈σ ⟩
-}

  fuse-arg : ∀{γ : Envᶠ}{σ : Envˢ}{τ : Envᵗ}{b : ℕ}
      (k : ℕ) {- which argument -}
      (arg : Arg b) op
      (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
      (rsˢ : Tuple (sig op) (Bind V C))
    → ind-hyp k op b arg  rsᶠ rsˢ γ τ σ
  fuse-args : ∀{γ : Envᶠ}{σ : Envˢ}{τ : Envᵗ}{bs : List ℕ}
      (k : ℕ)
      (args : Args bs) op
      (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
      (rsˢ : Tuple (sig op) (Bind V C))
    → ind-hyps k op bs args rsᶠ rsˢ γ τ σ
    
  fusion {γ}{σ}{τ} (` x) γ⨟τ≈σ = γ⨟τ≈σ x
  fusion {γ}{σ}{τ} (op ⦅ args ⦆) γ⨟τ≈σ =
     let IHs = fuse-args 0 args op (fold-args γ args) (fold-args σ args) in
     op-cong op args γ τ σ γ⨟τ≈σ IHs
  fuse-arg {γ} {σ} {τ}{zero} k (ast M) op rsᶠ rsˢ γ⨟τ≈σ = fusion M γ⨟τ≈σ
  fuse-arg {γ} {σ} {τ}{suc b} k (bind arg) op rsᶠ rsˢ =
      fuse-arg {γ , argᶠ op k rsᶠ}{σ , argˢ op k rsˢ}{τ , argˢ op k rsˢ}
                        k arg op rsᶠ rsˢ 
  fuse-args {γ} {σ} {τ} k nil op rsᶠ rsˢ = tt
  fuse-args {γ} {σ} {τ}{b ∷ bs} k (cons arg args) op rsᶠ rsˢ =
      ⟨ fuse-arg {b = b} k arg op rsᶠ rsˢ ,
        fuse-args {bs = bs} (suc k) args op rsᶠ rsˢ ⟩


