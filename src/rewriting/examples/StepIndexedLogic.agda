{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.StepIndexedLogic where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)

Setᵒ : Set₁
Setᵒ = ℕ → Set

⊥ᵒ : Setᵒ
⊥ᵒ zero     =  ⊤
⊥ᵒ (suc n)  =  ⊥

_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
(P ⊎ᵒ Q) n  =  (P n) ⊎ (Q n)

⊤ᵒ : Setᵒ
⊤ᵒ n  =  ⊤

_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
(P ×ᵒ Q) n  =  (P n) × (Q n)

_→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
(P →ᵒ Q) n  =  ∀ k → k ≤ n → P k → Q k

∀ᵒ : ∀{A} → (A → Setᵒ) → Setᵒ
∀ᵒ {A} F n = ∀ (v : A) → F v n

_ᵒ  : Set → Setᵒ
(p ᵒ) zero = ⊤
(p ᵒ) (suc n) = p

▷ᵒ_ : Setᵒ → Setᵒ
(▷ᵒ P) zero     =  ⊤
(▷ᵒ P) (suc n)  =  P n

ee : Setᵒ → Set
ee P  =  P zero

ee-⊥ : ee ⊥ᵒ
ee-⊥ = tt

ee-⊤ : ee ⊤ᵒ
ee-⊤ = tt

ee-× : ∀ {P Q} → ee P → ee Q → ee (P ×ᵒ Q)
ee-× P0 Q0 = (P0 , Q0)

ee-→ : ∀ {P Q} → ee Q → ee (P →ᵒ Q)
ee-→ Q0 zero z≤n P0 = Q0

ee-∀ : ∀{A F}
   → (∀ v → ee (F v))
   → ee (∀ᵒ {A} F)
ee-∀ {F} eeF v = eeF v

ee-Pᵒ : (P : Set)
   → ee (P ᵒ)
ee-Pᵒ P = tt

dc : Setᵒ → Set
dc P  =  ∀ n → P n → ∀ k → k ≤ n → P k

dc-⊥ : dc ⊥ᵒ
dc-⊥ zero tt k z≤n  =   tt
dc-⊥ (suc n) ()

dc-⊎ : ∀ {P Q} → dc P → dc Q → dc (P ⊎ᵒ Q)
dc-⊎ dcP dcQ n (inj₁ Pn) k k≤n  =  inj₁ (dcP n Pn k k≤n)
dc-⊎ dcP dcQ n (inj₂ Qn) k k≤n  =  inj₂ (dcQ n Qn k k≤n)

dc-⊤ : dc ⊤ᵒ
dc-⊤  =  λ n ⊤ᵒn k k≤n → tt

dc-× : ∀ {P Q} → dc P → dc Q → dc (P ×ᵒ Q)
dc-× dcP dcQ n (Pn , Qn) k k≤n  =  dcP n Pn k k≤n , dcQ n Qn k k≤n

dc-→ᵒ : ∀ {P Q} → dc P → dc Q → dc (P →ᵒ Q)
dc-→ᵒ dcP dcQ n [P→ᵒQ]n k k≤n i i≤k Pi = [P→ᵒQ]n i (≤-trans i≤k k≤n) Pi

dc-∀ : ∀{A F}
  → (∀ v → dc (F v))
  → dc (∀ᵒ {A} F)
dc-∀ {A}{F} dcF n ∀Fn k k≤n v = dcF v n (∀Fn v) k k≤n

dc-Pᵒ : (P : Set)
   → dc (P ᵒ)
dc-Pᵒ P n Pn zero k≤n = tt
dc-Pᵒ P (suc n) Pn (suc k) (s≤s k≤n) = Pn

record Setₖ : Set₁ where
  field
    val : Setᵒ
    dcl : dc val
    ez : ee val
open Setₖ

_ₖ : Set → Setₖ
P ₖ = record { val = (P ᵒ) ; dcl = dc-Pᵒ P ; ez = ee-Pᵒ P }

⊥ₖ : Setₖ
⊥ₖ = record { val = ⊥ᵒ ; dcl = dc-⊥ ; ez = ee-⊥ }

⊤ₖ : Setₖ
⊤ₖ  = record { val = ⊤ᵒ ; dcl = dc-⊤ ; ez = ee-⊤ }

_×ₖ_ : Setₖ → Setₖ → Setₖ
(P ×ₖ Q) = record { val = (val P ×ᵒ val Q)
                  ; dcl = dc-× (dcl P) (dcl Q)
                  ; ez = ee-× {val P}{val Q} (ez P) (ez Q) }

_→ₖ_ : Setₖ → Setₖ → Setₖ
(P →ₖ Q) = record { val = (λ k → ∀ j → j ≤ k → val P j → val Q j)
                  ; dcl = dc-→ᵒ (dcl P) (dcl Q)
                  ; ez = (ee-→ (ez Q)) }

∀ₖ : ∀{A} → (A → Setₖ) → Setₖ
∀ₖ {A} P = record { val = (λ k → ∀ (v : A) → val (P v) k)
                  ; dcl = (λ n f k k≤n v → dcl (P v) n (f v) k k≤n)
                  ; ez = ee-∀ {F = λ x → val (P x)} λ v → ez (P v) }

▷_ : Setₖ → Setₖ
▷ P = record { val = ▷ᵒ (val P) ; dcl = G ; ez = H }
  where
  G : dc (▷ᵒ (val P))
  G n x zero k≤n = tt
  G (suc n) Pn (suc k) (s≤s k≤n) = (dcl P) n Pn k k≤n

  H : ee (▷ᵒ (val P))
  H = tt

Predₖ : Set → Set₁
Predₖ A = A → Setₖ

⊤ᴾ : ∀{A} → Predₖ A
⊤ᴾ x = ⊤ₖ

⊥ᴾ : ∀{A} → Predₖ A
⊥ᴾ x = ⊥ₖ

iter : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → (A → A)
iter zero    F  =  id
iter (suc n) F  =  F ∘ iter n F

monotonic : ∀{A} (F : Predₖ A → Predₖ A) → Set₁
monotonic F = ∀ P Q x i → (val (P x) i → val (Q x) i)
                        → (val (F P x) i → val (F Q x) i)

record Functional (A : Set) : Set₁ where
  field
    fun : Predₖ A → Predₖ A
    mono : monotonic fun
open Functional    

dc-iter-index : ∀{i j k : ℕ}{A}{F : Functional A}{x : A}
   → j ≤ k
   → val (iter i (fun F) ⊤ᴾ x) k
   → val (iter i (fun F) ⊤ᴾ x) j
dc-iter-index {zero} {j} {k} j≤k iterFk = tt
dc-iter-index {suc i} {j} {k}{A}{F}{x} j≤k iterFk =
   let dcF = dcl (fun F (iter i (fun F) ⊤ᴾ) x) in
   dcF k iterFk j j≤k

dc-iter-depth : ∀(i j k : ℕ){A}{F : Functional A}{x : A}
   → j ≤′ k
   → val (iter k (fun F) ⊤ᴾ x) i
   → val (iter j (fun F) ⊤ᴾ x) i
dc-iter-depth i j .j _≤′_.≤′-refl iterkF = iterkF
dc-iter-depth i zero (suc k) (≤′-step j≤k) iterkF = tt
dc-iter-depth i (suc j) (suc k) {A}{F}{x} (≤′-step j≤k) FiterkFi =
  mono F (iter k (fun F) ⊤ᴾ) (iter j (fun F) ⊤ᴾ) x i
                  (λ iterkFi → dc-iter-depth i j k {A}{F}
                      (≤⇒≤′ (≤-trans (n≤1+n _) (≤′⇒≤ j≤k))) iterkFi) FiterkFi

μᴾ : ∀{A} → (F : Functional A) → Predₖ A
(μᴾ {A} F) x = record
  { val = (λ k → val (iter k (fun F) ⊤ᴾ x) k) 
  ; dcl = (λ n Fnxn k k≤n →
             let Fnxk = dc-iter-index{n}{k}{n}{A}{F}{x} k≤n Fnxn in
             dc-iter-depth k k n {F = F}{x = x} (≤⇒≤′ k≤n) Fnxk)
  ; ez = tt }

Lob : ∀{P : Setₖ}
   → (∀ k → val (▷ P) k → val P k)
     -----------------------------
   → ∀ k → val P k
Lob ▷P→P zero = ▷P→P zero tt
Lob {P} ▷P→P (suc k) = ▷P→P (suc k) (Lob{P} ▷P→P k)

