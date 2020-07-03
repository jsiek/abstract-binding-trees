open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import experimental.Environment
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Var

module experimental.Map (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import experimental.GSubst
open Shiftable {{...}}
open Quotable {{...}}

map : ∀{ℓ}{V : Set ℓ}
   {{_ : Shiftable V}} {{_ : Quotable V}}
   → GSubst V → ABT → ABT

map-arg : ∀{ℓ}{V : Set ℓ}
   {{_ : Shiftable V}} {{_ : Quotable V}}
   → GSubst V → {b : ℕ} →  Arg b → Arg b
map-args : ∀{ℓ}{V : Set ℓ}
   {{_ : Shiftable V}} {{_ : Quotable V}}
   → GSubst V → {bs : List ℕ} →  Args bs → Args bs
map σ (` x) = “ σ x ”
map {V} σ (op ⦅ args ⦆) = op ⦅ map-args σ args ⦆
map-arg σ (ast M) = ast (map σ M)
map-arg σ (bind M) = bind (map-arg (ext σ) M)
{-
map-arg σ (perm f f⁻¹ inv M) =
    perm f f⁻¹ inv (map-arg (f ∘ σ ∘ f⁻¹) M)
-}
map-args σ {[]} nil = nil
map-args σ {b ∷ bs} (cons x args) = cons (map-arg σ x) (map-args σ args)

_∘_≈_ : ∀{ℓ₁}{ℓ₂}{ℓ₃}{V₁ : Set ℓ₁}{V₂ : Set ℓ₂}{V₃ : Set ℓ₃}
        {{M₁ : Shiftable V₁}} {{M₂ : Shiftable V₂}} {{M₃ : Shiftable V₃}}
        {{Q₁ : Quotable V₁}}{{Q₂ : Quotable V₂}}{{Q₃ : Quotable V₃}}
        (σ₂ : GSubst V₂)(σ₁ : GSubst V₁)(σ₃ : GSubst V₃) → Set
_∘_≈_ {V₁}{V₂}{V₃}{{M₁}}{{M₂}}{{M₃}} σ₂ σ₁ σ₃ =
  ∀ x → map σ₂ “ σ₁ x ” ≡ “ σ₃ x ”

map-map-fusion-ext : ∀{ℓ₁}{ℓ₂}{ℓ₃}  {V₁ : Set ℓ₁}
  {V₂ : Set ℓ₂}  {V₃ : Set ℓ₃}
  {{_ : Shiftable V₁}} {{_ : Shiftable V₂}} {{_ : Shiftable V₃}}
  {{_ : Quotable V₁}} {{_ : Quotable V₂}} {{_ : Quotable V₃}}
  {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
   → (M : ABT)
   → σ₂ ∘ σ₁ ≈ σ₃
   → (∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
      → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃)
{-
   → (∀{σ₁ : E₁}{σ₂ : E₂}{σ₃ : E₃}{xs : List Var}
      → σ₂ ∘ σ₁ ≈ σ₃ → π xs σ₂ ∘ π xs σ₁ ≈ π xs σ₃)
-}
   → map σ₂ (map σ₁ M) ≡ map σ₃ M
map-map-fusion-ext (` x) σ₂∘σ₁≈σ₃ mf-ext {-mf-perm-} = σ₂∘σ₁≈σ₃ x
map-map-fusion-ext (op ⦅ args ⦆) σ₂∘σ₁≈σ₃ mf-ext {-mf-perm-} =
  cong (_⦅_⦆ op) (mmf-args args σ₂∘σ₁≈σ₃)
  where
  mmf-arg : ∀{σ₁}{σ₂}{σ₃}{b} (arg : Arg b) → σ₂ ∘ σ₁ ≈ σ₃
     → map-arg σ₂ (map-arg σ₁ arg) ≡ map-arg σ₃ arg
  mmf-args : ∀{σ₁ σ₂ σ₃ bs} (args : Args bs) → σ₂ ∘ σ₁ ≈ σ₃
     → map-args σ₂ (map-args σ₁ args) ≡ map-args σ₃ args
  mmf-arg (ast M) σ₂∘σ₁≈σ₃ =
      cong ast (map-map-fusion-ext M σ₂∘σ₁≈σ₃ mf-ext {-mf-perm-})
  mmf-arg (bind arg) σ₂∘σ₁≈σ₃ =
      cong bind (mmf-arg arg (mf-ext σ₂∘σ₁≈σ₃))
{-
  mmf-arg {σ₁}{σ₂}{σ₃} (perm xs arg) σ₂∘σ₁≈σ₃ =
      {!!} {- cong (perm xs) (mmf-arg arg (mf-perm σ₂∘σ₁≈σ₃)) -}
-}
  mmf-args {bs = []} nil σ₂∘σ₁≈σ₃ = refl
  mmf-args {bs = b ∷ bs} (cons arg args) σ₂∘σ₁≈σ₃ =
      cong₂ cons (mmf-arg arg σ₂∘σ₁≈σ₃) (mmf-args args σ₂∘σ₁≈σ₃)

_≈_ : ∀{ℓ}{V₁ : Set ℓ}{V₂ : Set ℓ}
        {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
        {{_ : Quotable V₁}} {{_ : Quotable V₂}}
        (σ₂ : GSubst V₂)(σ₁ : GSubst V₁) → Set
_≈_ σ₁ σ₂ = ∀ x → “ σ₁ x ” ≡ “ σ₂ x ”

{- todo: generalize to map-cong to simulation -}
map-cong : ∀{ℓ}{V₁ : Set ℓ}{V₂ : Set ℓ}
   {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
   {{_ : Quotable V₁}} {{_ : Quotable V₂}}
   {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}
   → (M : ABT)
   → σ₁ ≈ σ₂
   → (∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂} → σ₁ ≈ σ₂ → ext σ₁ ≈ ext σ₂)
{-
   → (∀{σ₁ : E₁}{σ₂ : E₂}{xs : List Var} → σ₁ ≈ σ₂ → π xs σ₁ ≈ π xs σ₂)
-}
   → map σ₁ M ≡ map σ₂ M
map-cong (` x) σ₁≈σ₂ mc-ext {-mc-perm-} = σ₁≈σ₂ x
map-cong (op ⦅ args ⦆) σ₁≈σ₂ mc-ext {-mc-perm-} =
  cong (_⦅_⦆ op) (mc-args args σ₁≈σ₂)
  where
  mc-arg : ∀{σ₁ σ₂ b} (arg : Arg b) → σ₁ ≈ σ₂
     → map-arg σ₁ arg ≡ map-arg σ₂ arg
  mc-args : ∀{σ₁ σ₂ bs} (args : Args bs) → σ₁ ≈ σ₂
     → map-args σ₁ args ≡ map-args σ₂ args
  mc-arg (ast M) σ₁≈σ₂ =
      cong ast (map-cong M σ₁≈σ₂ mc-ext {-mc-perm-})
  mc-arg (bind arg) σ₁≈σ₂ =
      cong bind (mc-arg arg (mc-ext σ₁≈σ₂))
{-
  mc-arg (perm xs arg) σ₁≈σ₂ =
      cong (perm xs) (mc-arg arg (mc-perm σ₁≈σ₂))
-}
  mc-args {bs = []} nil σ₁≈σ₂ = refl
  mc-args {bs = b ∷ bs} (cons arg args) σ₁≈σ₂ =
      cong₂ cons (mc-arg arg σ₁≈σ₂) (mc-args args σ₁≈σ₂)

_⊢_≈_ : ∀{ℓ}{V₁ : Set ℓ}{V₂ : Set ℓ}
        {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
        {{_ : Quotable V₁}} {{_ : Quotable V₂}}
        (M : ABT)(σ₂ : GSubst V₂)(σ₁ : GSubst V₁) → Set
_⊢_≈_ M σ₁ σ₂ = ∀ x → FV M x → “ σ₁ x ” ≡ “ σ₂ x ”

_⊢ₐ_≈_ : ∀{ℓ}{V₁ : Set ℓ}{V₂ : Set ℓ}
        {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
        {{_ : Quotable V₁}} {{_ : Quotable V₂}}
        {b : ℕ}(arg : Arg b)(σ₂ : GSubst V₂)(σ₁ : GSubst V₁) → Set
_⊢ₐ_≈_ {b} arg σ₁ σ₂ = ∀ x → FV-arg arg x → “ σ₁ x ” ≡ “ σ₂ x ”

_⊢₊_≈_ : ∀{ℓ}{V₁ : Set ℓ}{V₂ : Set ℓ}
        {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
        {{_ : Quotable V₁}} {{_ : Quotable V₂}}
        {bs : List ℕ}(args : Args bs)(σ₂ : GSubst V₂)(σ₁ : GSubst V₁) → Set
_⊢₊_≈_ {bs} args σ₁ σ₂ = ∀ x → FV-args args x → “ σ₁ x ” ≡ “ σ₂ x ”


map-cong-FV : ∀{ℓ}{V₁ : Set ℓ}{V₂ : Set ℓ}
   {{_ : Shiftable V₁}} {{_ : Shiftable V₂}}
   {{_ : Quotable V₁}} {{_ : Quotable V₂}}
   {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}
   → (M : ABT)
   → M ⊢ σ₁ ≈ σ₂
   → (∀{b}{arg : Arg b}{σ₁ : GSubst V₁}{σ₂ : GSubst V₂}
        → bind arg ⊢ₐ σ₁ ≈ σ₂ → arg ⊢ₐ ext σ₁ ≈ ext σ₂)
{-
   → (∀{b}{arg : Arg b}{σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{xs : List Var}
        → arg ⊢ₐ σ₁ ≈ σ₂ → arg ⊢ₐ π xs σ₁ ≈ π xs σ₂)
-}
   → map σ₁ M ≡ map σ₂ M
map-cong-FV (` x) σ₁≈σ₂ mc-ext {-mc-perm-} = σ₁≈σ₂ x refl
map-cong-FV (op ⦅ args ⦆) σ₁≈σ₂ mc-ext {-mc-perm-} =
    cong (_⦅_⦆ op) (mc-args args σ₁≈σ₂)
    where
    mc-arg : ∀{σ₁ σ₂ b} (arg : Arg b) → arg ⊢ₐ σ₁ ≈ σ₂
       → map-arg σ₁ arg ≡ map-arg σ₂ arg
    mc-args : ∀{σ₁ σ₂ bs} (args : Args bs) → args ⊢₊ σ₁ ≈ σ₂
       → map-args σ₁ args ≡ map-args σ₂ args
    mc-arg (ast M) σ₁≈σ₂ =
        cong ast (map-cong-FV M σ₁≈σ₂ (λ{b}{arg} → mc-ext {b}{arg})
                                      {-(λ{b}{arg} → mc-perm {b}{arg})-})
    mc-arg {σ₁}{σ₂}{b = suc b} (bind arg) σ₁≈σ₂ =
        cong bind (mc-arg arg (mc-ext {b}{arg} σ₁≈σ₂))
{-
    mc-arg {σ₁}{σ₂}{b} (perm xs arg) σ₁≈σ₂ =
        cong (perm xs) (mc-arg arg (mc-perm {b}{arg} σ₁≈σ₂))
-}
    mc-args {bs = []} nil σ₁≈σ₂ = refl
    mc-args {σ₁}{σ₂}{bs = b ∷ bs} (cons arg args) σ₁≈σ₂ =
        cong₂ cons (mc-arg arg G) (mc-args args H)
        where
        G : arg ⊢ₐ σ₁ ≈ σ₂
        G x x∈arg = σ₁≈σ₂ x (inj₁ x∈arg)
        H : args ⊢₊ σ₁ ≈ σ₂
        H x x∈args = σ₁≈σ₂ x (inj₂ x∈args)
