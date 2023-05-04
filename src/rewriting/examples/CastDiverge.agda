{-# OPTIONS --rewriting #-}
module rewriting.examples.CastDiverge where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Maybe
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.CastBigStep
open import rewriting.examples.StepIndexedLogic2

{----- Diverge ------}

data ⇑ : Term → ℕ → Set where
  ⇑zero : ∀{M} → ⇑ M zero
  ⇑app : ∀{L M N W k}
     → L ⇓ ƛ N
     → M ⇓ W → Value W
     → ⇑ (N [ W ]) k
     → ⇑ (L · M) (suc k)
  ⇑app-L : ∀{L M k} → ⇑ L k → ⇑ (L · M) (suc k)
  ⇑app-R : ∀{L M N k} → L ⇓ ƛ N → ⇑ M k → ⇑ (L · M) (suc k)
  ⇑inj : ∀{M G k}
     → ⇑ M (suc k)  {- was ⇑ M k   -Jeremy -}
     → ⇑ (M ⟨ G !⟩) (suc k)
  ⇑proj : ∀{M H k} → ⇑ M k → ⇑ (M ⟨ H ?⟩) (suc k)

downClosed⇑ : ∀ {M} → downClosed (⇑ M)
downClosed⇑ zero ⇑M .zero z≤n = ⇑zero
downClosed⇑ (suc k) ⇑M .zero z≤n = ⇑zero
downClosed⇑ (suc k) (⇑app L⇓ M⇓ w ⇑NW) (suc j) (s≤s j≤k) =
    ⇑app L⇓ M⇓ w (downClosed⇑ k ⇑NW j j≤k)
downClosed⇑ (suc k) (⇑app-L ⇑M) (suc j) (s≤s j≤k) =
    ⇑app-L (downClosed⇑ k ⇑M j j≤k)
downClosed⇑ (suc k) (⇑app-R x ⇑M) (suc j) (s≤s j≤k) =
    ⇑app-R x (downClosed⇑ k ⇑M j j≤k)
downClosed⇑ (suc k) (⇑inj ⇑M) (suc j) (s≤s j≤k) =
    ⇑inj (downClosed⇑ (suc k) ⇑M (suc j) (s≤s j≤k))
downClosed⇑ (suc k) (⇑proj ⇑M) (suc j) (s≤s j≤k) =
    ⇑proj (downClosed⇑ k ⇑M j j≤k)

{----- Diverge in SIL ------}

⇑ᵒ : Term → Setᵒ
⇑ᵒ M = record { # = ⇑ M
              ; down = downClosed⇑ 
              ; tz = ⇑zero
              }

{---- Lift Divergence Rules into SIL -----}

⊢ᵒ⇑app-L : ∀{𝒫}{L}{M}
 → 𝒫 ⊢ᵒ ▷ᵒ (⇑ᵒ L)
 → 𝒫 ⊢ᵒ ⇑ᵒ (L · M)
⊢ᵒ⇑app-L {𝒫}{L}{M} ⊢▷⇑L = ⊢ᵒ-intro
  λ { zero 𝒫z → ⇑zero
    ; (suc n) 𝒫sn → ⇑app-L (⊢ᵒ-elim ⊢▷⇑L (suc n) 𝒫sn) }

⊢ᵒ⇑app-R : ∀{𝒫}{L}{M}{N}
 → 𝒫 ⊢ᵒ (L ⇓ ƛ N)ᵒ
 → 𝒫 ⊢ᵒ ▷ᵒ (⇑ᵒ M)
 → 𝒫 ⊢ᵒ ⇑ᵒ (L · M)
⊢ᵒ⇑app-R {𝒫}{L}{M}{N} ⊢L⇓ ⊢▷⇑M = ⊢ᵒ-intro
  λ { zero _ → ⇑zero
    ; (suc n) 𝒫sn →
      ⇑app-R (⊢ᵒ-elim ⊢L⇓ (suc n) 𝒫sn) (⊢ᵒ-elim ⊢▷⇑M (suc n) 𝒫sn ) }

⊢ᵒ⇑app : ∀{𝒫}{L}{M}{N}{W}
 → 𝒫 ⊢ᵒ (L ⇓ ƛ N)ᵒ
 → 𝒫 ⊢ᵒ (M ⇓ W)ᵒ
 → 𝒫 ⊢ᵒ (Value W)ᵒ
 → 𝒫 ⊢ᵒ ▷ᵒ (⇑ᵒ (N [ W ]))
 → 𝒫 ⊢ᵒ ⇑ᵒ (L · M)
⊢ᵒ⇑app {𝒫}{L}{M}{N} ⊢L⇓ ⊢M⇓ ⊢w ⊢▷⇑NW = ⊢ᵒ-intro
  λ { zero _ → ⇑zero
    ; (suc n) 𝒫sn →
      ⇑app (⊢ᵒ-elim ⊢L⇓ (suc n) 𝒫sn)
           (⊢ᵒ-elim ⊢M⇓ (suc n) 𝒫sn)
           (⊢ᵒ-elim ⊢w (suc n) 𝒫sn)
           (⊢ᵒ-elim ⊢▷⇑NW (suc n) 𝒫sn) }

⊢⇑app-inv : ∀{𝒫}{L}{M}{R}
 → (▷ᵒ (⇑ᵒ L) ∷ 𝒫 ⊢ᵒ R)
 → (∀ N → (L ⇓ ƛ N)ᵒ ∷ ▷ᵒ (⇑ᵒ M) ∷ 𝒫 ⊢ᵒ R)
 → (∀ N W → (L ⇓ ƛ N)ᵒ ∷ (M ⇓ W)ᵒ ∷ (Value W)ᵒ ∷ ▷ᵒ (⇑ᵒ (N [ W ]))
       ∷ 𝒫 ⊢ᵒ R)
 → ⇑ᵒ (L · M) ∷ 𝒫 ⊢ᵒ R
⊢⇑app-inv {𝒫}{L}{M}{R} c1 c2 c3 =
  ⊢ᵒ-intro λ
  { zero x → tz R
  ; (suc n) (⇑app-L ⇑Ln , 𝒫sn) →
     ⊢ᵒ-elim c1 (suc n) (⇑Ln , 𝒫sn)
  ; (suc n) (⇑app-R L⇓ ⇑Mn , 𝒫sn) →
     ⊢ᵒ-elim (c2 _) (suc n) (L⇓ , ⇑Mn , 𝒫sn)
  ; (suc n) (⇑app L⇓ M⇓ w ⇑NWn , 𝒫sn) → 
     ⊢ᵒ-elim (c3 _ _) (suc n) (L⇓ , M⇓ , w , ⇑NWn , 𝒫sn)
  }

⊢⇑inj : ∀{𝒫}{M}{G}
 → 𝒫 ⊢ᵒ (⇑ᵒ M)
 → 𝒫 ⊢ᵒ ⇑ᵒ (M ⟨ G !⟩)
⊢⇑inj {𝒫}{M}{G} ⊢⇑M = ⊢ᵒ-intro
  λ { zero 𝒫n → ⇑zero
    ; (suc n) 𝒫n → ⇑inj (⊢ᵒ-elim ⊢⇑M (suc n) 𝒫n)}

⊢⇑inj-inv : ∀{𝒫}{M}{G}{R}
  → (⇑ᵒ M) ∷ 𝒫 ⊢ᵒ R
  → ⇑ᵒ (M ⟨ G !⟩) ∷ 𝒫 ⊢ᵒ R
⊢⇑inj-inv {𝒫}{M}{G}{R} ⇑M⊢R = ⊢ᵒ-intro
  λ { zero _ → tz R
    ; (suc n) (⇑inj ⇑Mn , 𝒫sn) → ⊢ᵒ-elim ⇑M⊢R (suc n) (⇑Mn , 𝒫sn) }
