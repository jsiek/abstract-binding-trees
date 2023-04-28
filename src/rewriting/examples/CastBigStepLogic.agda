{-# OPTIONS --rewriting #-}
module rewriting.examples.CastBigStepLogic where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties 
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.CastBigStep
open import rewriting.examples.StepIndexedLogic2

downClosed⇓ : ∀ M R → downClosed (M ⇓ R)
downClosed⇓ M R zero M⇓Rk .zero z≤n = M⇓Rk
downClosed⇓ M R (suc k) M⇓Rk .zero z≤n = zero⇓
downClosed⇓ .($ _) .($ _) (suc k) lit⇓ (suc j) (s≤s j≤k) = lit⇓
downClosed⇓ .(ƛ _) .(ƛ _) (suc k) lam⇓ (suc j) (s≤s j≤k) = lam⇓
downClosed⇓ (L · M) R (suc k) (app⇓{N = N}{W} L⇓λN M⇓W w NW⇓R)
    (suc j) (s≤s j≤k) =
  app⇓ (downClosed⇓ L (ƛ N) k L⇓λN j j≤k)
       (downClosed⇓ M W k M⇓W j j≤k) w (downClosed⇓ (N [ W ]) R k NW⇓R j j≤k)
downClosed⇓ (L · M) .blame (suc k) (app⇓-blame-L L⇓Bk) (suc j) (s≤s j≤k) =
  app⇓-blame-L (downClosed⇓ L blame k L⇓Bk j j≤k)
downClosed⇓ (L · M) .blame (suc k) (app⇓-blame-R{V = V} L⇓Vk v M⇓Bk) (suc j) (s≤s j≤k) = app⇓-blame-R (downClosed⇓ L V k L⇓Vk j j≤k ) v
                       (downClosed⇓ M blame k M⇓Bk j j≤k)
downClosed⇓ (M ⟨ _ !⟩) (V ⟨ _ !⟩) (suc k) (inj⇓ M⇓Rk x) (suc j) (s≤s j≤k) =
   inj⇓ (downClosed⇓ M V k M⇓Rk j j≤k) x
downClosed⇓ (M ⟨ _ !⟩) .blame (suc k) (inj⇓-blame M⇓Bk) (suc j) (s≤s j≤k) =
   inj⇓-blame (downClosed⇓ M blame k M⇓Bk j j≤k)
downClosed⇓ (M ⟨ _ ?⟩) .blame (suc k) (proj⇓-blame M⇓Bk) (suc j) (s≤s j≤k) =
   proj⇓-blame (downClosed⇓ M blame k M⇓Bk j j≤k)
downClosed⇓ (M ⟨ _ ?⟩) R (suc k) (collapse⇓{V = V} M⇓Vk) (suc j) (s≤s j≤k) =
   collapse⇓ (downClosed⇓ M (R ⟨ _ !⟩) k M⇓Vk j j≤k)
downClosed⇓ (M ⟨ _ ?⟩) .blame (suc k) (collide⇓{V = V} M⇓V!k x)
   (suc j) (s≤s j≤k) =
   collide⇓ (downClosed⇓ M (V ⟨ _ !⟩) k M⇓V!k j j≤k) x
downClosed⇓ .blame .blame (suc k) blame⇓ (suc j) (s≤s j≤k) = blame⇓
