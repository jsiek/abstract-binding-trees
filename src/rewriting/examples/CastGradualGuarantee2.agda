{-# OPTIONS --rewriting #-}
module rewriting.examples.CastGradualGuarantee2 where

open import Data.List using (List; []; _∷_; length; map)
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
open import rewriting.examples.CastEval
open import rewriting.examples.StepIndexedLogic2

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Prec × Term × Term) ⊎ (Prec × Term × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

ℰˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A⊑B ⟧ M M′ = (inj₂ (A⊑B , M , M′)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A⊑B ⟧ V V′ = (inj₁ (A⊑B , V , V′)) ∈ zeroˢ

pre-ℰ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)

pre-𝒱 (.★ , ★ , unk⊑) (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = let g = gnd⇒ty G in
                 (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (▷ˢ (𝒱ˢ⟦ (g , g , Refl⊑) ⟧ V V′))
... | no neq = ⊥ ˢ
pre-𝒱 (.★ , $ₜ ι′ , unk⊑) (V ⟨ $ᵍ ι !⟩) ($ c)
    with ($ᵍ ι) ≡ᵍ ($ᵍ ι′)
... | yes refl = (Value V)ˢ ×ˢ ▷ˢ (𝒱ˢ⟦ ($ₜ ι , $ₜ ι , Refl⊑) ⟧ V ($ c))
... | no new = ⊥ ˢ
pre-𝒱 (.★ , A′ ⇒ B′ , unk⊑) (V ⟨ ★⇒★ !⟩) V′ =
    (Value V)ˢ ×ˢ (Value V′)ˢ
    ×ˢ ▷ˢ (𝒱ˢ⟦ (★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑) ⟧ V V′)
pre-𝒱 ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) = (c ≡ c′) ˢ
pre-𝒱 ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] (pre-𝒱 (A , A′ , A⊑A′) W W′)
                  →ˢ (pre-ℰ (B , B′ , B⊑B′) (N [ W ]) (N′ [ W′ ]))
pre-𝒱 (A , A′ , A⊑A′) V V′ = ⊥ ˢ

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

pre-ℰ c M M′ =
      (∀ˢ[ V′ ] (M′ ⇓ᵗ V′)ˢ →ˢ (∃ˢ[ V ] (M ⇓ᵗ V)ˢ ×ˢ pre-𝒱 c V V′))
   ×ˢ ((M′ ⇓ᵇ)ˢ →ˢ (M ⇓ᵇ)ˢ)
   ×ˢ ((M′ ⇑)ˢ →ˢ (M ⇑)ˢ)
   ×ˢ (∀ˢ[ V ]  (M ⇓ᵗ V)ˢ →ˢ ((∃ˢ[ V′ ] (M′ ⇓ᵗ V′)ˢ ×ˢ pre-𝒱 c V V′)
                            ⊎ˢ (M′ ⇓ᵇ)ˢ))
   ×ˢ ((M ⇓ᵇ)ˢ →ˢ (M′ ⇓ᵇ)ˢ)
   ×ˢ ((M ⇑)ˢ →ˢ ((M′ ⇑)ˢ ⊎ˢ (M′ ⇓ᵇ)ˢ))

