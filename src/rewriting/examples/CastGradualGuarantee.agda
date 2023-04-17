{-# OPTIONS --rewriting #-}
module rewriting.examples.CastGradualGuarantee where

open import Data.List using (List; []; _∷_; length)
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
open import rewriting.examples.CastDeterministic
open import rewriting.examples.StepIndexedLogic2

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Prec × Term × Term) ⊎ (Prec × Term × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

ℰˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A⊑B ⟧ M M′ = (inj₂ (A⊑B , M , M′)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A⊑B ⟧ V V′ = (inj₁ (A⊑B , V , V′)) ∈ zeroˢ

pre-𝒱 : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 (.★ , ★ , unk⊑) (V ⟨ G !⟩) (V′ ⟨ H !⟩)
  with G ≡ᵍ H
... | yes refl = let g = gnd⇒ty G in ▷ˢ (𝒱ˢ⟦ (g , g , Refl⊑) ⟧ V V′)
... | no neq = ⊥ ˢ
pre-𝒱 (.★ , $ₜ ι , unk⊑) V V′ = {!!}
pre-𝒱 (.★ , A′ ⇒ B′ , unk⊑) V V′ = {!!}
pre-𝒱 (.($ₜ _) , .($ₜ _) , base⊑) V V′ = {!!}
pre-𝒱 (.(_ ⇒ _) , .(_ ⇒ _) , fun⊑ A⊑A′ A⊑A′₁) V V′ = {!!}
pre-𝒱 (A , A′ , A⊑A′) V V′ = ⊥ ˢ
