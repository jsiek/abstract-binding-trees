{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastSafeLogic2 where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤ᵖ; tt to ttᵖ)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.StepIndexedLogic2
open import rewriting.examples.CastLogRelLogic2

{-# REWRITE sub-var #-}

compatibility-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatibility-var {Γ}{A}{x} ∋x γ =
     let ⊢𝓥γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ A ⟧ (γ x)
         ⊢𝓥γx = lookup-𝓖 Γ γ ∋x in
     let ⊢𝓔γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⟧ (γ x)
         ⊢𝓔γx = 𝓥⇒𝓔{A}{𝓖⟦ Γ ⟧ γ} ⊢𝓥γx in
     ⊢𝓔γx

compatible-nat : ∀{Γ}{n : ℕ} → Γ ⊨ ($ n) ⦂ ($ₜ ′ℕ)
compatible-nat {Γ}{n} γ =
     let ⊢𝓥n : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ $ₜ ′ℕ ⟧ ($ n)
         ⊢𝓥n = λ { zero x → tt ; (suc k) x → refl} in
     let ⊢𝓔n : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ $ₜ ′ℕ ⟧ ($ n)
         ⊢𝓔n = 𝓥⇒𝓔{$ₜ ′ℕ}{𝓖⟦ Γ ⟧ γ} ⊢𝓥n in
     ⊢𝓔n

compatible-bool : ∀{Γ}{b : 𝔹} → Γ ⊨ ($ b) ⦂ ($ₜ ′𝔹)
compatible-bool {Γ}{b} γ =
     let ⊢𝓥b : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ $ₜ ′𝔹 ⟧ ($ b)
         ⊢𝓥b = λ { zero x → tt ; (suc k) x → refl} in
     let ⊢𝓔b : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ $ₜ ′𝔹 ⟧ ($ b)
         ⊢𝓔b = 𝓥⇒𝓔{$ₜ ′𝔹}{𝓖⟦ Γ ⟧ γ} ⊢𝓥b in
     ⊢𝓔b

compatible-app : ∀{Γ}{A}{B}{L}{M}
    → Γ ⊨ L ⦂ (A ⇒ B)
    → Γ ⊨ M ⦂ A
      -------------------
    → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M γ = ⊢𝓔LM
  where
  ⊢𝓔L : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⇒ B ⟧ (⟪ γ ⟫ L)
  ⊢𝓔L = ⊨L γ

  ⊢𝓔M : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⟧ (⟪ γ ⟫ M)
  ⊢𝓔M = ⊨M γ

  𝓥L⊢𝓔LM : 𝓥⟦ A ⇒ B ⟧ (⟪ γ ⟫ L) ∷ 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ B ⟧ (⟪ γ ⟫ (L · M))
  𝓥L⊢𝓔LM = {!!}

  rdL→rdLM : reducible (⟪ γ ⟫ L) → reducible (⟪ γ ⟫ (L · M))
  rdL→rdLM (L′ , γL→L′) = _ , (ξξ (□· (⟪ γ ⟫ M)) refl refl γL→L′)

  𝓟₁ = reducible (⟪ γ ⟫ L) ᵒ ∷ 𝓖⟦ Γ ⟧ γ

  ⊢▷𝓔N : ∀ N (rdL : reducible (⟪ γ ⟫ L))
     → ((⟪ γ ⟫ (L · M)) —→ N)ᵒ ∷ 𝓖⟦ Γ ⟧ γ ⊢ᵒ ▷ᵒ (𝓔⟦ B ⟧ N)
  ⊢▷𝓔N N rdL = Sᵒ⊢ᵒ (𝓖⟦ Γ ⟧ γ){(⟪ γ ⟫ (L · M)) —→ N} {▷ᵒ (𝓔⟦ B ⟧ N)}
           {!!}
      where
      Goal : ∀ N (rdL : reducible (⟪ γ ⟫ L)) (LM→N : ⟪ γ ⟫ (L · M) —→ N)
             → 𝓖⟦ Γ ⟧ γ ⊢ᵒ ▷ᵒ (𝓔⟦ B ⟧ N)
      Goal N rdL LM→N
          with app-invL rdL LM→N
      ... | L′ , L→L′ , refl =
            let x : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ▷ᵒ (𝓔⟦ B ⟧ (L′ · (⟪ γ ⟫ M)))
                x = {!!} in
            x

  presLM′ : reducible (⟪ γ ⟫ L) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ preservation B (⟪ γ ⟫ (L · M))
  presLM′ rdL = ⊢ᵒ-∀-intro{𝓖⟦ Γ ⟧ γ}{Term}
                   {λ N → (((⟪ γ ⟫ (L · M)) —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ B ⟧ N))}
                   λ N → ⊢ᵒ-→-intro {𝓖⟦ Γ ⟧ γ}{((⟪ γ ⟫ (L · M)) —→ N)ᵒ}
                             {▷ᵒ (𝓔⟦ B ⟧ N)} (⊢▷𝓔N N rdL)
  {-
  preservation A M = (∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)))
  -}
  
  presLM : 𝓟₁ ⊢ᵒ preservation B (⟪ γ ⟫ (L · M))
  presLM = Sᵒ⊢ᵒ (𝓖⟦ Γ ⟧ γ) {(reducible (⟪ γ ⟫ L))}
                 {preservation B (⟪ γ ⟫ (L · M))} presLM′

  rdL⊢𝓔LM : 𝓟₁ ⊢ᵒ 𝓔⟦ B ⟧ (⟪ γ ⟫ (L · M))
  rdL⊢𝓔LM =
      let rdL : 𝓟₁ ⊢ᵒ (reducible (⟪ γ ⟫ L))ᵒ
          rdL = ⊢ᵒ-hyp {𝓖⟦ Γ ⟧ γ}{(reducible (⟪ γ ⟫ L))ᵒ} in
      let rdLM : 𝓟₁ ⊢ᵒ (reducible (⟪ γ ⟫ (L · M)))ᵒ
          rdLM = Sᵒ→Tᵒ⇒⊢ᵒ 𝓟₁ rdL rdL→rdLM in
      𝓔-intro 𝓟₁ (⊢ᵒ-inj₂ {𝓟₁}{𝓥⟦ B ⟧ (⟪ γ ⟫ (L · M))}
                      {(reducible (⟪ γ ⟫ (L · M)))ᵒ ⊎ᵒ (Blame (⟪ γ ⟫ (L · M)))ᵒ}
                      (⊢ᵒ-inj₁ {𝓟₁}{(reducible (⟪ γ ⟫ (L · M)))ᵒ}
                               {(Blame (⟪ γ ⟫ (L · M)))ᵒ} rdLM))
                  presLM 

  blL⊢𝓔LM : (Blame (⟪ γ ⟫ L)) ᵒ ∷ 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ B ⟧ (⟪ γ ⟫ (L · M))
  blL⊢𝓔LM = {!!}

  ⊢𝓔LM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ B ⟧ (⟪ γ ⟫ (L · M))
  ⊢𝓔LM =
     let progL = 𝓔-progress (𝓖⟦ Γ ⟧ γ) ⊢𝓔L in
     ⊢ᵒ-case3 {𝓖⟦ Γ ⟧ γ}{𝓥⟦ A ⇒ B ⟧ (⟪ γ ⟫ L)}{(reducible (⟪ γ ⟫ L))ᵒ}
              {(Blame (⟪ γ ⟫ L))ᵒ}{𝓔⟦ B ⟧ (⟪ γ ⟫ (L · M))}
              progL 𝓥L⊢𝓔LM rdL⊢𝓔LM blL⊢𝓔LM

