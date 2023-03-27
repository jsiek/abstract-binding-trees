{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastLogRelLogic2 where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
--open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using (⊤; tt)
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
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import Structures using (extensionality)
open import rewriting.examples.Cast
open import rewriting.examples.StepIndexedLogic2

pre-𝓥 : Type → Term → Fun (Type × Term) ⊤ Wellfounded
pre-𝓥 ★ (op-inject{G} g ⦅ cons (ast V) nil ⦆) =
    (Value V)ᶠ ×ᶠ ▷ᶠ (recur (G , V))
pre-𝓥 ($ₜ ι) (op-lit {ι′} c ⦅ nil ⦆) = (ι ≡ ι′)ᶠ
pre-𝓥 (A ⇒ B) (ƛ N) =
    ∀ᶠ{Term} λ W → ▷ᶠ (recur (A , W)) →ᶠ (irred W)ᶠ →ᶠ
                   ▷ᶠ (recur (A , N [ W ]))

-- bogus cases for ★
pre-𝓥 ★ (` x) = (⊥) ᶠ
pre-𝓥 ★ ($ c) = (⊥) ᶠ
pre-𝓥 ★ (ƛ N) = (⊥) ᶠ
pre-𝓥 ★ (L · M) = (⊥) ᶠ
pre-𝓥 ★ (M ⟨ h ?⟩) = (⊥) ᶠ
pre-𝓥 ★ blame = (⊥) ᶠ

-- bogus cases for ι
pre-𝓥 ($ₜ ι) (` x) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) (ƛ N) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) (L · M) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) (M ⟨ g !⟩) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) (M ⟨ h ?⟩) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) blame = (⊥) ᶠ

-- bogus cases for A ⇒ B
pre-𝓥 (A ⇒ B) (` x) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) ($ c) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) (L · M) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) (M ⟨ g !⟩) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) (M ⟨ h ?⟩) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) blame = (⊥) ᶠ

-- Type Safety = Progress & Preservation
pre-𝓔 : Type × Term → Fun (Type × Term) ⊤ Wellfounded
pre-𝓔 (A , M) = (pre-𝓥 A M ⊎ᶠ (red M)ᶠ)
                 ×ᶠ ∀ᶠ{Term} λ N → ((M —→ N) ᶠ) →ᶠ ▷ᶠ (recur (A , N))

𝓔ᶠ : Fun (Type × Term) (Type × Term) Wellfounded
𝓔ᶠ = flipᶠ pre-𝓔 tt

𝓔⟦_⟧ : (A : Type) → Term → Setₒ
𝓔⟦ A ⟧ V = #(μᵖ 𝓔ᶠ) (A , V)

𝓔-fixpointₚ : #(μᵖ 𝓔ᶠ) ≡ₚ #((fun 𝓔ᶠ) (μᵖ 𝓔ᶠ))
𝓔-fixpointₚ = fixpoint 𝓔ᶠ

𝓔-fixpointₒ : ∀ A M → #(μᵖ 𝓔ᶠ) (A , M) ≡ₒ #((fun 𝓔ᶠ) (μᵖ 𝓔ᶠ)) (A , M)
𝓔-fixpointₒ A M = fixpoint 𝓔ᶠ (A , M)

𝓥⟦_⟧ : (A : Type) → Term → Setₒ
𝓥⟦ A ⟧ V = (λ k → # (fun (pre-𝓥 A V) (μᵖ 𝓔ᶠ)) tt k)

𝓔-def : ∀{A}{M}
  → 𝓔⟦ A ⟧ M ≡ₒ (𝓥⟦ A ⟧ M ⊎ₒ (red M)ₒ)
                ×ₒ ∀ₒ λ N → ((M —→ N) ₒ) →ₒ ▷ₒ 𝓔⟦ A ⟧ N
𝓔-def {A}{M} =
  𝓔⟦ A ⟧ M                                                    ≡ₒ⟨ ≡ₒ-refl refl ⟩
  #(μᵖ 𝓔ᶠ) (A , M)                                         ≡ₒ⟨ 𝓔-fixpointₒ A M ⟩
  #((fun 𝓔ᶠ) (μᵖ 𝓔ᶠ)) (A , M)                                 ≡ₒ⟨ ≡ₒ-refl refl ⟩
  ((𝓥⟦ A ⟧ M ⊎ₒ (red M)ₒ)
    ×ₒ ∀ₒ λ N → ((M —→ N) ₒ) →ₒ ▷ₒ 𝓔⟦ A ⟧ N)
  QEDₒ

𝓥⇒Value : ∀ {k} A M → 𝓥⟦ A ⟧ M (suc k) → Value M
𝓥⇒Value ★ (M ⟨ g !⟩) (v , _) = v 〈 g 〉
𝓥⇒Value ($ₜ ι) ($ c) 𝓥M = $̬ c
𝓥⇒Value (A ⇒ B) (ƛ N) 𝓥M = ƛ̬ N
-- vacuous cases
𝓥⇒Value ★ (` x) ()
𝓥⇒Value ★ ($ c) ()
𝓥⇒Value ★ (ƛ N) ()
𝓥⇒Value ★ (L · M) ()
𝓥⇒Value ★ (M ⟨ h ?⟩) ()
𝓥⇒Value ★ blame ()
𝓥⇒Value ($ₜ ι) (` x) ()
𝓥⇒Value ($ₜ ι) (ƛ N) ()
𝓥⇒Value ($ₜ ι) (L · M) ()
𝓥⇒Value ($ₜ ι) (M ⟨ g !⟩) ()
𝓥⇒Value ($ₜ ι) (M ⟨ h ?⟩) ()
𝓥⇒Value ($ₜ ι) blame ()
𝓥⇒Value (A ⇒ B) (` x) ()
𝓥⇒Value (A ⇒ B) ($ c) ()
𝓥⇒Value (A ⇒ B) (L · M) ()
𝓥⇒Value (A ⇒ B) (M ⟨ g !⟩) ()
𝓥⇒Value (A ⇒ B) (M ⟨ h ?⟩) ()
𝓥⇒Value (A ⇒ B) blame ()


V-base-intro : ∀{n}{ι}{c : rep ι}
   → 𝓥⟦ $ₜ ι ⟧ ($ c) n
V-base-intro {zero} = tt
V-base-intro {suc n}{ι}{c} = refl

V-base-elim : ∀{n}{ι}{ι′}{c : rep ι′}
   → 𝓥⟦ $ₜ ι ⟧ ($ c) (suc n)
   → (ι ≡ ι′)
V-base-elim {n} refl = refl

V-dyn-intro : ∀{G}{V}{g : Ground G}{n}
   → Value V
   → 𝓥⟦ G ⟧ V n
   → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) (suc n)
V-dyn-intro {G}{V}{g}{n} v 𝓥V = v , {!!}

--    let unroll = proj₁ (𝓔-fixpointₚ (G , V) n) in
--    let x = unroll 𝓔V in
--    let P = apply (fun (pre-𝓔 (G , V)) (iter n (flip pre-𝓔 tt) ⊤ᵖ)) tt in
--    {-
--    # (fun (pre-𝓔 (G , V)) (iter n (flip pre-𝓔 tt) ⊤ᵖ)) tt)
--    -}
--    (value-irred (v 〈 g 〉)) , {!!}
--    --(inj₁ (v , ▷ᵒ-intro{n}{P} {!!}))
