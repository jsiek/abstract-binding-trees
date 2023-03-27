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

𝓔⊎𝓥-type : Set
𝓔⊎𝓥-type = (Type × Term) ⊎ (Type × Term)

𝓥ᶠ⟦_⟧ : Type → Term → Fun 𝓔⊎𝓥-type ⊤ Continuous
𝓥ᶠ⟦ A ⟧ V = recur (inj₁ (A , V))

𝓔ᶠ⟦_⟧ : Type → Term → Fun 𝓔⊎𝓥-type ⊤ Continuous
𝓔ᶠ⟦ A ⟧ M = recur (inj₂ (A , M))

pre-𝓥 : Type → Term → Fun 𝓔⊎𝓥-type ⊤ Wellfounded
pre-𝓥 ★ (op-inject{G} g ⦅ cons (ast V) nil ⦆) = -- (V ⟨ g !⟩ )
    (Value V)ᶠ ×ᶠ ▷ᶠ (𝓥ᶠ⟦ G ⟧ V)
pre-𝓥 ($ₜ ι) (op-lit {ι′} c ⦅ nil ⦆) =   -- ($ c)
    (ι ≡ ι′)ᶠ
pre-𝓥 (A ⇒ B) (ƛ N) =
    ∀ᶠ[ W ] ▷ᶠ (𝓥ᶠ⟦ A ⟧ W) →ᶠ ▷ᶠ (𝓔ᶠ⟦ B ⟧ (N [ W ]))

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
pre-𝓔 : Type → Term
       → Fun 𝓔⊎𝓥-type ⊤ Wellfounded
pre-𝓔 A M = (pre-𝓥 A M ⊎ᶠ (reducible M)ᶠ)          -- Progress
             ×ᶠ (∀ᶠ[ N ] (M —→ N)ᶠ →ᶠ ▷ᶠ (𝓔ᶠ⟦ A ⟧ N)) -- Preservation

pre-𝓔⊎𝓥 : 𝓔⊎𝓥-type → Fun 𝓔⊎𝓥-type ⊤ Wellfounded
pre-𝓔⊎𝓥 (inj₁ (A , V)) = pre-𝓥 A V
pre-𝓔⊎𝓥 (inj₂ (A , M)) = pre-𝓔 A M

𝓔⊎𝓥 : Fun 𝓔⊎𝓥-type 𝓔⊎𝓥-type Wellfounded
𝓔⊎𝓥 = flipᶠ pre-𝓔⊎𝓥 tt

-- Semantically Well Typed Value
𝓥⟦_⟧ : (A : Type) → Term → Setᵒ
𝓥⟦ A ⟧ V = apply (μᵖ 𝓔⊎𝓥) (inj₁ (A , V))

-- Semantically Well Typed Term
𝓔⟦_⟧ : (A : Type) → Term → Setᵒ
𝓔⟦ A ⟧ M = apply (μᵖ 𝓔⊎𝓥) (inj₂ (A , M))

𝓔⊎𝓥-fixpointₚ : #(μᵖ 𝓔⊎𝓥) ≡ₚ #((fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥))
𝓔⊎𝓥-fixpointₚ = fixpoint 𝓔⊎𝓥

𝓔⊎𝓥-fixpointₒ : ∀ x → #(μᵖ 𝓔⊎𝓥) x ≡ₒ #((fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥)) x
𝓔⊎𝓥-fixpointₒ x = fixpoint 𝓔⊎𝓥 x


𝓔-def : ∀{A}{M}
  → #(𝓔⟦ A ⟧ M) ≡ₒ (#(𝓥⟦ A ⟧ M) ⊎ₒ (reducible M)ₒ)
                    ×ₒ (∀ₒ[ N ] ((M —→ N)ₒ →ₒ ▷ₒ #(𝓔⟦ A ⟧ N)))
𝓔-def {A}{M} =
  #(𝓔⟦ A ⟧ M)                                                ≡ₒ⟨ ≡ₒ-refl refl ⟩
  #(μᵖ 𝓔⊎𝓥) (inj₂ (A , M))                 ≡ₒ⟨ 𝓔⊎𝓥-fixpointₒ (inj₂ (A , M)) ⟩
  #((fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥)) (inj₂ (A , M))
                  ≡ₒ⟨ cong-×ₒ (cong-⊎ₒ (≡ₒ-sym (𝓔⊎𝓥-fixpointₒ (inj₁ (A , M))))
                                              (≡ₒ-refl refl)) (≡ₒ-refl refl) ⟩
  ((#(𝓥⟦ A ⟧ M) ⊎ₒ (reducible M)ₒ)
    ×ₒ (∀ₒ[ N ] ((M —→ N)ₒ →ₒ ▷ₒ #(𝓔⟦ A ⟧ N))))
  QEDₒ



-- 𝓥⇒Value : ∀ {k} A M → 𝓥⟦ A ⟧ M (suc k) → Value M
-- 𝓥⇒Value ★ (M ⟨ g !⟩) (v , _) = v 〈 g 〉
-- 𝓥⇒Value ($ₜ ι) ($ c) 𝓥M = $̬ c
-- 𝓥⇒Value (A ⇒ B) (ƛ N) 𝓥M = ƛ̬ N
-- -- vacuous cases
-- 𝓥⇒Value ★ (` x) ()
-- 𝓥⇒Value ★ ($ c) ()
-- 𝓥⇒Value ★ (ƛ N) ()
-- 𝓥⇒Value ★ (L · M) ()
-- 𝓥⇒Value ★ (M ⟨ h ?⟩) ()
-- 𝓥⇒Value ★ blame ()
-- 𝓥⇒Value ($ₜ ι) (` x) ()
-- 𝓥⇒Value ($ₜ ι) (ƛ N) ()
-- 𝓥⇒Value ($ₜ ι) (L · M) ()
-- 𝓥⇒Value ($ₜ ι) (M ⟨ g !⟩) ()
-- 𝓥⇒Value ($ₜ ι) (M ⟨ h ?⟩) ()
-- 𝓥⇒Value ($ₜ ι) blame ()
-- 𝓥⇒Value (A ⇒ B) (` x) ()
-- 𝓥⇒Value (A ⇒ B) ($ c) ()
-- 𝓥⇒Value (A ⇒ B) (L · M) ()
-- 𝓥⇒Value (A ⇒ B) (M ⟨ g !⟩) ()
-- 𝓥⇒Value (A ⇒ B) (M ⟨ h ?⟩) ()
-- 𝓥⇒Value (A ⇒ B) blame ()


-- V-base-intro : ∀{n}{ι}{c : rep ι}
--    → 𝓥⟦ $ₜ ι ⟧ ($ c) n
-- V-base-intro {zero} = tt
-- V-base-intro {suc n}{ι}{c} = refl

-- V-base-elim : ∀{n}{ι}{ι′}{c : rep ι′}
--    → 𝓥⟦ $ₜ ι ⟧ ($ c) (suc n)
--    → (ι ≡ ι′)
-- V-base-elim {n} refl = refl

-- V-dyn-intro : ∀{G}{V}{g : Ground G}{n}
--    → Value V
--    → 𝓥⟦ G ⟧ V n
--    → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) (suc n)
-- V-dyn-intro {G}{V}{g}{n} v 𝓥V =
--     let 𝓥V′ : # (fun (pre-𝓥 G V) (μᵖ 𝓔⊎𝓥)) tt n
--         𝓥V′ = 𝓥V in
--     let 𝓥V″ : # (fun (pre-𝓥 G V) {!!}) tt n
--         𝓥V″ = {!!} in
--     let 𝓔n = (iter n (flip pre-𝓔 tt) ⊤ᵖ) in
--     let xx = congr (pre-𝓥 G V) 𝓔n (μᵖ 𝓔⊎𝓥) {!!} in
--     v , (inj₁ Goal) , {!!}
--     where
--     Goal : # (fun (pre-𝓥 G V) (iter n (flip pre-𝓔 tt) ⊤ᵖ)) tt n
--     Goal = {!!}

-- --    let unroll = proj₁ (𝓔⊎𝓥-fixpointₚ (G , V) n) in
-- --    let x = unroll 𝓔V in
-- --    let P = apply (fun (pre-𝓔 (G , V)) (iter n (flip pre-𝓔 tt) ⊤ᵖ)) tt in
-- --    {-
-- --    # (fun (pre-𝓔 (G , V)) (iter n (flip pre-𝓔 tt) ⊤ᵖ)) tt)
-- --    -}
-- --    (value-irred (v 〈 g 〉)) , {!!}
-- --    --(inj₁ (v , ▷ᵒ-intro{n}{P} {!!}))
