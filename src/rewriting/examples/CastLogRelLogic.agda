{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastLogRelLogic where

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
open import rewriting.examples.StepIndexedLogic

pre-𝓔 : Predᵒ (Type × Term) → Predᵒ (Type × Term)
pre-𝓔 𝓥 (A , M) = ∀ᵒ(λ N → (M —↠ N)ᵒ →ᵒ (irred N)ᵒ →ᵒ (𝓥 (A , N) ⊎ᵒ (N ≡ blame)ᵒ))

pre-𝓥 : Predᵒ (Type × Term) → Predᵒ (Type × Term)
pre-𝓥 𝓥 (★ , (op-inject {G} g ⦅ cons (ast V) nil ⦆)) = 𝓥 (G , V)
pre-𝓥 𝓥 ($ₜ ι , ((op-lit {ι′} c) ⦅ nil ⦆)) = (ι ≡ ι′)ᵒ
pre-𝓥 𝓥 (A ⇒ B , ƛ N) = ∀ᵒ(λ W → 𝓥 (A , W) →ᵒ pre-𝓔 𝓥 (A , N [ W ]))
-- bogus cases for ★
pre-𝓥 𝓥 (★ , ` x) = ⊥ᵒ
pre-𝓥 𝓥 (★ , $ c) = ⊥ᵒ
pre-𝓥 𝓥 (★ , ƛ N) = ⊥ᵒ
pre-𝓥 𝓥 (★ ,  L · M) = ⊥ᵒ
pre-𝓥 𝓥 (★ , M ⟨ h ?⟩) = ⊥ᵒ
pre-𝓥 𝓥 (★  , blame ) = ⊥ᵒ
-- bogus cases for $ₜ ι
pre-𝓥 𝓥 ($ₜ ι , ` x) = ⊥ᵒ
pre-𝓥 𝓥 ($ₜ ι , ƛ N) = ⊥ᵒ
pre-𝓥 𝓥 ($ₜ ι , L · M) = ⊥ᵒ
pre-𝓥 𝓥 ($ₜ ι , M ⟨ h ?⟩) = ⊥ᵒ
pre-𝓥 𝓥 ($ₜ ι , M ⟨ g !⟩) = ⊥ᵒ
pre-𝓥 𝓥 ($ₜ ι , blame) = ⊥ᵒ
-- bogus cases for A ⇒ B
pre-𝓥 𝓥 (A ⇒ B , ` x) = ⊥ᵒ
pre-𝓥 𝓥 (A ⇒ B , $ c) = ⊥ᵒ
pre-𝓥 𝓥 (A ⇒ B , L · M) = ⊥ᵒ
pre-𝓥 𝓥 (A ⇒ B , M ⟨ h ?⟩) = ⊥ᵒ
pre-𝓥 𝓥 (A ⇒ B , M ⟨ g !⟩) = ⊥ᵒ
pre-𝓥 𝓥 (A ⇒ B , blame) = ⊥ᵒ

𝓥⟦_⟧ : (A : Type) → Term → Setᵒ
𝓥⟦ A ⟧ V = μᵖ pre-𝓥 (A , V)

𝓔⟦_⟧ : (A : Type) → Term → Setᵒ
𝓔⟦ A ⟧ V = ∀ᵒ(λ N → (M —↠ N)ᵒ →ᵒ (irred N)ᵒ →ᵒ (𝓥⟦ A ⟧ N) ⊎ᵒ (N ≡ blame)ᵒ)

-- pre-𝓥 : (A : Type) → Term → (Type → Term → Setᵒ) → (Type → Term → Setᵒ) → Setᵒ
-- pre-𝓥 ★ (op-inject {G} g ⦅ cons (ast V) nil ⦆) ▷𝓥 ▷𝓔 =  ▷𝓥 G V
-- pre-𝓥 ($ₜ ι) ((op-lit {ι′} c) ⦅ nil ⦆) ▷𝓥 ▷𝓔 =  (ι ≡ ι′)ᵒ 
-- pre-𝓥 (A ⇒ B) (ƛ N) ▷𝓥 ▷𝓔 =  ∀ᵒ(λ W → ▷𝓥 A W →ᵒ ▷𝓔 B (N [ W ]))
-- -- bogus cases for ★
-- pre-𝓥 ★ (` x) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ★ ($ c) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ★ (ƛ N) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ★ (L · M) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ★ (M ⟨ h ?⟩) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ★ blame ▷𝓥 ▷𝓔 = ⊥ᵒ
-- -- bogus cases for $ₜ ι
-- pre-𝓥 ($ₜ ι) (` x) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ($ₜ ι) (ƛ N) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ($ₜ ι) (L · M) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ($ₜ ι) (M ⟨ h ?⟩) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ($ₜ ι) (M ⟨ g !⟩) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 ($ₜ ι) blame ▷𝓥 ▷𝓔 = ⊥ᵒ
-- -- bogus cases for A ⇒ B
-- pre-𝓥 (A ⇒ B) (` x) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 (A ⇒ B) ($ c) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 (A ⇒ B) (L · M) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 (A ⇒ B) (M ⟨ h ?⟩) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 (A ⇒ B) (M ⟨ g !⟩) ▷𝓥 ▷𝓔 = ⊥ᵒ
-- pre-𝓥 (A ⇒ B) blame ▷𝓥 ▷𝓔 = ⊥ᵒ

-- pre-𝓔 : (A : Type) → Term → (Type → Term → Setᵒ) → (Type → Term → Setᵒ) → Setᵒ
-- pre-𝓔 A M ▷𝓥 ▷𝓔 = (((irred M)ᵒ) →ᵒ pre-𝓥 A M ▷𝓥 ▷𝓔)
--                 ×ᵒ (∀ᵒ(λ N → ((M —→ N)ᵒ) →ᵒ (▷𝓔 A N)))

-- 𝓥⟦_⟧ : (A : Type) → Term → Setᵒ
-- 𝓔⟦_⟧ : (A : Type) → Term → Setᵒ

-- 𝓥⟦ A ⟧ V zero =
--     pre-𝓥 A V (λ B M → ⊥ᵒ) (λ B M → ⊥ᵒ) zero
-- 𝓥⟦ A ⟧ V (suc k) =
--     pre-𝓥 A V (λ B M j → 𝓥⟦ B ⟧ M k) (λ B M j → 𝓔⟦ B ⟧ M k) (suc k)

-- 𝓔⟦ A ⟧ M zero =
--     pre-𝓔 A M (λ B M → ⊥ᵒ) (λ B M → ⊥ᵒ) zero
-- 𝓔⟦ A ⟧ M (suc k) =
--     pre-𝓔 A M (λ B M j → 𝓥⟦ B ⟧ M k) (λ B M j → 𝓔⟦ B ⟧ M k) (suc k)

-- ee-pre-𝓥 : ∀{A M} → ee (pre-𝓥 A M (λ B M → ⊥ᵒ) (λ B M → ⊥ᵒ))
-- ee-pre-𝓥 {★} {M ⟨ g !⟩} = tt
-- ee-pre-𝓥 {$ₜ ι} {$ c} = tt
-- ee-pre-𝓥 {A ⇒ B} {ƛ N} V zero z≤n ⊥k = tt

-- ee-pre-𝓥 {★} {` x} = tt
-- ee-pre-𝓥 {★} {$ c} = tt
-- ee-pre-𝓥 {★} {ƛ N} = tt
-- ee-pre-𝓥 {★} {L · M} = tt
-- ee-pre-𝓥 {★} {M ⟨ h ?⟩} = tt
-- ee-pre-𝓥 {★} {blame} = tt

-- ee-pre-𝓥 {$ₜ ι} {` x} = tt
-- ee-pre-𝓥 {$ₜ ι} {ƛ N} = tt
-- ee-pre-𝓥 {$ₜ ι} {L · M} = tt
-- ee-pre-𝓥 {$ₜ ι} {M ⟨ g !⟩} = tt
-- ee-pre-𝓥 {$ₜ ι} {M ⟨ h ?⟩} = tt
-- ee-pre-𝓥 {$ₜ ι} {blame} = tt

-- ee-pre-𝓥 {A ⇒ B} {` x} = tt
-- ee-pre-𝓥 {A ⇒ B} {$ c} = tt
-- ee-pre-𝓥 {A ⇒ B} {L · M} = tt
-- ee-pre-𝓥 {A ⇒ B} {M ⟨ g !⟩} = tt
-- ee-pre-𝓥 {A ⇒ B} {M ⟨ h ?⟩} = tt
-- ee-pre-𝓥 {A ⇒ B} {blame} = tt

-- ee-𝓥 : ∀{A M} → ee (𝓥⟦ A ⟧ M)
-- ee-𝓥 {A}{M} = ee-pre-𝓥{A}{M}

-- ee-𝓔 :  ∀{A M} → ee (𝓔⟦ A ⟧ M)
-- ee-𝓔 {A}{M} =
--    ee-×{P = (_ →ᵒ _)}{Q = ∀ᵒ(λ N → _ →ᵒ _)}
--       (ee-→ (ee-pre-𝓥{A}{M}))
--       (ee-∀ {F = (λ N → _ →ᵒ _)} λ{v 0 z≤n x₁ → tt})


-- pc : Setᵒ → Set
-- pc P  =  ∀ k → P (suc k) → P k

-- pc-𝓥 : ∀{A M} → pc (𝓥⟦ A ⟧ M)
-- pc-𝓔 : ∀{A M} → pc (𝓔⟦ A ⟧ M)

-- pc-𝓥 {A} {M} zero 𝓥sk = tt
-- pc-𝓥 {★} {M} (suc k) 𝓥sk = {!!}
-- pc-𝓥 {$ₜ ι} {M} (suc k) 𝓥sk = {!!}
-- pc-𝓥 {A ⇒ B} {ƛ N} (suc k) 𝓥sk W j j<k 𝓥Wk
--     with pc-𝓥{A ⇒ B}{ƛ N} k 𝓥sk
-- ... | 𝓥ƛNk
--     with k
-- ... | zero = tt
-- ... | suc k′ = 

--   let xx = 𝓥ƛNk W {!!} {!!} in
--   let IH2 = pc-𝓥{A}{W} k {!!} in
--   let xx = 𝓥sk W {!!} {!!} {!!} in
--   {!!}
-- pc-𝓔 {A}{M} = {!!}

-- dc′ : Setᵒ → Set
-- dc′ P  =  ∀ n → P n → ∀ k → k ≤′ n → P k

-- dc′-𝓥 : ∀{A M} → dc′ (𝓥⟦ A ⟧ M)
-- dc′-𝓔 : ∀{A M} → dc′ (𝓔⟦ A ⟧ M)

-- dc′-𝓥 {A} {M} k 𝓥Mk .k ≤′-refl = 𝓥Mk
-- dc′-𝓥 {★} {M} (suc k) 𝓥Mk i (≤′-step i≤k) = {!!}
-- dc′-𝓥 {$ₜ ι} {M} (suc k) 𝓥Mk i (≤′-step i≤k) = {!!}
-- dc′-𝓥 {A ⇒ B} {ƛ N} (suc k) 𝓥ƛNsk zero (≤′-step i≤k) = tt
-- dc′-𝓥 {A ⇒ B} {ƛ N} (suc k) 𝓥ƛNsk (suc i) (≤′-step i≤k) V j j<i 𝓥Vi =
--   let xx = 𝓥ƛNsk V i {!!} {!!} in
--   {!!}
-- -- Goal: 𝓔⟦ B ⟧ (N [ V ]) i


-- dc′-𝓔 {A} {M} k 𝓔Mk i i≤k = {!!}

-- dc-𝓥 : ∀{A M} → dc (𝓥⟦ A ⟧ M)
-- dc-𝓔 : ∀{A M} → dc (𝓥⟦ A ⟧ M)

-- -- dc-𝓥 {★} {M ⟨ g !⟩} = {!!}
-- -- dc-𝓥 {$ₜ ι} {$ c} = {!!}
-- -- dc-𝓥 {A ⇒ B} {ƛ N} 0 𝓥λNi 0 z≤n = ee-∀ {F = (λ W → ⊥ᵒ →ᵒ ⊥ᵒ)} λ {v 0 z≤n x₁ → tt}
-- -- dc-𝓥 {A ⇒ B} {ƛ N} (suc k) 𝓥λNsj (suc j) (s≤s j≤k) W i i<j 𝓥Wj =
-- --    let xx = 𝓥λNsj W {!!} {!!} {!!} in
-- --    {!!}
-- dc-𝓥 {A} {M} zero 𝓥Mk zero j≤k = 𝓥Mk
-- dc-𝓥 {A} {M} (suc k) 𝓥Mk .zero z≤n = ee-pre-𝓥 {A}{M}
-- dc-𝓥 {A} {M} (suc k) 𝓥Mk (suc j) (s≤s j≤k) = {!!}

-- dc-𝓔 {A}{M} = {!!}

-- LobFunᵒ : (Type → Term → (Type → Term → Setᵒ) → Setᵒ)
--   → (Type → Term → Setᵒ)
-- LobFunᵒ F A M zero = F A M (λ A M → ⊥ᵒ) zero 
-- LobFunᵒ F A M (suc k) = F A M (λ A N i → LobFunᵒ F A M k) (suc k)

-- 𝓥⟦_⟧ : (A : Type) → Term → Setᵒ
-- 𝓥⟦ A ⟧ V = LobFunᵒ pre-𝓥 A V


-- 𝓔⟦_⟧ : (A : Type) → Term → Setᵒ
-- 𝓔⟦ A ⟧ M = LobFunᵒ pre-𝓔 A M

-- V-base : ∀{n}{ι}{ι′}{c : rep ι′}
--    → 𝓥⟦ $ₜ ι ⟧ ($ c) (suc n) ≡ (ι ≡ ι′)
-- V-base {n} = refl

-- V-dyn : ∀{n}{G}{V}{g : Ground G}
--    → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) (suc n) ≡ 𝓥⟦ G ⟧ V n
--    --LobFunᵒ pre-𝓥 G (V ⟨ g !⟩) n
-- V-dyn {n}{G}{V}{g} = {!!}


-- -- pre-𝓥 : (A : Type) → Term → (Type → Term → Setₖ) → Setₖ
-- -- pre-𝓥 ★ (op-inject {G} g ⦅ cons (ast V) nil ⦆) rec = rec G V
-- -- pre-𝓥 ($ₜ ι) ((op-lit {ι′} c) ⦅ nil ⦆) rec = (ι ≡ ι′)ₖ
-- -- pre-𝓥 (A ⇒ B) (ƛ N) rec =
-- --    ∀ₖ(λ W → rec A W →ₖ
-- --    ∀ₖ(λ V → ((N [ W ] —↠ V)ₖ) →ₖ (((irred V) ₖ) →ₖ rec B V)))
-- -- pre-𝓥 A V rec = ⊥ₖ


-- -- LobFunₖ : (Type → Term → (Type → Term → Setₖ) → Setₖ)
-- --   → (Type → Term → Setᵒ)
-- -- LobFunₖ F A M zero = val (F A M λ B N → ⊥ₖ) zero
-- -- LobFunₖ F A M (suc k) =
-- --   let rec = LobFunₖ F A M k in
-- --   val (F A M λ B N → record { val = {!!} ; dcl = {!!} ; ez = {!!} }) (suc k)


-- -- 𝓥⟦_⟧ : (A : Type) → Term → Setₖ
-- -- 𝓥⟦ A ⟧ V = record { val = LobFunᵒ {!!} A V ; dcl = {!!} ; ez = {!!} }
-- --

-- -- 𝓔⟦_⟧ : (A : Type) → Term → Setₖ

-- -- 𝓥⟦_⟧ : (A : Type) → Term → Setₖ
-- -- 𝓥⟦ ★ ⟧ (` x) = ⊥ₖ
-- -- 𝓥⟦ ★ ⟧ ($ c) = ⊥ₖ
-- -- 𝓥⟦ ★ ⟧ (ƛ N) = ⊥ₖ
-- -- 𝓥⟦ ★ ⟧ (L · M) = ⊥ₖ
-- -- 𝓥⟦ ★ ⟧ (op-inject {G} g ⦅ cons (ast V) nil ⦆) = ▷ (𝓥⟦ G ⟧ V)
-- -- 𝓥⟦ ★ ⟧ (V ⟨ h ?⟩) = ⊥ₖ
-- -- 𝓥⟦ ★ ⟧ blame = ⊥ₖ

-- -- 𝓥⟦ $ₜ ι ⟧ (` x) = ⊥ₖ
-- -- 𝓥⟦ $ₜ ι ⟧ ((op-lit {ι′} c) ⦅ nil ⦆) = (ι ≡ ι′)ₖ
-- -- 𝓥⟦ $ₜ ι ⟧ (ƛ N) = ⊥ₖ
-- -- 𝓥⟦ $ₜ ι ⟧ (L · M) = ⊥ₖ
-- -- 𝓥⟦ $ₜ ι ⟧ (V ⟨ g !⟩) = ⊥ₖ
-- -- 𝓥⟦ $ₜ ι ⟧ (V ⟨ h ?⟩) = ⊥ₖ
-- -- 𝓥⟦ $ₜ ι ⟧ blame = ⊥ₖ

-- -- 𝓥⟦ A ⇒ B ⟧ (` x) = ⊥ₖ
-- -- 𝓥⟦ A ⇒ B ⟧ ($ c) = ⊥ₖ
-- -- 𝓥⟦ A ⇒ B ⟧ (ƛ N) = ∀ₖ {Term} (λ W → 𝓥⟦ A ⟧ W →ₖ 𝓔⟦ B ⟧ (N [ W ]))
-- -- 𝓥⟦ A ⇒ B ⟧ (L · M) = ⊥ₖ
-- -- 𝓥⟦ A ⇒ B ⟧ (V ⟨ g !⟩) = ⊥ₖ
-- -- 𝓥⟦ A ⇒ B ⟧ (V ⟨ h ?⟩) = ⊥ₖ
-- -- 𝓥⟦ A ⇒ B ⟧ blame = ⊥ₖ
