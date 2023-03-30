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
pre-𝓔 A M = (pre-𝓥 A M ⊎ᶠ (reducible M)ᶠ ⊎ᶠ (Blame M)ᶠ)    -- Progress
             ×ᶠ (∀ᶠ[ N ] (M —→ N)ᶠ →ᶠ ▷ᶠ (𝓔ᶠ⟦ A ⟧ N))        -- Preservation

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

𝓔⊎𝓥-fixpointᵖ : μᵖ 𝓔⊎𝓥 ≡ᵖ (fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥)
𝓔⊎𝓥-fixpointᵖ = fixpoint 𝓔⊎𝓥

𝓔⊎𝓥-fixpointᵒ : ∀ X → apply (μᵖ 𝓔⊎𝓥) X ≡ᵒ apply ((fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥)) X
𝓔⊎𝓥-fixpointᵒ X = apply-≡ᵖ 𝓔⊎𝓥-fixpointᵖ X 

progress : Type → Term → Setᵒ
progress A M = (𝓥⟦ A ⟧ M) ⊎ᵒ (reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ

preservation : Type → Term → Setᵒ
preservation A M = (∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)))

𝓔-prop : Type → Term → Setᵒ
𝓔-prop A M = (progress A M) ×ᵒ (preservation A M)

𝓔-def : ∀{A}{M}
  → 𝓔⟦ A ⟧ M ≡ᵒ progress A M ×ᵒ preservation A M
𝓔-def {A}{M} =
  𝓔⟦ A ⟧ M                                                ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
  apply (μᵖ 𝓔⊎𝓥) (inj₂ (A , M))          ≡ᵒ⟨ 𝓔⊎𝓥-fixpointᵒ (inj₂ (A , M)) ⟩
  apply ((fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥)) (inj₂ (A , M))
                  ≡ᵒ⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (𝓔⊎𝓥-fixpointᵒ (inj₁ (A , M))))
                                       (≡ᵒ-refl refl)) (≡ᵒ-refl refl) ⟩
  progress A M ×ᵒ preservation A M
  QEDᵒ

𝓔-unfold : ∀ 𝓟 {A}{M}
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
  → 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
𝓔-unfold 𝓟 {A}{M} 𝓟⊢𝓔M =
   ≡ᵒ⇒⊢ᵒ{𝓟}{𝓔⟦ A ⟧ M}{progress A M ×ᵒ preservation A M} 𝓟⊢𝓔M (𝓔-def{A}{M})

𝓔-progress : ∀ 𝓟 {A}{M}
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
  → 𝓟 ⊢ᵒ progress A M
𝓔-progress 𝓟 {A}{M} 𝓟⊢𝓔M =
  ⊢ᵒ-proj₁{𝓟}{progress A M}{preservation A M} (𝓔-unfold 𝓟 𝓟⊢𝓔M)

𝓔-preservation : ∀ 𝓟 {A}{M}
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
  → 𝓟 ⊢ᵒ preservation A M
𝓔-preservation 𝓟 {A}{M} 𝓟⊢𝓔M =
  ⊢ᵒ-proj₂{𝓟}{progress A M}{preservation A M} (𝓔-unfold 𝓟 𝓟⊢𝓔M)

𝓔-fold : ∀ 𝓟 {A}{M}
  → 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
𝓔-fold 𝓟 {A}{M} 𝓟⊢prog×pres =
   ≡ᵒ⇒⊢ᵒ{𝓟}{progress A M ×ᵒ preservation A M}{𝓔⟦ A ⟧ M}
     𝓟⊢prog×pres (≡ᵒ-sym (𝓔-def{A}{M}))

𝓔-intro : ∀ 𝓟 {A}{M}
  → 𝓟 ⊢ᵒ progress A M
  → 𝓟 ⊢ᵒ preservation A M
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
𝓔-intro 𝓟 {A}{M} 𝓟⊢prog 𝓟⊢pres =
  𝓔-fold 𝓟{A}{M} (⊢ᵒ-×-intro {𝓟}{progress A M}{preservation A M}
                     𝓟⊢prog 𝓟⊢pres)

𝓥⇒Value : ∀ {k} A M → # (𝓥⟦ A ⟧ M) (suc k) → Value M
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

V-base : ∀{ι}{ι′}{c : rep ι′}
   → (𝓥⟦ $ₜ ι ⟧ ($ c)) ≡ᵒ (ι ≡ ι′)ᵒ
V-base = ≡ᵒ-intro (λ k z → z) (λ k z → z)

V-base-intro : ∀{n}{ι}{c : rep ι}
   → # (𝓥⟦ $ₜ ι ⟧ ($ c)) n
V-base-intro {zero} = tt
V-base-intro {suc n}{ι}{c} = refl

V-base-elim : ∀{n}{ι}{ι′}{c : rep ι′}
   → # (𝓥⟦ $ₜ ι ⟧ ($ c)) (suc n)
   → (ι ≡ ι′)
V-base-elim {n} refl = refl

-- V-dyn : ∀{G}{V}{g : Ground G}
--    → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) ≡ᵒ ((Value V)ᵒ ×ᵒ ▷ᵒ (𝓥⟦ G ⟧ V))
-- V-dyn {G}{V}{g} =
--    let X = (inj₁ (★ , V ⟨ g !⟩)) in
--    𝓥⟦ ★ ⟧ (V ⟨ g !⟩)                                     ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
--    apply (μᵖ 𝓔⊎𝓥) X                                     ≡ᵒ⟨ 𝓔⊎𝓥-fixpointᵒ X ⟩
--    apply ((fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥)) X                        ≡ᵒ⟨ ≡ᵒ-refl refl ⟩ 
--    (Value V)ᵒ ×ᵒ ▷ᵒ (𝓥⟦ G ⟧ V)
--    QEDᵒ

-- V-fun : ∀{A B}{N}
--    → (𝓥⟦ A ⇒ B ⟧ (ƛ N)) ≡ᵒ
--      (∀ᵒ[ W ] ((▷ᵒ (𝓥⟦ A ⟧ W)) →ᵒ (▷ᵒ (𝓔⟦ B ⟧ (N [ W ])))))
-- V-fun {A}{B}{N} =
--    let X = (inj₁ (A ⇒ B , ƛ N)) in
--    (𝓥⟦ A ⇒ B ⟧ (ƛ N))                                  ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
--    (apply (μᵖ 𝓔⊎𝓥) X)                                 ≡ᵒ⟨ 𝓔⊎𝓥-fixpointᵒ X ⟩
--    (apply ((fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥)) X)                        ≡ᵒ⟨ ≡ᵒ-refl refl ⟩ 
--    (∀ᵒ[ W ] ((▷ᵒ (𝓥⟦ A ⟧ W)) →ᵒ (▷ᵒ (𝓔⟦ B ⟧ (N [ W ])))))
--    QEDᵒ

-- {- Semantic Type Safety -}

-- 𝓖⟦_⟧ : (Γ : List Type) → Subst → List Setᵒ
-- 𝓖⟦ [] ⟧ σ = []
-- 𝓖⟦ A ∷ Γ ⟧ σ = (𝓥⟦ A ⟧ (σ 0)) ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x))

-- _⊨_⦂_ : List Type → Term → Type → Set
-- Γ ⊨ M ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⟧ (⟪ γ ⟫ M)

-- lookup-𝓖 : (Γ : List Type) → (γ : Subst)
--   → ∀ {A}{y} → (Γ ∋ y ⦂ A)
--   → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ A ⟧ (γ y)
-- lookup-𝓖 (B ∷ Γ) γ {A} {zero} refl =
--     ⊢ᵒ-hyp{𝓖⟦ Γ ⟧ (λ x → γ (suc x))}{𝓥⟦ B ⟧ (γ 0)}
-- lookup-𝓖 (B ∷ Γ) γ {A} {suc y} ∋y =
--     let IH = lookup-𝓖 Γ (λ x → γ (suc x)) ∋y in
--     ⊢ᵒ-weaken{𝓖⟦ Γ ⟧ (λ x → γ (suc x))}{𝓥⟦ A ⟧ (γ (suc y))}{𝓥⟦ B ⟧ (γ 0)}
--         IH

-- {- Lemmas -}

-- 𝓥⇒𝓔 : ∀{A}{𝓟}{V}
--    → 𝓟 ⊢ᵒ 𝓥⟦ A ⟧ V
--    → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ V
-- 𝓥⇒𝓔 {A}{𝓟}{V} 𝓟⊢𝓥V n ⊨𝓟n =
--     let 𝓥V = 𝓟⊢𝓥V n ⊨𝓟n in
--     (inj₁ 𝓥V) , λ { N zero x V→N → tt ;
--                      N (suc j) (s≤s j≤) V→N →
--                          ⊥-elim (value-irreducible (𝓥⇒Value A V 𝓥V) V→N)}

-- exp-▷ : ∀{𝓟}{A}{M N : Term}
--    → 𝓟 ⊢ᵒ (M —→ N)ᵒ
--    → 𝓟 ⊢ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)
--      -------------------
--    → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
-- exp-▷{𝓟}{A}{M}{N} 𝓟⊢M→N ⊢▷𝓔N =
--   ≡ᵒ⇒⊢ᵒ{𝓟}{progress A M ×ᵒ preservation A M}{𝓔⟦ A ⟧ M}
--       Goal (≡ᵒ-sym (𝓔-def{A}{M}))
--   where
--   redM : 𝓟 ⊢ᵒ reducible M ᵒ
--   redM = Sᵒ→Tᵒ⇒⊢ᵒ 𝓟 𝓟⊢M→N λ M→N → _ , M→N

--   ⊢prog : 𝓟 ⊢ᵒ progress A M
--   ⊢prog = ⊢ᵒ-inj₂{𝓟}{𝓥⟦ A ⟧ M}{(reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ}
--             (⊢ᵒ-inj₁{𝓟}{(reducible M)ᵒ}{(Blame M)ᵒ} redM)
          
--   ⊢pres : 𝓟 ⊢ᵒ preservation A M
--   ⊢pres = ⊢ᵒ-∀-intro{𝓟}{Term}{λ N → ((M —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N))}
--       λ { N′ zero ⊨𝓟n .zero z≤n M→N′ → tt ;
--           N′ (suc n) ⊨𝓟n .zero z≤n M→N′ → tt ;
--           N′ (suc n) ⊨𝓟n (suc j) (s≤s j≤n) M→N′ →
--             let ⊨𝓟sj = (downClosed-⊨ᵒ 𝓟 (suc n) ⊨𝓟n (suc j) (s≤s j≤n)) in
--             subst (λ X → (▷ᵒ (𝓔⟦ A ⟧ X)) (suc j))
--               (deterministic (𝓟⊢M→N (suc j) ⊨𝓟sj) M→N′) (⊢▷𝓔N (suc j) ⊨𝓟sj)}
          
--   Goal : 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
--   Goal = ⊢ᵒ-×-intro{𝓟}{progress A M}{preservation A M} ⊢prog ⊢pres

-- {-
-- determ : ∀{M}{N}{N′}
--    → [] ⊢ᵒ (M —→ N)ᵒ
--    → [] ⊢ᵒ (M —→ N′)ᵒ
--    → N ≡ N′
-- determ {M}{N}{N′} ⊢M→N ⊢M→N′ =
--   let M→N = ⊢M→N (suc 0) tt in
--   let M→N′ = ⊢M→N′ (suc 0) tt in
--   deterministic M→N M→N′

-- 𝓔—→ : ∀{𝓟}{M}{N}{A}
--    → 𝓟 ⊢ᵒ (M —→ N)ᵒ
--    → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ N
--    → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
-- 𝓔—→ {𝓟}{M}{N}{A} ⊢M→N ⊢N =
--    let rM : 𝓟 ⊢ᵒ (reducible M)ᵒ
--        rM = λ { zero x → tt
--               ; (suc n) x → _ , (⊢M→N (suc n) x) } in
--    let progM : 𝓟 ⊢ᵒ progress A M
--        progM = (⊢ᵒ-inj₂{𝓟}{𝓥⟦ A ⟧ M}{(reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ}
--                   (⊢ᵒ-inj₁{𝓟}{(reducible M)ᵒ}{(Blame M)ᵒ} rM)) in

--     let ⊢▷𝓔N : ∀ N → (M —→ N) ᵒ ∷ 𝓟 ⊢ᵒ ▷ᵒ 𝓔⟦ A ⟧ N
--         ⊢▷𝓔N N =
             
--             {!!} in
                  
--     let presM : 𝓟 ⊢ᵒ preservation A M
--         presM = ⊢ᵒ-∀-intro{𝓟}{Term}{λ N → (M —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)}
--                    λ N → ⊢ᵒ-→-intro{𝓟}{(M —→ N)ᵒ}{▷ᵒ (𝓔⟦ A ⟧ N)} (⊢▷𝓔N N) in
--    𝓔-intro 𝓟 progM presM

-- 𝓔-frame : ∀{𝓟}{F : Frame}{M N : Term}{A}{B}
--    → 𝓟 ⊢ᵒ 𝓔⟦ B ⟧ M
--    → 𝓥⟦ B ⟧ M ∷ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
--      ----------------------------------
--    → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
-- 𝓔-frame {𝓟} {F} {M} {N} {A} {B} 𝓟⊢𝓔M 𝓥M∷𝓟⊢𝓔FM =
--   ⊢ᵒ-lob 𝓟 (𝓔⟦ A ⟧ (F ⟦ M ⟧)) Goal1
--   where
--   ▷𝓔FM = ▷ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)

--   Goal2a1 : reducible M ᵒ ∷ ▷𝓔FM ∷ 𝓟 ⊢ᵒ progress A (F ⟦ M ⟧)
--   Goal2a1 zero x = inj₂ (inj₂ tt)
--   Goal2a1 (suc n) ((M′ , M→M′) , snd) = inj₂ (inj₁ (_ , (ξξ F refl refl M→M′)))

--   Goal2a4 : ∀ N → ◁ᵒ (((F ⟦ M ⟧) —→ N) ᵒ) ∷ ◁ᵒ ▷𝓔FM ∷ ◁̃ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ N
--   Goal2a4 N =
--       let ◁𝓟′ = ◁ᵒ (((F ⟦ M ⟧) —→ N) ᵒ) ∷ ◁ᵒ ▷𝓔FM ∷ ◁̃ 𝓟 in
--       let ⊢◁▷𝓔FM : ◁𝓟′ ⊢ᵒ ◁ᵒ ▷𝓔FM
--           ⊢◁▷𝓔FM = ⊢ᵒ-weaken{◁ᵒ ▷𝓔FM ∷ ◁̃ 𝓟}{◁ᵒ ▷𝓔FM}{◁ᵒ (((F ⟦ M ⟧) —→ N) ᵒ)}
--                        (⊢ᵒ-hyp{◁̃ 𝓟}{◁ᵒ ▷𝓔FM}) in
--       let ⊢𝓔FM : ◁𝓟′ ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
--           ⊢𝓔FM = ≡ᵒ⇒⊢ᵒ{◁𝓟′}{◁ᵒ ▷𝓔FM}{𝓔⟦ A ⟧ (F ⟦ M ⟧)}
--                       ⊢◁▷𝓔FM (◁▷ᵒ{𝓔⟦ A ⟧ (F ⟦ M ⟧)}) in
--       let presFM : ◁𝓟′ ⊢ᵒ (∀ᵒ[ N ] (((F ⟦ M ⟧) —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)))
--           presFM = 𝓔-preservation ◁𝓟′ ⊢𝓔FM in
--       let presFM′ : ◁𝓟′ ⊢ᵒ (((F ⟦ M ⟧) —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N))
--           presFM′ = ⊢ᵒ-∀-elim{◁𝓟′}{Term}
--                        {λ N → (((F ⟦ M ⟧) —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N))} presFM N in
--       let ⊢◁FM→N : ◁𝓟′ ⊢ᵒ ◁ᵒ (((F ⟦ M ⟧) —→ N) ᵒ)
--           ⊢◁FM→N = ⊢ᵒ-hyp {◁ᵒ ▷𝓔FM ∷ ◁̃ 𝓟}{◁ᵒ (((F ⟦ M ⟧) —→ N) ᵒ)} in
--       let ⊢FM→N : ◁𝓟′ ⊢ᵒ ((F ⟦ M ⟧) —→ N) ᵒ
--           ⊢FM→N = ◁Pᵒ{◁𝓟′}{(F ⟦ M ⟧) —→ N} ⊢◁FM→N in
--       let ⊢▷𝓔N : ◁𝓟′ ⊢ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)
--           ⊢▷𝓔N = ⊢ᵒ-→-elim {◁𝓟′}{((F ⟦ M ⟧) —→ N) ᵒ}{▷ᵒ (𝓔⟦ A ⟧ N)}
--                             presFM′ ⊢FM→N in
--       {!!}


--   Goal2a3 : ∀ N → ((F ⟦ M ⟧) —→ N) ᵒ ∷ ▷𝓔FM ∷ 𝓟 ⊢ᵒ ▷ᵒ 𝓔⟦ A ⟧ N
--   Goal2a3 N = weak-▷ {((F ⟦ M ⟧) —→ N) ᵒ ∷ ▷𝓔FM ∷ 𝓟}{𝓔⟦ A ⟧ N} (Goal2a4 N)

--   Goal2a2 : reducible M ᵒ ∷ ▷𝓔FM ∷ 𝓟 ⊢ᵒ preservation A (F ⟦ M ⟧)
--   Goal2a2 = ⊢ᵒ-weaken {▷𝓔FM ∷ 𝓟}{preservation A (F ⟦ M ⟧)}{reducible M ᵒ}
--             (⊢ᵒ-∀-intro {▷𝓔FM ∷ 𝓟}{Term}
--                        {λ N → (F ⟦ M ⟧ —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)}
--                (λ N → ⊢ᵒ-→-intro{▷𝓔FM ∷ 𝓟}{(F ⟦ M ⟧ —→ N) ᵒ}
--                      {▷ᵒ 𝓔⟦ A ⟧ N} (Goal2a3 N)))
  
--   Goal2a : reducible M ᵒ ∷ ▷𝓔FM ∷ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
--   Goal2a = 𝓔-intro (reducible M ᵒ ∷ ▷𝓔FM ∷ 𝓟){A}{F ⟦ M ⟧} Goal2a1 Goal2a2

--   Goal2b : Blame M ᵒ ∷ ▷𝓔FM ∷ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
--   Goal2b = {!!}
  
--   Goal2 : reducible M ᵒ ⊎ᵒ Blame M ᵒ ∷ ▷𝓔FM ∷ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
--   Goal2 = ⊢ᵒ-case-L{▷𝓔FM ∷ 𝓟}{reducible M ᵒ}{Blame M ᵒ}{𝓔⟦ A ⟧ (F ⟦ M ⟧)}
--              Goal2a Goal2b

--   Goal1 : ▷𝓔FM ∷ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
--   Goal1 =
--     let ▷𝓔FM∷𝓟⊢progM = ⊢ᵒ-weaken{𝓟}{progress B M}{▷𝓔FM}
--                               (𝓔-progress 𝓟 𝓟⊢𝓔M) in
--     let 𝓥M∷▷𝓔FM∷𝓟⊢𝓔FM =
--           ⊢ᵒ-swap {𝓟}{𝓔⟦ A ⟧ (F ⟦ M ⟧)}{▷𝓔FM}{𝓥⟦ B ⟧ M}
--                (⊢ᵒ-weaken{𝓥⟦ B ⟧ M ∷ 𝓟}{𝓔⟦ A ⟧ (F ⟦ M ⟧)}{▷𝓔FM}
--                                   𝓥M∷𝓟⊢𝓔FM) in
--     ⊢ᵒ-case{▷𝓔FM ∷ 𝓟}{𝓥⟦ B ⟧ M}{(reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ}
--            {𝓔⟦ A ⟧ (F ⟦ M ⟧)}
--         ▷𝓔FM∷𝓟⊢progM  𝓥M∷▷𝓔FM∷𝓟⊢𝓔FM  Goal2
-- -}



-- {-
-- 𝓔-frame {𝓟} {□· M} {L} {L′} {A} {B} 𝓟⊢𝓔L 𝓥M∷𝓟⊢𝓔FM =
--   {!!}
--   -- ⊢ᵒ-case{𝓟}{𝓥⟦ B ⟧ L}{(reducible L)ᵒ ⊎ᵒ (Blame L)ᵒ}{𝓔⟦ A ⟧ (L · M)}
--   --    (𝓔-progress 𝓟 𝓟⊢𝓔L) 𝓥M∷𝓟⊢𝓔FM Goal2
--   where

--   Goal2a1 : reducible L ᵒ ∷ 𝓟 ⊢ᵒ progress A (L · M)
--   Goal2a1 zero x = inj₂ (inj₂ tt)
--   Goal2a1 (suc n) ((L′ , L→L′) , ⊨𝓟sn) =
--       inj₂ (inj₁ (_ , (ξξ (□· M) refl refl L→L′)))

--   Goal2a21 : ∀ N → (L · M —→ N) ᵒ ∷ reducible L ᵒ ∷ 𝓟 ⊢ᵒ ▷ᵒ 𝓔⟦ A ⟧ N
--   Goal2a21 N = {!!}


--   Goal2a2 : reducible L ᵒ ∷ 𝓟 ⊢ᵒ preservation A (L · M)
--   Goal2a2 = ⊢ᵒ-∀-intro {reducible L ᵒ ∷ 𝓟}{Term}
--                 {λ N → (L · M —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)}
--                 (λ N → ⊢ᵒ-→-intro{reducible L ᵒ ∷ 𝓟}{(L · M —→ N) ᵒ}{▷ᵒ 𝓔⟦ A ⟧ N} (Goal2a21 N)) 

--   Goal2a : reducible L ᵒ ∷ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (L · M)
--   Goal2a = 𝓔-intro (reducible L ᵒ ∷ 𝓟) {A}{L · M} Goal2a1 Goal2a2

--   Goal2b : Blame L ᵒ ∷ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (L · M)
--   Goal2b = {!!}

--   Goal2 : reducible L ᵒ ⊎ᵒ Blame L ᵒ ∷ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (L · M)
--   Goal2 = ⊢ᵒ-case-L{𝓟}{reducible L ᵒ}{Blame L ᵒ}{𝓔⟦ A ⟧ (L · M)} Goal2a Goal2b

-- {-
--     with (≡ᵒ⇒⊢ᵒ{𝓟}{𝓔⟦ B ⟧ L}{𝓔-prop B L} 𝓟⊢𝓔L (𝓔-def{B}{L})) (suc n′) ⊨𝓟n
-- ... | inj₁ 𝓥Ln , Lpres =
--      {!!}
-- ... | inj₂ (inj₁ (L′ , L→L′)) , Lpres =
--      {!!}
-- ... | inj₂ (inj₂ isBlame) , Lpres =
--        let blame·M—→blame = ξξ-blame {L · M} (□· M) refl in
--        {!!}
--        where
--        Goal : 𝓟 ⊢ᵒ progress A ((□· M) ⟦ L ⟧) ×ᵒ preservation A ((□· M) ⟦ L ⟧)
--        Goal = {!!}
--        --(inj₂ (inj₁ (_ , blame·M—→blame))) , {!!}
-- -}  

-- 𝓔-frame {𝓟} {v ·□} {M} {N} {A} {B} 𝓔M M→N⊢▷𝓔FN n ⊨𝓟n = {!!}
-- 𝓔-frame {𝓟} {□⟨ g !⟩} {M} {N} {A} {B} 𝓔M M→N⊢▷𝓔FN n ⊨𝓟n = {!!}
-- 𝓔-frame {𝓟} {□⟨ h ?⟩} {M} {N} {A} {B} 𝓔M M→N⊢▷𝓔FN n ⊨𝓟n = {!!}
-- -}
