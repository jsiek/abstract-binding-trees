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

𝓔-unfold : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
  → 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
𝓔-unfold 𝓟⊢𝓔M = ≡ᵒ⇒⊢ᵒ 𝓟⊢𝓔M 𝓔-def

𝓔-progress : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
  → 𝓟 ⊢ᵒ progress A M
𝓔-progress 𝓟⊢𝓔M = ⊢ᵒ-proj₁ (𝓔-unfold 𝓟⊢𝓔M)

𝓔-preservation : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
  → 𝓟 ⊢ᵒ preservation A M
𝓔-preservation 𝓟⊢𝓔M = ⊢ᵒ-proj₂ (𝓔-unfold 𝓟⊢𝓔M)

𝓔-fold : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
𝓔-fold 𝓟⊢prog×pres = ≡ᵒ⇒⊢ᵒ 𝓟⊢prog×pres (≡ᵒ-sym (𝓔-def))

𝓔-intro : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ progress A M
  → 𝓟 ⊢ᵒ preservation A M
  → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
𝓔-intro 𝓟⊢prog 𝓟⊢pres = 𝓔-fold (⊢ᵒ-×-intro 𝓟⊢prog 𝓟⊢pres)

𝓔-blame : ∀{𝓟}{A} → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ blame
𝓔-blame {𝓟}{A} =
    𝓔-intro (⊢ᵒ-inj₂ (⊢ᵒ-inj₂ (⊢ᵒ-Sᵒ-intro isBlame)))
            (⊢ᵒ-∀-intro (λ N → ⊢ᵒ-→-intro
                          (Sᵒ⊢ᵒ λ blame→ → ⊥-elim (blame-irreducible blame→))))

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

V-dyn : ∀{G}{V}{g : Ground G}
   → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) ≡ᵒ ((Value V)ᵒ ×ᵒ ▷ᵒ (𝓥⟦ G ⟧ V))
V-dyn {G}{V}{g} =
   let X = (inj₁ (★ , V ⟨ g !⟩)) in
   𝓥⟦ ★ ⟧ (V ⟨ g !⟩)                                     ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
   apply (μᵖ 𝓔⊎𝓥) X                                     ≡ᵒ⟨ 𝓔⊎𝓥-fixpointᵒ X ⟩
   apply ((fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥)) X                        ≡ᵒ⟨ ≡ᵒ-refl refl ⟩ 
   (Value V)ᵒ ×ᵒ ▷ᵒ (𝓥⟦ G ⟧ V)
   QEDᵒ

V-dyn-elim : ∀{𝓟}{V}{R}
   → 𝓟 ⊢ᵒ 𝓥⟦ ★ ⟧ V
   → (∀ W G (g : Ground G) → V ≡ op-inject{G} g ⦅ cons (ast W) nil ⦆
             → 𝓟 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝓥⟦ G ⟧ W))
             → 𝓟 ⊢ᵒ R)
   → 𝓟 ⊢ᵒ R
V-dyn-elim {𝓟}{V}{R} ⊢𝓥V cont =
  ⊢ᵒ-sucP ⊢𝓥V λ { 𝓥Vsn → G 𝓥Vsn ⊢𝓥V cont }
  where
  G : ∀{V}{n}
      → # (𝓥⟦ ★ ⟧ V) (suc n)
      → 𝓟 ⊢ᵒ 𝓥⟦ ★ ⟧ V
      → (∀ W G g → V ≡ op-inject{G} g ⦅ cons (ast W) nil ⦆
                → 𝓟 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝓥⟦ G ⟧ W))
                → 𝓟 ⊢ᵒ R)
      → 𝓟 ⊢ᵒ R
  G {W ⟨ g !⟩}{n} 𝓥Vsn ⊢𝓥V cont
      with 𝓥⇒Value ★ (W ⟨ g !⟩) 𝓥Vsn
  ... | w 〈 g 〉 =
      let ⊢▷𝓥W = ⊢ᵒ-proj₂ (≡ᵒ⇒⊢ᵒ ⊢𝓥V (V-dyn{V = W}{g})) in
      cont W _ g refl (⊢ᵒ-×-intro (⊢ᵒ-Sᵒ-intro w) ⊢▷𝓥W)
  G {` x}{n} ()
  G {$ c}{n} ()
  G {ƛ N}{n} ()
  G {L · M}{n} ()
  G {M ⟨ h ?⟩}{n} ()
  G {blame}{n} ()
  
V-fun : ∀{A B}{N}
   → (𝓥⟦ A ⇒ B ⟧ (ƛ N)) ≡ᵒ
     (∀ᵒ[ W ] ((▷ᵒ (𝓥⟦ A ⟧ W)) →ᵒ (▷ᵒ (𝓔⟦ B ⟧ (N [ W ])))))
V-fun {A}{B}{N} =
   let X = (inj₁ (A ⇒ B , ƛ N)) in
   (𝓥⟦ A ⇒ B ⟧ (ƛ N))                                  ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
   (apply (μᵖ 𝓔⊎𝓥) X)                                 ≡ᵒ⟨ 𝓔⊎𝓥-fixpointᵒ X ⟩
   (apply ((fun 𝓔⊎𝓥) (μᵖ 𝓔⊎𝓥)) X)                        ≡ᵒ⟨ ≡ᵒ-refl refl ⟩ 
   (∀ᵒ[ W ] ((▷ᵒ (𝓥⟦ A ⟧ W)) →ᵒ (▷ᵒ (𝓔⟦ B ⟧ (N [ W ])))))
   QEDᵒ

V-fun-elim : ∀{𝓟}{A}{B}{V}{R}
   → 𝓟 ⊢ᵒ 𝓥⟦ A ⇒ B ⟧ V
   → (∀ N → V ≡ ƛ N
             → (∀{W} → 𝓟 ⊢ᵒ (▷ᵒ (𝓥⟦ A ⟧ W)) →ᵒ (▷ᵒ (𝓔⟦ B ⟧ (N [ W ]))))
             → 𝓟 ⊢ᵒ R)
   → 𝓟 ⊢ᵒ R
V-fun-elim {𝓟}{A}{B}{V}{R} ⊢𝓥V cont =
  ⊢ᵒ-sucP ⊢𝓥V λ { 𝓥Vsn → G {V} 𝓥Vsn ⊢𝓥V cont}
  where
  G : ∀{V}{n}
     → # (𝓥⟦ A ⇒ B ⟧ V) (suc n)
     → 𝓟 ⊢ᵒ 𝓥⟦ A ⇒ B ⟧ V
     → (∀ N → V ≡ ƛ N
             → (∀{W} → 𝓟 ⊢ᵒ (▷ᵒ (𝓥⟦ A ⟧ W)) →ᵒ (▷ᵒ (𝓔⟦ B ⟧ (N [ W ]))))
             → 𝓟 ⊢ᵒ R)
     → 𝓟 ⊢ᵒ R
  G{ƛ N}{n} 𝓥V ⊢𝓥V cont = cont N refl λ {W} →
      ⊢ᵒ-∀-elim{P = λ W → (▷ᵒ (𝓥⟦ A ⟧ W)) →ᵒ (▷ᵒ (𝓔⟦ B ⟧ (N [ W ])))}
                 (≡ᵒ⇒⊢ᵒ ⊢𝓥V V-fun) W
  G{` x}{n} ()
  G{$ c}{n} ()
  G{L · M}{n} ()
  G{M ⟨ g !⟩}{n} ()
  G{M ⟨ h ?⟩}{n} ()
  G{blame}{n} ()

{- Semantic Type Safety -}

𝓖⟦_⟧ : (Γ : List Type) → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ = []
𝓖⟦ A ∷ Γ ⟧ σ = (𝓥⟦ A ⟧ (σ 0)) ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x))

_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⟧ (⟪ γ ⟫ M)

lookup-𝓖 : (Γ : List Type) → (γ : Subst)
  → ∀ {A}{y} → (Γ ∋ y ⦂ A)
  → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ A ⟧ (γ y)
lookup-𝓖 (B ∷ Γ) γ {A} {zero} refl = ⊢ᵒ-hyp
lookup-𝓖 (B ∷ Γ) γ {A} {suc y} ∋y =
    ⊢ᵒ-weaken (lookup-𝓖 Γ (λ x → γ (suc x)) ∋y) 

{- Lemmas -}

𝓥⇒𝓔 : ∀{A}{𝓟}{V}
   → 𝓟 ⊢ᵒ 𝓥⟦ A ⟧ V
   → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ V
𝓥⇒𝓔 {A}{𝓟}{V} 𝓟⊢𝓥V =
    ⊢ᵒ-intro
    λ n ⊨𝓟n →
    let 𝓥V = (⊢ᵒ-elim 𝓟⊢𝓥V) n ⊨𝓟n in
    (inj₁ 𝓥V) , λ { N zero x V→N → tt ;
                     N (suc j) (s≤s j≤) V→N →
                         ⊥-elim (value-irreducible (𝓥⇒Value A V 𝓥V) V→N)}

exp-▷ : ∀{𝓟}{A}{M N : Term}
   → 𝓟 ⊢ᵒ (M —→ N)ᵒ
   → 𝓟 ⊢ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)
     -------------------
   → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ M
exp-▷{𝓟}{A}{M}{N} 𝓟⊢M→N ⊢▷𝓔N =
  ≡ᵒ⇒⊢ᵒ{𝓟}{progress A M ×ᵒ preservation A M}{𝓔⟦ A ⟧ M}
      Goal (≡ᵒ-sym (𝓔-def{A}{M}))
  where
  redM : 𝓟 ⊢ᵒ reducible M ᵒ
  redM = Sᵒ→Tᵒ⇒⊢ᵒ 𝓟⊢M→N λ M→N → _ , M→N

  ⊢prog : 𝓟 ⊢ᵒ progress A M
  ⊢prog = ⊢ᵒ-inj₂{𝓟}{𝓥⟦ A ⟧ M}{(reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ}
            (⊢ᵒ-inj₁{𝓟}{(reducible M)ᵒ}{(Blame M)ᵒ} redM)
          
  ⊢pres : 𝓟 ⊢ᵒ preservation A M
  ⊢pres = ⊢ᵒ-∀-intro {P = λ N → ((M —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ A ⟧ N))}
      λ N′ → ⊢ᵒ-intro
        λ { zero ⊨𝓟n .zero z≤n M→N′ → tt ;
            (suc n) ⊨𝓟n .zero z≤n M→N′ → tt ;
            (suc n) ⊨𝓟n (suc j) (s≤s j≤n) M→N′ →
              let ⊨𝓟sj = (downClosed-⊨ᵒ 𝓟 (suc n) ⊨𝓟n (suc j) (s≤s j≤n)) in
              subst (λ X → # (𝓔⟦ A ⟧ X) j)
                  (deterministic (((⊢ᵒ-elim 𝓟⊢M→N) (suc j) ⊨𝓟sj)) M→N′)
                  ((⊢ᵒ-elim ⊢▷𝓔N) (suc j) ⊨𝓟sj)}
          
  Goal : 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
  Goal = ⊢ᵒ-×-intro ⊢prog ⊢pres

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

{- 𝓔-frame (Monadic Bind Lemma) -}

𝓔-f-cont : Type → Type → Frame → Term → Setᵒ
𝓔-f-cont A B F M = ∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝓥⟦ B ⟧ V →ᵒ 𝓔⟦ A ⟧ (F ⟦ V ⟧)

𝓔-fp : Type → Type → Frame → Term → Setᵒ
𝓔-fp A B F M = 𝓔⟦ B ⟧ M
                →ᵒ 𝓔-f-cont A B F M
                →ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)

𝓔-frame-prop : Type → Type → Frame → Setᵒ
𝓔-frame-prop A B F = ∀ᵒ[ M ] 𝓔-fp A B F M

frame-prop-lemma : ∀{𝓟}{A}{B}{M}{F}
   → 𝓟 ⊢ᵒ ▷ᵒ 𝓔-frame-prop A B F
   → 𝓟 ⊢ᵒ ▷ᵒ 𝓔⟦ B ⟧ M
   → 𝓟 ⊢ᵒ ▷ᵒ 𝓔-f-cont A B F M
   → 𝓟 ⊢ᵒ ▷ᵒ (𝓔⟦ A ⟧ (F ⟦ M ⟧))
frame-prop-lemma{𝓟}{A}{B}{M}{F} IH 𝓔M V→FV =
  let IH1 = (⊢ᵒ-▷∀{P = λ M → 𝓔-fp A B F M} IH) in
  let IH2 = ⊢ᵒ-∀-elim IH1 M in
  let IH3 = (⊢ᵒ-→-elim (⊢ᵒ-▷→{𝓟}{𝓔⟦ B ⟧ M} IH2) 𝓔M) in
  let IH4 = ⊢ᵒ-▷→{𝓟}{𝓔-f-cont A B F M} IH3 in
       ⊢ᵒ-→-elim IH4 V→FV


Pₒ→Qₒ : ∀{P Q : Set}{n}
   → (P → Q)
   → (P ₒ) n
     --------
   → (Q ₒ) n
Pₒ→Qₒ {P} {Q} {zero} P→Q Pn = tt
Pₒ→Qₒ {P} {Q} {suc n} P→Q Pn = P→Q Pn

𝓔-f-cont-lemma : ∀{𝓟}{A}{B}{F}{M}{M′}
   → M —→ M′
   → 𝓟 ⊢ᵒ 𝓔-f-cont A B F M
   → 𝓟 ⊢ᵒ 𝓔-f-cont A B F M′
𝓔-f-cont-lemma {𝓟}{A}{B}{F}{M}{M′} M→M′ 𝓔-cont =
   ⊢ᵒ-∀-intro λ V →
      let M→V→𝓔FV : 𝓟 ⊢ᵒ (M —↠ V)ᵒ →ᵒ 𝓥⟦ B ⟧ V →ᵒ 𝓔⟦ A ⟧ (F ⟦ V ⟧)
          M→V→𝓔FV = ⊢ᵒ-∀-elim 𝓔-cont V in
   
      let M′→V→𝓔FV : 𝓥⟦ B ⟧ V ∷ (M′ —↠ V)ᵒ ∷ 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ V ⟧)
          M′→V→𝓔FV = ⊢ᵒ-intro λ n (𝓥Vn , M′→Vn , ⊨𝓟n) →
                ⊢ᵒ-elim M→V→𝓔FV n ⊨𝓟n n ≤-refl
                    (Pₒ→Qₒ (λ M′→V → M —→⟨ M→M′ ⟩ M′→V) M′→Vn)
                    n ≤-refl 𝓥Vn in
       ⊢ᵒ-→-intro (⊢ᵒ-→-intro M′→V→𝓔FV)

𝓔-frame-aux : ∀{𝓟}{A}{B}{F} → 𝓟 ⊢ᵒ 𝓔-frame-prop A B F
𝓔-frame-aux {𝓟}{A}{B}{F} = ⊢ᵒ-lob Goal
 where     
 Goal : ▷ᵒ 𝓔-frame-prop A B F ∷ 𝓟 ⊢ᵒ 𝓔-frame-prop A B F
 Goal = ⊢ᵒ-∀-intro λ M → ⊢ᵒ-→-intro (⊢ᵒ-→-intro Goal′)
  where
  Goal′ : ∀{M}
     → (𝓔-f-cont A B F M) ∷ 𝓔⟦ B ⟧ M ∷ ▷ᵒ 𝓔-frame-prop A B F ∷ 𝓟
        ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
  Goal′{M} =
     let ⊢𝓔M : 𝓟′ ⊢ᵒ 𝓔⟦ B ⟧ M
         ⊢𝓔M = ⊢ᵒ-weaken ⊢ᵒ-hyp in
     ⊢ᵒ-case3 (𝓔-progress ⊢𝓔M) Mval Mred Mblame
     where
     𝓟′ = (𝓔-f-cont A B F M) ∷ 𝓔⟦ B ⟧ M ∷ ▷ᵒ 𝓔-frame-prop A B F ∷ 𝓟

     Mval : 𝓥⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
     Mval =
       let ⊢𝓥M : 𝓥⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ 𝓥⟦ B ⟧ M
           ⊢𝓥M = ⊢ᵒ-hyp in
       let 𝓥V→𝓔FV : 𝓥⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ 𝓔-f-cont A B F M
           𝓥V→𝓔FV = ⊢ᵒ-weaken ⊢ᵒ-hyp in
       let Cont = λ V → (M —↠ V)ᵒ →ᵒ 𝓥⟦ B ⟧ V →ᵒ 𝓔⟦ A ⟧ (F ⟦ V ⟧) in
       let M→M→𝓥M→𝓔FM : 𝓥⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ ((M —↠ M)ᵒ →ᵒ 𝓥⟦ B ⟧ M
                                        →ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧))
           M→M→𝓥M→𝓔FM = ⊢ᵒ-∀-elim{P = Cont} 𝓥V→𝓔FV M in
       let 𝓥M→𝓔FM = ⊢ᵒ-→-elim M→M→𝓥M→𝓔FM (⊢ᵒ-Sᵒ-intro (M END)) in
       ⊢ᵒ-→-elim 𝓥M→𝓔FM ⊢𝓥M

     progMred : (reducible M)ᵒ ∷ 𝓟′ ⊢ᵒ progress A (F ⟦ M ⟧)
     progMred =
        let redFM : (reducible M)ᵒ ∷ 𝓟′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
            redFM = Sᵒ→Tᵒ⇒⊢ᵒ ⊢ᵒ-hyp λ {(M′ , M→M′) → _ , (ξ F M→M′)} in
        ⊢ᵒ-inj₂ (⊢ᵒ-inj₁ redFM)

     redM⇒▷𝓔N : ∀{N} → reducible M → (F ⟦ M ⟧ —→ N)
        → 𝓟′ ⊢ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)
     redM⇒▷𝓔N {N} rM FM→N =
          let finv = frame-inv2{M}{N}{F} rM FM→N in
          let M′ = proj₁ finv in
          let M→M′ = proj₁ (proj₂ finv) in
          let N≡ = proj₂ (proj₂ finv) in

          let IH : 𝓟′ ⊢ᵒ ▷ᵒ 𝓔-frame-prop A B F
              IH = ⊢ᵒ-weaken (⊢ᵒ-weaken ⊢ᵒ-hyp) in
          let 𝓔M : 𝓟′ ⊢ᵒ 𝓔⟦ B ⟧ M
              𝓔M = ⊢ᵒ-weaken ⊢ᵒ-hyp in
          let ▷𝓔M′ : 𝓟′ ⊢ᵒ ▷ᵒ 𝓔⟦ B ⟧ M′
              ▷𝓔M′ = ⊢ᵒ-→-elim
                         (⊢ᵒ-∀-elim{P = λ N → (M —→ N)ᵒ →ᵒ ▷ᵒ (𝓔⟦ B ⟧ N)}
                            (𝓔-preservation 𝓔M) M′)
                                (⊢ᵒ-Sᵒ-intro M→M′) in
          let M→V→𝓥V→𝓔FV : 𝓟′ ⊢ᵒ 𝓔-f-cont A B F M
              M→V→𝓥V→𝓔FV = ⊢ᵒ-hyp in
          let M′→V→𝓥V→𝓔FV : 𝓟′ ⊢ᵒ 𝓔-f-cont A B F M′
              M′→V→𝓥V→𝓔FV = 𝓔-f-cont-lemma{𝓟′}{A}{B} M→M′ M→V→𝓥V→𝓔FV in
          let ▷𝓔FM′ : 𝓟′ ⊢ᵒ ▷ᵒ (𝓔⟦ A ⟧ (F ⟦ M′ ⟧))
              ▷𝓔FM′ = frame-prop-lemma IH ▷𝓔M′ (⊢ᵒ-mono M′→V→𝓥V→𝓔FV) in
          subst (λ N → 𝓟′ ⊢ᵒ ▷ᵒ 𝓔⟦ A ⟧ N) (sym N≡) ▷𝓔FM′

     Mred : (reducible M)ᵒ ∷ 𝓟′ ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
     Mred = 𝓔-intro progMred
           (Sᵒ⊢ᵒ λ redM → ⊢ᵒ-∀-intro λ N →
            ⊢ᵒ-→-intro (Sᵒ⊢ᵒ λ FM→N → (redM⇒▷𝓔N redM FM→N)))

     progMblame : (Blame M)ᵒ ∷ 𝓟′ ⊢ᵒ progress A (F ⟦ M ⟧)
     progMblame =
        let redFM : (Blame M)ᵒ ∷ 𝓟′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
            redFM = Sᵒ→Tᵒ⇒⊢ᵒ ⊢ᵒ-hyp λ {isBlame → _ , (ξ-blame F)} in
        ⊢ᵒ-inj₂ (⊢ᵒ-inj₁ redFM)

     blameM⇒▷𝓔N : ∀{N} → Blame M → (F ⟦ M ⟧ —→ N)
        → 𝓟′ ⊢ᵒ ▷ᵒ (𝓔⟦ A ⟧ N)
     blameM⇒▷𝓔N {N} isBlame FM→N =
         let eq = blame-frame FM→N in
         subst (λ N → 𝓟′ ⊢ᵒ ▷ᵒ 𝓔⟦ A ⟧ N) (sym eq) (⊢ᵒ-mono 𝓔-blame)

     Mblame : (Blame M)ᵒ ∷ 𝓟′ ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
     Mblame = 𝓔-intro progMblame
              (Sᵒ⊢ᵒ λ blameM → ⊢ᵒ-∀-intro λ N →
               ⊢ᵒ-→-intro (Sᵒ⊢ᵒ λ FM→N → blameM⇒▷𝓔N blameM FM→N))

𝓔-frame : ∀{𝓟}{A}{B}{F}{M}
   → 𝓟 ⊢ᵒ 𝓔⟦ B ⟧ M
   → 𝓟 ⊢ᵒ (∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝓥⟦ B ⟧ V →ᵒ 𝓔⟦ A ⟧ (F ⟦ V ⟧))
   → 𝓟 ⊢ᵒ 𝓔⟦ A ⟧ (F ⟦ M ⟧)
𝓔-frame {𝓟}{A}{B}{F}{M} ⊢𝓔M ⊢𝓥V→𝓔FV =
  ⊢ᵒ-→-elim (⊢ᵒ-→-elim (⊢ᵒ-∀-elim{𝓟}{P = λ M → 𝓔-fp A B F M}
                          𝓔-frame-aux M)
                        ⊢𝓔M)
             ⊢𝓥V→𝓔FV
