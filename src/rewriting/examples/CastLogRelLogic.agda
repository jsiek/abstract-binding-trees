{-# OPTIONS --rewriting #-}
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
open import rewriting.examples.CastDeterministic
open import rewriting.examples.StepIndexedLogic

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Type × Term) ⊎ (Type × Term)

𝒱ᶠ⟦_⟧ : Type → Term → Fun ℰ⊎𝒱-type ⊤ Continuous
𝒱ᶠ⟦ A ⟧ V = recur (inj₁ (A , V))

ℰᶠ⟦_⟧ : Type → Term → Fun ℰ⊎𝒱-type ⊤ Continuous
ℰᶠ⟦ A ⟧ M = recur (inj₂ (A , M))

pre-𝒱 : Type → Term → Fun ℰ⊎𝒱-type ⊤ Wellfounded
pre-𝒱 ★ (op-inject{G} g ⦅ cons (ast V) nil ⦆) = -- (V ⟨ g !⟩ )
    (Value V)ᶠ ×ᶠ ▷ᶠ (𝒱ᶠ⟦ G ⟧ V)
pre-𝒱 ($ₜ ι) (op-lit {ι′} c ⦅ nil ⦆) =   -- ($ c)
    (ι ≡ ι′)ᶠ
pre-𝒱 (A ⇒ B) (ƛ N) =
    ∀ᶠ[ W ] ▷ᶠ (𝒱ᶠ⟦ A ⟧ W) →ᶠ ▷ᶠ (ℰᶠ⟦ B ⟧ (N [ W ]))

-- bogus cases for ★
pre-𝒱 ★ (` x) = (⊥) ᶠ
pre-𝒱 ★ ($ c) = (⊥) ᶠ
pre-𝒱 ★ (ƛ N) = (⊥) ᶠ
pre-𝒱 ★ (L · M) = (⊥) ᶠ
pre-𝒱 ★ (M ⟨ h ?⟩) = (⊥) ᶠ
pre-𝒱 ★ blame = (⊥) ᶠ

-- bogus cases for ι
pre-𝒱 ($ₜ ι) (` x) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) (ƛ N) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) (L · M) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) (M ⟨ g !⟩) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) (M ⟨ h ?⟩) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) blame = (⊥) ᶠ

-- bogus cases for A ⇒ B
pre-𝒱 (A ⇒ B) (` x) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) ($ c) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) (L · M) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) (M ⟨ g !⟩) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) (M ⟨ h ?⟩) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) blame = (⊥) ᶠ

-- Type Safety = Progress & Preservation
pre-ℰ : Type → Term
       → Fun ℰ⊎𝒱-type ⊤ Wellfounded
pre-ℰ A M = (pre-𝒱 A M ⊎ᶠ (reducible M)ᶠ ⊎ᶠ (Blame M)ᶠ)    -- Progress
             ×ᶠ (∀ᶠ[ N ] (M —→ N)ᶠ →ᶠ ▷ᶠ (ℰᶠ⟦ A ⟧ N))        -- Preservation

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Fun ℰ⊎𝒱-type ⊤ Wellfounded
pre-ℰ⊎𝒱 (inj₁ (A , V)) = pre-𝒱 A V
pre-ℰ⊎𝒱 (inj₂ (A , M)) = pre-ℰ A M

ℰ⊎𝒱 : Fun ℰ⊎𝒱-type ℰ⊎𝒱-type Wellfounded
ℰ⊎𝒱 = flipᶠ pre-ℰ⊎𝒱 tt

-- Semantically Well Typed Value
𝒱⟦_⟧ : (A : Type) → Term → Setᵒ
𝒱⟦ A ⟧ V = apply (μᵖ ℰ⊎𝒱) (inj₁ (A , V))

-- Semantically Well Typed Term
ℰ⟦_⟧ : (A : Type) → Term → Setᵒ
ℰ⟦ A ⟧ M = apply (μᵖ ℰ⊎𝒱) (inj₂ (A , M))

ℰ⊎𝒱-fixpointᵖ : μᵖ ℰ⊎𝒱 ≡ᵖ (fun ℰ⊎𝒱) (μᵖ ℰ⊎𝒱)
ℰ⊎𝒱-fixpointᵖ = fixpoint ℰ⊎𝒱

ℰ⊎𝒱-fixpointᵒ : ∀ X → apply (μᵖ ℰ⊎𝒱) X ≡ᵒ apply ((fun ℰ⊎𝒱) (μᵖ ℰ⊎𝒱)) X
ℰ⊎𝒱-fixpointᵒ X = apply-≡ᵖ ℰ⊎𝒱-fixpointᵖ X 

progress : Type → Term → Setᵒ
progress A M = (𝒱⟦ A ⟧ M) ⊎ᵒ (reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ

preservation : Type → Term → Setᵒ
preservation A M = (∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)))

ℰ-prop : Type → Term → Setᵒ
ℰ-prop A M = (progress A M) ×ᵒ (preservation A M)

ℰ-def : ∀{A}{M}
  → ℰ⟦ A ⟧ M ≡ᵒ progress A M ×ᵒ preservation A M
ℰ-def {A}{M} =
  ℰ⟦ A ⟧ M                                                ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
  apply (μᵖ ℰ⊎𝒱) (inj₂ (A , M))          ≡ᵒ⟨ ℰ⊎𝒱-fixpointᵒ (inj₂ (A , M)) ⟩
  apply ((fun ℰ⊎𝒱) (μᵖ ℰ⊎𝒱)) (inj₂ (A , M))
                  ≡ᵒ⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (ℰ⊎𝒱-fixpointᵒ (inj₁ (A , M))))
                                       (≡ᵒ-refl refl)) (≡ᵒ-refl refl) ⟩
  progress A M ×ᵒ preservation A M
  QEDᵒ

ℰ-unfold : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
  → 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
ℰ-unfold 𝓟⊢ℰM = ≡ᵒ⇒⊢ᵒ 𝓟⊢ℰM ℰ-def

ℰ-progress : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
  → 𝓟 ⊢ᵒ progress A M
ℰ-progress 𝓟⊢ℰM = ⊢ᵒ-proj₁ (ℰ-unfold 𝓟⊢ℰM)

ℰ-preservation : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
  → 𝓟 ⊢ᵒ preservation A M
ℰ-preservation 𝓟⊢ℰM = ⊢ᵒ-proj₂ (ℰ-unfold 𝓟⊢ℰM)

ℰ-fold : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
ℰ-fold 𝓟⊢prog×pres = ≡ᵒ⇒⊢ᵒ 𝓟⊢prog×pres (≡ᵒ-sym (ℰ-def))

ℰ-intro : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ progress A M
  → 𝓟 ⊢ᵒ preservation A M
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
ℰ-intro 𝓟⊢prog 𝓟⊢pres = ℰ-fold (⊢ᵒ-×-intro 𝓟⊢prog 𝓟⊢pres)

ℰ-blame : ∀{𝓟}{A} → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ blame
ℰ-blame {𝓟}{A} =
    ℰ-intro (⊢ᵒ-inj₂ (⊢ᵒ-inj₂ (⊢ᵒ-Sᵒ-intro isBlame)))
            (⊢ᵒ-∀-intro (λ N → ⊢ᵒ-→-intro
                          (Sᵒ⊢ᵒ λ blame→ → ⊥-elim (blame-irreducible blame→))))

𝒱⇒Value : ∀ {k} A M → # (𝒱⟦ A ⟧ M) (suc k) → Value M
𝒱⇒Value ★ (M ⟨ g !⟩) (v , _) = v 〈 g 〉
𝒱⇒Value ($ₜ ι) ($ c) 𝒱M = $̬ c
𝒱⇒Value (A ⇒ B) (ƛ N) 𝒱M = ƛ̬ N
-- vacuous cases
𝒱⇒Value ★ (` x) ()
𝒱⇒Value ★ ($ c) ()
𝒱⇒Value ★ (ƛ N) ()
𝒱⇒Value ★ (L · M) ()
𝒱⇒Value ★ (M ⟨ h ?⟩) ()
𝒱⇒Value ★ blame ()
𝒱⇒Value ($ₜ ι) (` x) ()
𝒱⇒Value ($ₜ ι) (ƛ N) ()
𝒱⇒Value ($ₜ ι) (L · M) ()
𝒱⇒Value ($ₜ ι) (M ⟨ g !⟩) ()
𝒱⇒Value ($ₜ ι) (M ⟨ h ?⟩) ()
𝒱⇒Value ($ₜ ι) blame ()
𝒱⇒Value (A ⇒ B) (` x) ()
𝒱⇒Value (A ⇒ B) ($ c) ()
𝒱⇒Value (A ⇒ B) (L · M) ()
𝒱⇒Value (A ⇒ B) (M ⟨ g !⟩) ()
𝒱⇒Value (A ⇒ B) (M ⟨ h ?⟩) ()
𝒱⇒Value (A ⇒ B) blame ()

V-base : ∀{ι}{ι′}{c : rep ι′}
   → (𝒱⟦ $ₜ ι ⟧ ($ c)) ≡ᵒ (ι ≡ ι′)ᵒ
V-base = ≡ᵒ-intro (λ k z → z) (λ k z → z)

V-base-intro : ∀{n}{ι}{c : rep ι}
   → # (𝒱⟦ $ₜ ι ⟧ ($ c)) n
V-base-intro {zero} = tt
V-base-intro {suc n}{ι}{c} = refl

V-base-elim : ∀{n}{ι}{ι′}{c : rep ι′}
   → # (𝒱⟦ $ₜ ι ⟧ ($ c)) (suc n)
   → (ι ≡ ι′)
V-base-elim {n} refl = refl

V-dyn : ∀{G}{V}{g : Ground G}
   → 𝒱⟦ ★ ⟧ (V ⟨ g !⟩) ≡ᵒ ((Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ G ⟧ V))
V-dyn {G}{V}{g} =
   let X = (inj₁ (★ , V ⟨ g !⟩)) in
   𝒱⟦ ★ ⟧ (V ⟨ g !⟩)                                     ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
   apply (μᵖ ℰ⊎𝒱) X                                     ≡ᵒ⟨ ℰ⊎𝒱-fixpointᵒ X ⟩
   apply ((fun ℰ⊎𝒱) (μᵖ ℰ⊎𝒱)) X                        ≡ᵒ⟨ ≡ᵒ-refl refl ⟩ 
   (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ G ⟧ V)
   QEDᵒ

V-dyn-elim : ∀{𝓟}{V}{R}
   → 𝓟 ⊢ᵒ 𝒱⟦ ★ ⟧ V
   → (∀ W G (g : Ground G) → V ≡ op-inject{G} g ⦅ cons (ast W) nil ⦆
             → 𝓟 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ G ⟧ W))
             → 𝓟 ⊢ᵒ R)
   → 𝓟 ⊢ᵒ R
V-dyn-elim {𝓟}{V}{R} ⊢𝒱V cont =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → G 𝒱Vsn ⊢𝒱V cont }
  where
  G : ∀{V}{n}
      → # (𝒱⟦ ★ ⟧ V) (suc n)
      → 𝓟 ⊢ᵒ 𝒱⟦ ★ ⟧ V
      → (∀ W G g → V ≡ op-inject{G} g ⦅ cons (ast W) nil ⦆
                → 𝓟 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ G ⟧ W))
                → 𝓟 ⊢ᵒ R)
      → 𝓟 ⊢ᵒ R
  G {W ⟨ g !⟩}{n} 𝒱Vsn ⊢𝒱V cont
      with 𝒱⇒Value ★ (W ⟨ g !⟩) 𝒱Vsn
  ... | w 〈 g 〉 =
      let ⊢▷𝒱W = ⊢ᵒ-proj₂ (≡ᵒ⇒⊢ᵒ ⊢𝒱V (V-dyn{V = W}{g})) in
      cont W _ g refl (⊢ᵒ-×-intro (⊢ᵒ-Sᵒ-intro w) ⊢▷𝒱W)
  G {` x}{n} ()
  G {$ c}{n} ()
  G {ƛ N}{n} ()
  G {L · M}{n} ()
  G {M ⟨ h ?⟩}{n} ()
  G {blame}{n} ()
  
V-fun : ∀{A B}{N}
   → (𝒱⟦ A ⇒ B ⟧ (ƛ N)) ≡ᵒ
     (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
V-fun {A}{B}{N} =
   let X = (inj₁ (A ⇒ B , ƛ N)) in
   (𝒱⟦ A ⇒ B ⟧ (ƛ N))                                  ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
   (apply (μᵖ ℰ⊎𝒱) X)                                 ≡ᵒ⟨ ℰ⊎𝒱-fixpointᵒ X ⟩
   (apply ((fun ℰ⊎𝒱) (μᵖ ℰ⊎𝒱)) X)                        ≡ᵒ⟨ ≡ᵒ-refl refl ⟩ 
   (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
   QEDᵒ

V-fun-elim : ∀{𝓟}{A}{B}{V}{R}
   → 𝓟 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
   → (∀ N → V ≡ ƛ N
             → (∀{W} → 𝓟 ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ]))))
             → 𝓟 ⊢ᵒ R)
   → 𝓟 ⊢ᵒ R
V-fun-elim {𝓟}{A}{B}{V}{R} ⊢𝒱V cont =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → G {V} 𝒱Vsn ⊢𝒱V cont}
  where
  G : ∀{V}{n}
     → # (𝒱⟦ A ⇒ B ⟧ V) (suc n)
     → 𝓟 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
     → (∀ N → V ≡ ƛ N
             → (∀{W} → 𝓟 ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ]))))
             → 𝓟 ⊢ᵒ R)
     → 𝓟 ⊢ᵒ R
  G{ƛ N}{n} 𝒱V ⊢𝒱V cont = cont N refl λ {W} →
      ⊢ᵒ-∀-elim{P = λ W → (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))}
                 (≡ᵒ⇒⊢ᵒ ⊢𝒱V V-fun) W
  G{` x}{n} ()
  G{$ c}{n} ()
  G{L · M}{n} ()
  G{M ⟨ g !⟩}{n} ()
  G{M ⟨ h ?⟩}{n} ()
  G{blame}{n} ()

{- Semantic Type Safety -}

𝓖⟦_⟧ : (Γ : List Type) → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ = []
𝓖⟦ A ∷ Γ ⟧ σ = (𝒱⟦ A ⟧ (σ 0)) ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x))

_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)

lookup-𝓖 : (Γ : List Type) → (γ : Subst)
  → ∀ {A}{y} → (Γ ∋ y ⦂ A)
  → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (γ y)
lookup-𝓖 (B ∷ Γ) γ {A} {zero} refl = ⊢ᵒ-hyp
lookup-𝓖 (B ∷ Γ) γ {A} {suc y} ∋y =
    ⊢ᵒ-weaken (lookup-𝓖 Γ (λ x → γ (suc x)) ∋y) 

{- Lemmas -}

𝒱⇒ℰ : ∀{A}{𝓟}{V}
   → 𝓟 ⊢ᵒ 𝒱⟦ A ⟧ V
   → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ V
𝒱⇒ℰ {A}{𝓟}{V} 𝓟⊢𝒱V =
    ⊢ᵒ-intro
    λ n ⊨𝓟n →
    let 𝒱V = (⊢ᵒ-elim 𝓟⊢𝒱V) n ⊨𝓟n in
    (inj₁ 𝒱V) , λ { N zero x V→N → tt ;
                     N (suc j) (s≤s j≤) V→N →
                         ⊥-elim (value-irreducible (𝒱⇒Value A V 𝒱V) V→N)}

exp-▷ : ∀{𝓟}{A}{M N : Term}
   → 𝓟 ⊢ᵒ (M —→ N)ᵒ
   → 𝓟 ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
     -------------------
   → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
exp-▷{𝓟}{A}{M}{N} 𝓟⊢M→N ⊢▷ℰN =
  ≡ᵒ⇒⊢ᵒ{𝓟}{progress A M ×ᵒ preservation A M}{ℰ⟦ A ⟧ M}
      Goal (≡ᵒ-sym (ℰ-def{A}{M}))
  where
  redM : 𝓟 ⊢ᵒ reducible M ᵒ
  redM = Sᵒ→Tᵒ⇒⊢ᵒ 𝓟⊢M→N λ M→N → _ , M→N

  ⊢prog : 𝓟 ⊢ᵒ progress A M
  ⊢prog = ⊢ᵒ-inj₂{𝓟}{𝒱⟦ A ⟧ M}{(reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ}
            (⊢ᵒ-inj₁{𝓟}{(reducible M)ᵒ}{(Blame M)ᵒ} redM)
          
  ⊢pres : 𝓟 ⊢ᵒ preservation A M
  ⊢pres = ⊢ᵒ-∀-intro {P = λ N → ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N))}
      λ N′ → ⊢ᵒ-intro
        λ { zero ⊨𝓟n .zero z≤n M→N′ → tt ;
            (suc n) ⊨𝓟n .zero z≤n M→N′ → tt ;
            (suc n) ⊨𝓟n (suc j) (s≤s j≤n) M→N′ →
              let ⊨𝓟sj = (downClosed-⊨ᵒ 𝓟 (suc n) ⊨𝓟n (suc j) (s≤s j≤n)) in
              subst (λ X → # (ℰ⟦ A ⟧ X) j)
                  (deterministic (((⊢ᵒ-elim 𝓟⊢M→N) (suc j) ⊨𝓟sj)) M→N′)
                  ((⊢ᵒ-elim ⊢▷ℰN) (suc j) ⊨𝓟sj)}
          
  Goal : 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
  Goal = ⊢ᵒ-×-intro ⊢prog ⊢pres

{- ℰ-frame (Monadic Bind Lemma) -}

ℰ-f-cont : Type → Type → Frame → Term → Setᵒ
ℰ-f-cont A B F M = ∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)

ℰ-fp : Type → Type → Frame → Term → Setᵒ
ℰ-fp A B F M = ℰ⟦ B ⟧ M
                →ᵒ ℰ-f-cont A B F M
                →ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)

ℰ-frame-prop : Type → Type → Frame → Setᵒ
ℰ-frame-prop A B F = ∀ᵒ[ M ] ℰ-fp A B F M

frame-prop-lemma : ∀{𝓟}{A}{B}{M}{F}
   → 𝓟 ⊢ᵒ ▷ᵒ ℰ-frame-prop A B F
   → 𝓟 ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M
   → 𝓟 ⊢ᵒ ▷ᵒ ℰ-f-cont A B F M
   → 𝓟 ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M ⟧))
frame-prop-lemma{𝓟}{A}{B}{M}{F} IH ℰM V→FV =
  let IH1 = (⊢ᵒ-▷∀{P = λ M → ℰ-fp A B F M} IH) in
  let IH2 = ⊢ᵒ-∀-elim IH1 M in
  let IH3 = (⊢ᵒ-→-elim (⊢ᵒ-▷→{𝓟}{ℰ⟦ B ⟧ M} IH2) ℰM) in
  let IH4 = ⊢ᵒ-▷→{𝓟}{ℰ-f-cont A B F M} IH3 in
       ⊢ᵒ-→-elim IH4 V→FV


Pₒ→Qₒ : ∀{P Q : Set}{n}
   → (P → Q)
   → (P ₒ) n
     --------
   → (Q ₒ) n
Pₒ→Qₒ {P} {Q} {zero} P→Q Pn = tt
Pₒ→Qₒ {P} {Q} {suc n} P→Q Pn = P→Q Pn

ℰ-f-cont-lemma : ∀{𝓟}{A}{B}{F}{M}{M′}
   → M —→ M′
   → 𝓟 ⊢ᵒ ℰ-f-cont A B F M
   → 𝓟 ⊢ᵒ ℰ-f-cont A B F M′
ℰ-f-cont-lemma {𝓟}{A}{B}{F}{M}{M′} M→M′ ℰ-cont =
   ⊢ᵒ-∀-intro λ V →
      let M→V→ℰFV : 𝓟 ⊢ᵒ (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
          M→V→ℰFV = ⊢ᵒ-∀-elim ℰ-cont V in
   
      let M′→V→ℰFV : 𝒱⟦ B ⟧ V ∷ (M′ —↠ V)ᵒ ∷ 𝓟 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
          M′→V→ℰFV = ⊢ᵒ-intro λ n (𝒱Vn , M′→Vn , ⊨𝓟n) →
                ⊢ᵒ-elim M→V→ℰFV n ⊨𝓟n n ≤-refl
                    (Pₒ→Qₒ (λ M′→V → M —→⟨ M→M′ ⟩ M′→V) M′→Vn)
                    n ≤-refl 𝒱Vn in
       ⊢ᵒ-→-intro (⊢ᵒ-→-intro M′→V→ℰFV)

ℰ-frame-aux : ∀{𝓟}{A}{B}{F} → 𝓟 ⊢ᵒ ℰ-frame-prop A B F
ℰ-frame-aux {𝓟}{A}{B}{F} = ⊢ᵒ-lob Goal
 where     
 Goal : ▷ᵒ ℰ-frame-prop A B F ∷ 𝓟 ⊢ᵒ ℰ-frame-prop A B F
 Goal = ⊢ᵒ-∀-intro λ M → ⊢ᵒ-→-intro (⊢ᵒ-→-intro Goal′)
  where
  Goal′ : ∀{M}
     → (ℰ-f-cont A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-frame-prop A B F ∷ 𝓟
        ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
  Goal′{M} =
   let ⊢ℰM : 𝓟′ ⊢ᵒ ℰ⟦ B ⟧ M
       ⊢ℰM = ⊢ᵒ-weaken ⊢ᵒ-hyp in
   ⊢ᵒ-case3 (ℰ-progress ⊢ℰM) Mval Mred Mblame
   where
   𝓟′ = (ℰ-f-cont A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-frame-prop A B F ∷ 𝓟

   Mval : 𝒱⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mval =
     let ⊢𝒱M : 𝒱⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ 𝒱⟦ B ⟧ M
         ⊢𝒱M = ⊢ᵒ-hyp in
     let ℰcontFM : 𝒱⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ ℰ-f-cont A B F M
         ℰcontFM = ⊢ᵒ-weaken ⊢ᵒ-hyp in
     let Cont = λ V → (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧) in
     ⊢ᵒ-→-elim (⊢ᵒ-→-elim (⊢ᵒ-∀-elim{P = Cont} ℰcontFM M)
                          (⊢ᵒ-Sᵒ-intro (M END)))
               ⊢𝒱M

   Mred : (reducible M)ᵒ ∷ 𝓟′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mred = ℰ-intro progressMred
         (Sᵒ⊢ᵒ λ redM → ⊢ᵒ-∀-intro λ N →
          ⊢ᵒ-→-intro (Sᵒ⊢ᵒ λ FM→N → (redM⇒▷ℰN redM FM→N)))
    where
    progressMred : (reducible M)ᵒ ∷ 𝓟′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMred =
       let redFM : (reducible M)ᵒ ∷ 𝓟′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
           redFM = Sᵒ→Tᵒ⇒⊢ᵒ ⊢ᵒ-hyp λ {(M′ , M→M′) → _ , (ξ F M→M′)} in
       ⊢ᵒ-inj₂ (⊢ᵒ-inj₁ redFM)

    redM⇒▷ℰN : ∀{N} → reducible M → (F ⟦ M ⟧ —→ N)
       → 𝓟′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
    redM⇒▷ℰN {N} rM FM→N =
         let finv = frame-inv2{M}{N}{F} rM FM→N in
         let M′ = proj₁ finv in
         let M→M′ = proj₁ (proj₂ finv) in
         let N≡ = proj₂ (proj₂ finv) in

         let IH : 𝓟′ ⊢ᵒ ▷ᵒ ℰ-frame-prop A B F
             IH = ⊢ᵒ-weaken (⊢ᵒ-weaken ⊢ᵒ-hyp) in
         let ℰM : 𝓟′ ⊢ᵒ ℰ⟦ B ⟧ M
             ℰM = ⊢ᵒ-weaken ⊢ᵒ-hyp in
         let ▷ℰM′ : 𝓟′ ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M′
             ▷ℰM′ = ⊢ᵒ-→-elim
                        (⊢ᵒ-∀-elim{P = λ N → (M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)}
                           (ℰ-preservation ℰM) M′)
                               (⊢ᵒ-Sᵒ-intro M→M′) in
         let M→V→𝒱V→ℰFV : 𝓟′ ⊢ᵒ ℰ-f-cont A B F M
             M→V→𝒱V→ℰFV = ⊢ᵒ-hyp in
         let M′→V→𝒱V→ℰFV : 𝓟′ ⊢ᵒ ℰ-f-cont A B F M′
             M′→V→𝒱V→ℰFV = ℰ-f-cont-lemma{𝓟′}{A}{B} M→M′ M→V→𝒱V→ℰFV in
         let ▷ℰFM′ : 𝓟′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M′ ⟧))
             ▷ℰFM′ = frame-prop-lemma IH ▷ℰM′ (⊢ᵒ-mono M′→V→𝒱V→ℰFV) in
         subst (λ N → 𝓟′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym N≡) ▷ℰFM′

   Mblame : (Blame M)ᵒ ∷ 𝓟′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mblame = ℰ-intro progressMblame
            (Sᵒ⊢ᵒ λ blameM → ⊢ᵒ-∀-intro λ N →
             ⊢ᵒ-→-intro (Sᵒ⊢ᵒ λ FM→N → blameM⇒▷ℰN blameM FM→N))
    where
    progressMblame : (Blame M)ᵒ ∷ 𝓟′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMblame =
       let redFM : (Blame M)ᵒ ∷ 𝓟′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
           redFM = Sᵒ→Tᵒ⇒⊢ᵒ ⊢ᵒ-hyp λ {isBlame → _ , (ξ-blame F)} in
       ⊢ᵒ-inj₂ (⊢ᵒ-inj₁ redFM)

    blameM⇒▷ℰN : ∀{N} → Blame M → (F ⟦ M ⟧ —→ N)
       → 𝓟′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
    blameM⇒▷ℰN {N} isBlame FM→N =
        let eq = blame-frame FM→N in
        subst (λ N → 𝓟′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym eq) (⊢ᵒ-mono ℰ-blame)


ℰ-frame : ∀{𝓟}{A}{B}{F}{M}
   → 𝓟 ⊢ᵒ ℰ⟦ B ⟧ M
   → 𝓟 ⊢ᵒ (∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧))
   → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
ℰ-frame {𝓟}{A}{B}{F}{M} ⊢ℰM ⊢𝒱V→ℰFV =
  ⊢ᵒ-→-elim (⊢ᵒ-→-elim (⊢ᵒ-∀-elim{𝓟}{P = λ M → ℰ-fp A B F M}
                          ℰ-frame-aux M)
                        ⊢ℰM)
             ⊢𝒱V→ℰFV
