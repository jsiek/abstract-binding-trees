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

data Dir : Set where
  ↪ : Dir
  ↩ : Dir

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Prec × Dir × Term × Term) ⊎ (Prec × Dir × Term × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

ℰˢ⟦_⟧ : Prec → Dir → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A⊑B ⟧ d M M′ = (inj₂ (A⊑B , d , M , M′)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Prec → Dir → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A⊑B ⟧ d V V′ = (inj₁ (A⊑B , d , V , V′)) ∈ zeroˢ

pre-ℰ : Prec → Dir → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 : Prec → Dir → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)

pre-𝒱 (.★ , ★ , unk⊑) d (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = let g = gnd⇒ty G in
                 (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (▷ˢ (𝒱ˢ⟦ (g , g , Refl⊑) ⟧ d V V′))
... | no neq = ⊥ ˢ
pre-𝒱 (.★ , $ₜ ι′ , unk⊑) d (V ⟨ $ᵍ ι !⟩) ($ c)
    with ($ᵍ ι) ≡ᵍ ($ᵍ ι′)
... | yes refl = (Value V)ˢ ×ˢ ▷ˢ (𝒱ˢ⟦ ($ₜ ι , $ₜ ι , Refl⊑) ⟧ d V ($ c))
... | no new = ⊥ ˢ
pre-𝒱 (.★ , A′ ⇒ B′ , unk⊑) d (V ⟨ ★⇒★ !⟩) V′ =
    (Value V)ˢ ×ˢ (Value V′)ˢ
    ×ˢ ▷ˢ (𝒱ˢ⟦ (★ ⇒ ★ , A′ ⇒ B′ , fun⊑ unk⊑ unk⊑) ⟧ d V V′)
pre-𝒱 ($ₜ ι , $ₜ ι , base⊑) d ($ c) ($ c′) = (c ≡ c′) ˢ
pre-𝒱 ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) d (ƛ N) (ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] (pre-𝒱 (A , A′ , A⊑A′) d W W′)
                  →ˢ (pre-ℰ (B , B′ , B⊑B′) d (N [ W ]) (N′ [ W′ ]))
pre-𝒱 (A , A′ , A⊑A′) d V V′ = ⊥ ˢ

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

pre-ℰ c ↪ M M′ =
      (∀ˢ[ V ]  (M ⇓ᵗ V)ˢ →ˢ ((∃ˢ[ V′ ] (M′ ⇓ᵗ V′)ˢ ×ˢ pre-𝒱 c ↪ V V′)
                            ⊎ˢ (M′ ⇓ᵇ)ˢ))
   ×ˢ ((M ⇓ᵇ)ˢ →ˢ (M′ ⇓ᵇ)ˢ)
   ×ˢ ((M ⇑)ˢ →ˢ ((M′ ⇑)ˢ ⊎ˢ (M′ ⇓ᵇ)ˢ))
pre-ℰ c ↩ M M′ =
      (∀ˢ[ V′ ] (M′ ⇓ᵗ V′)ˢ →ˢ (∃ˢ[ V ] (M ⇓ᵗ V)ˢ ×ˢ pre-𝒱 c ↩ V V′))
   ×ˢ ((M′ ⇓ᵇ)ˢ →ˢ (M ⇓ᵇ)ˢ)
   ×ˢ ((M′ ⇑)ˢ →ˢ (M ⇑)ˢ)

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (c , d , V , V′)) = pre-𝒱 c d V V′
pre-ℰ⊎𝒱 (inj₂ (c , d , M , M′)) = pre-ℰ c d M M′

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X

𝒱⟦_⟧ : (c : Prec) → Dir → Term → Term → Setᵒ
𝒱⟦ c ⟧ d V V′ = ℰ⊎𝒱 (inj₁ (c , d , V , V′))

ℰ⟦_⟧ : (c : Prec) → Dir → Term → Term → Setᵒ
ℰ⟦ c ⟧ d M M′ = ℰ⊎𝒱 (inj₂ (c , d , M , M′))

ℰ↪-stmt : ∀{c}{M M′}
  → ℰ⟦ c ⟧ ↪ M M′ ≡ᵒ
        ((∀ᵒ[ V ]  (M ⇓ᵗ V)ᵒ →ᵒ ((∃ᵒ[ V′ ] (M′ ⇓ᵗ V′)ᵒ ×ᵒ 𝒱⟦ c ⟧ ↪ V V′)
                            ⊎ᵒ (M′ ⇓ᵇ)ᵒ))
     ×ᵒ ((M ⇓ᵇ)ᵒ →ᵒ (M′ ⇓ᵇ)ᵒ)
     ×ᵒ ((M ⇑)ᵒ →ᵒ ((M′ ⇑)ᵒ ⊎ᵒ (M′ ⇓ᵇ)ᵒ)))
ℰ↪-stmt {c}{M}{M′} =
  let X₂ = inj₂ (c , ↪ , M , M′) in
  ℰ⟦ c ⟧ ↪ M M′                                                ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 X₂                                     ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₂ ⟩
  # (pre-ℰ⊎𝒱 X₂) (ℰ⊎𝒱 , ttᵖ)
      ⩦⟨ (cong-×ᵒ (cong-∀ λ V → cong-→{S = (M ⇓ᵗ V)ᵒ} (≡ᵒ-refl refl) (cong-⊎ᵒ (cong-∃ (λ V′ → cong-×ᵒ (≡ᵒ-refl refl) (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (c , ↪ , V , V′)))))) (≡ᵒ-refl refl))) (≡ᵒ-refl refl)) ⟩
      ((∀ᵒ[ V ]  (M ⇓ᵗ V)ᵒ →ᵒ ((∃ᵒ[ V′ ] (M′ ⇓ᵗ V′)ᵒ ×ᵒ 𝒱⟦ c ⟧ ↪ V V′)
                            ⊎ᵒ (M′ ⇓ᵇ)ᵒ))
   ×ᵒ ((M ⇓ᵇ)ᵒ →ᵒ (M′ ⇓ᵇ)ᵒ)
   ×ᵒ ((M ⇑)ᵒ →ᵒ ((M′ ⇑)ᵒ ⊎ᵒ (M′ ⇓ᵇ)ᵒ)))           ∎

ℰ↩-stmt : ∀{c}{M M′}
  → ℰ⟦ c ⟧ ↩ M M′ ≡ᵒ
      ((∀ᵒ[ V′ ] (M′ ⇓ᵗ V′)ᵒ →ᵒ (∃ᵒ[ V ] (M ⇓ᵗ V)ᵒ ×ᵒ 𝒱⟦ c ⟧ ↩ V V′))
   ×ᵒ ((M′ ⇓ᵇ)ᵒ →ᵒ (M ⇓ᵇ)ᵒ)
   ×ᵒ ((M′ ⇑)ᵒ →ᵒ (M ⇑)ᵒ))
ℰ↩-stmt {c}{M}{M′} =
  let X₂ = inj₂ (c , ↩ , M , M′) in
  ℰ⟦ c ⟧ ↩ M M′                                                ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 X₂                                     ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₂ ⟩
  # (pre-ℰ⊎𝒱 X₂) (ℰ⊎𝒱 , ttᵖ)
      ⩦⟨ cong-×ᵒ (cong-∀ λ V′ → cong-→{S = (M′ ⇓ᵗ V′)ᵒ} (≡ᵒ-refl refl) (cong-∃ λ V → cong-×ᵒ (≡ᵒ-refl refl) (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (c , ↩ , V , V′)))))) (cong-×ᵒ (≡ᵒ-refl refl) (≡ᵒ-refl refl)) ⟩
      ((∀ᵒ[ V′ ] (M′ ⇓ᵗ V′)ᵒ →ᵒ (∃ᵒ[ V ] (M ⇓ᵗ V)ᵒ ×ᵒ 𝒱⟦ c ⟧ ↩ V V′))
   ×ᵒ ((M′ ⇓ᵇ)ᵒ →ᵒ (M ⇓ᵇ)ᵒ)
   ×ᵒ ((M′ ⇑)ᵒ →ᵒ (M ⇑)ᵒ))            ∎

𝒱-base : ∀{ι}{d}{c}{c′}
  → 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ d ($ c) ($ c′) ≡ᵒ (c ≡ c′) ᵒ
𝒱-base{ι}{d}{c}{c′} = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

𝒱-base-intro : ∀{𝒫}{ι}{d}{c} → 𝒫 ⊢ᵒ 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ d ($ c) ($ c)
𝒱-base-intro{ι}{d}{c} = substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl)

𝒱-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{d}{N}{N′}
   → (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ d (ƛ N) (ƛ N′))
      ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((𝒱⟦ A , A′ , A⊑A′ ⟧ d W W′)
                         →ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ d (N [ W ]) (N′ [ W′ ]))))
𝒱-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{d}{N}{N′} =
   let X₁ = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , d , ƛ N , ƛ N′) in
   let X₂ = λ W W′ → inj₁ ((A , A′ , A⊑A′) , d , W , W′) in
   let X₃ = λ W W′ → inj₂ ((B , B′ , B⊑B′) , d , N [ W ] , N′ [ W′ ]) in
   (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ d (ƛ N) (ƛ N′))    ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X₁                                            ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₁ ⟩
   # (pre-ℰ⊎𝒱 X₁) (ℰ⊎𝒱 , ttᵖ)
     ⩦⟨ cong-∀ (λ W → cong-∀ λ W′ →
           cong-→ (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (X₂ W W′)))
                  (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (X₃ W W′)))) ⟩
   (∀ᵒ[ W ] ∀ᵒ[ W′ ] (𝒱⟦ A , A′ , A⊑A′ ⟧ d W W′
                    →ᵒ ℰ⟦ B , B′ , B⊑B′ ⟧ d (N [ W ]) (N′ [ W′ ])))    ∎

𝒱-fun-elim : ∀{𝒫}{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{dir}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′
   → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀{W W′} → 𝒫 ⊢ᵒ (𝒱⟦ A , A′ , c ⟧ dir W W′)
                             →ᵒ (ℰ⟦ B , B′ , d ⟧ dir (N [ W ]) (N′ [ W′ ])))
             → 𝒫 ⊢ᵒ R)
     --------------------------------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-fun-elim {𝒫}{A}{B}{A′}{B′}{c}{d}{dir}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ { 𝒱VV′sn → G {V}{V′} 𝒱VV′sn ⊢𝒱VV′ cont }
  where
  G : ∀{V}{V′}{n}
     → # (𝒱⟦  A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′
     → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀{W W′} → 𝒫 ⊢ᵒ (𝒱⟦ A , A′ , c ⟧ dir W W′)
                             →ᵒ (ℰ⟦ B , B′ , d ⟧ dir (N [ W ]) (N′ [ W′ ])))
             → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G {ƛ N}{ƛ N′}{n} 𝒱VV′ ⊢𝒱VV′ cont = cont N N′ refl refl λ {W}{W′} →
     instᵒ (instᵒ (substᵒ 𝒱-fun ⊢𝒱VV′) W) W′ 

{- Relate Open Terms -}

𝓖⟦_⟧ : (Γ : List Prec) → Dir → Subst → Subst → List Setᵒ
𝓖⟦ [] ⟧ d σ σ′ = []
𝓖⟦ c ∷ Γ ⟧ d σ σ′ = (𝒱⟦ c ⟧ d (σ 0) (σ′ 0))
                     ∷ 𝓖⟦ Γ ⟧ d (λ x → σ (suc x)) (λ x → σ′ (suc x))

_∣_⊨_⊑_⦂_ : List Prec → Dir → Term → Term → Prec → Set
Γ ∣ d ⊨ M ⊑ M′ ⦂ c = ∀ (γ γ′ : Subst)
   → 𝓖⟦ Γ ⟧ d γ γ′ ⊢ᵒ ℰ⟦ c ⟧ d (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′)

{- Related values are syntactic values -}

𝒱⇒Value : ∀ {k}{d} c M M′
   → # (𝒱⟦ c ⟧ d M M′) (suc k)
     ------------------------
   → Value M × Value M′
𝒱⇒Value {k} (.★ , ★ , unk⊑) (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
𝒱⇒Value {k} (.★ , $ₜ ι′ , unk⊑) (V ⟨ $ᵍ ι !⟩) ($ c) 𝒱MM′
    with  ($ᵍ ι) ≡ᵍ ($ᵍ ι′)
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , _ = (v 〈 $ᵍ ι′ 〉) , ($̬ c)
𝒱⇒Value {k} (.★ , A′ ⇒ B′ , unk⊑) (V ⟨ ★⇒★ !⟩) V′ 𝒱VV′
    with 𝒱VV′
... | v , v′ , _ = (v 〈 ★⇒★ 〉) , v′
𝒱⇒Value {k} ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) refl = ($̬ c) , ($̬ c)
𝒱⇒Value {k} ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) 𝒱VV′ =
    (ƛ̬ N) , (ƛ̬ N′)

{- Related values are related expressions -}

𝒱⇒ℰ : ∀{c : Prec}{d}{𝒫}{V V′}
   → 𝒫 ⊢ᵒ 𝒱⟦ c ⟧ d V V′
     -------------------
   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ d V V′
𝒱⇒ℰ {c}{↪}{𝒫}{V}{V′} ⊢𝒱VV′ = substᵒ (≡ᵒ-sym ℰ↪-stmt)
  ((Λᵒ[ V₁ ] (→ᵒI
     (⊢ᵒ-sucP Zᵒ (λ (k , A , ⊢V , ⊢V₁ , v , evalV=V₁) → 
     (inj₁ᵒ (⊢ᵒ-∃-intro {!!} ({!!} ,ᵒ {!!})))))
     ))
  ,ᵒ ({!!} ,ᵒ {!!}))
𝒱⇒ℰ {c}{↩}{𝒫}{V}{V′} ⊢𝒱VV′ = substᵒ (≡ᵒ-sym ℰ↩-stmt) {!!}
