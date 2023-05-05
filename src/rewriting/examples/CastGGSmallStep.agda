{-# OPTIONS --rewriting #-}
module rewriting.examples.CastGGSmallStep where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties 
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.CastPrecision
open import rewriting.examples.StepIndexedLogic2

ℰ⇐⊎𝒱⇐-type : Set
ℰ⇐⊎𝒱⇐-type = (Prec × Term × Term) ⊎ (Prec × Term × Term)

ℰ⇐⊎𝒱⇐-ctx : Context
ℰ⇐⊎𝒱⇐-ctx = ℰ⇐⊎𝒱⇐-type ∷ []

ℰ⇐ˢ⟦_⟧ : ∀{A}{B} → A ⊑ B → Term → Term → Setˢ ℰ⇐⊎𝒱⇐-ctx (cons Now ∅)
ℰ⇐ˢ⟦_⟧ {A}{B} A⊑B M M′ = (inj₂ ((A , B , A⊑B) , M , M′)) ∈ zeroˢ

𝒱⇐ˢ⟦_⟧ : ∀{A}{B} → A ⊑ B → Term → Term → Setˢ ℰ⇐⊎𝒱⇐-ctx (cons Now ∅)
𝒱⇐ˢ⟦_⟧ {A}{B} A⊑B V V′ = (inj₁ ((A , B , A⊑B) , V , V′)) ∈ zeroˢ

aux-ℰ⇐ : ∀{A}{A′} → A ⊑ A′ → Term → Term → Setˢ ℰ⇐⊎𝒱⇐-ctx (cons Later ∅)
aux-𝒱⇐ : ∀{A}{A′} → A ⊑ A′ → Term → Term → Setˢ ℰ⇐⊎𝒱⇐-ctx (cons Later ∅)

aux-𝒱⇐ unk⊑unk (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl =
      let g = gnd⇒ty G in
      (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ (▷ˢ (𝒱⇐ˢ⟦ Refl⊑{g} ⟧ V V′))
... | no neq = ⊥ ˢ
aux-𝒱⇐ unk⊑unk V V′ = ⊥ ˢ
aux-𝒱⇐ {.★}{.A′} (unk⊑any{G}{A′} G⊑A′) (V ⟨ H !⟩) V′
    with G ≡ᵍ H
... | yes refl =    
     (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ (aux-𝒱⇐ G⊑A′ V V′)
... | no neq = ⊥ ˢ     
aux-𝒱⇐ {.★}{.A′} (unk⊑any{G}{A′} G⊑A′) V V′ = ⊥ ˢ
aux-𝒱⇐ {.($ₜ ι)}{.($ₜ ι)} (base⊑{ι}) ($ c) ($ c′) = (c ≡ c′) ˢ
aux-𝒱⇐ {.($ₜ ι)}{.($ₜ ι)} (base⊑{ι}) V V′ = ⊥ ˢ
aux-𝒱⇐ {.(A ⇒ B)}{.(A′ ⇒ B′)} (fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) (ƛ N) (ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] (aux-𝒱⇐ A⊑A′ W W′)
                      →ˢ (aux-ℰ⇐ B⊑B′ (N [ W ]) (N′ [ W′ ]))
aux-𝒱⇐ {.(A ⇒ B)}{.(A′ ⇒ B′)} (fun⊑{A}{B}{A′}{B′} A⊑A′ B⊑B′) V V′ = ⊥ ˢ

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

aux-ℰ⇐ c M M′ =
    ((Value M′)ˢ ×ˢ (∃ˢ[ V ] (M —↠ V)ˢ ×ˢ (Value V)ˢ ×ˢ aux-𝒱⇐ c V M′))
  ⊎ˢ (∃ˢ[ N′ ] (M′ —→ N′)ˢ ×ˢ ▷ˢ (ℰ⇐ˢ⟦ c ⟧ M N′))
  ⊎ˢ (Blame M′)ˢ

aux-ℰ⇐⊎𝒱⇐ : ℰ⇐⊎𝒱⇐-type → Setˢ ℰ⇐⊎𝒱⇐-ctx (cons Later ∅)
aux-ℰ⇐⊎𝒱⇐ (inj₁ ((A , B , lt) , V , V′)) = aux-𝒱⇐ lt V V′
aux-ℰ⇐⊎𝒱⇐ (inj₂ ((A , B , lt) , M , M′)) = aux-ℰ⇐ lt M M′

ℰ⇐⊎𝒱⇐ : ℰ⇐⊎𝒱⇐-type → Setᵒ
ℰ⇐⊎𝒱⇐ X = μᵒ aux-ℰ⇐⊎𝒱⇐ X

𝒱⇐⟦_⟧ : (c : Prec)  → Term → Term → Setᵒ
𝒱⇐⟦ c ⟧ V V′ = ℰ⇐⊎𝒱⇐ (inj₁ (c , V , V′))

ℰ⇐⟦_⟧ : (c : Prec) → Term → Term → Setᵒ
ℰ⇐⟦ c ⟧ M M′ = ℰ⇐⊎𝒱⇐ (inj₂ (c , M , M′))

{- Names for parts of ℰ⇐ -}
catchup⇐ : Prec → Term → Term → Setᵒ
catchup⇐ c M V′ = (Value V′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ
                                   ×ᵒ 𝒱⇐⟦ c ⟧ V V′)

step⇐ : Prec → Term → Term → Setᵒ
step⇐ c M M′ = (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (ℰ⇐⟦ c ⟧ M N′))

ℰ⇐-stmt : ∀{c}{M M′}
  → ℰ⇐⟦ c ⟧ M M′ ≡ᵒ catchup⇐ c M M′ ⊎ᵒ step⇐ c M M′ ⊎ᵒ (Blame M′)ᵒ
ℰ⇐-stmt {c}{M}{M′} =
  ℰ⇐⟦ c ⟧ M M′
         ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ aux-ℰ⇐⊎𝒱⇐ X₂
          ⩦⟨ fixpointᵒ aux-ℰ⇐⊎𝒱⇐ X₂ ⟩
  # (aux-ℰ⇐⊎𝒱⇐ X₂) (ℰ⇐⊎𝒱⇐ , ttᵖ)
          ⩦⟨ EQ ⟩
  catchup⇐ c M M′ ⊎ᵒ step⇐ c M M′ ⊎ᵒ (Blame M′)ᵒ
          ∎
  where
  X₁ = λ V → (inj₁ (c , V , M′))
  X₂ = inj₂ (c , M , M′)
  EQ : # (aux-ℰ⇐⊎𝒱⇐ X₂) (ℰ⇐⊎𝒱⇐ , ttᵖ)
     ≡ᵒ catchup⇐ c M M′ ⊎ᵒ step⇐ c M M′ ⊎ᵒ (Blame M′)ᵒ
  EQ = cong-⊎ᵒ (cong-×ᵒ (≡ᵒ-refl refl) (cong-∃ (λ V → cong-×ᵒ (≡ᵒ-refl refl)
                   (cong-×ᵒ (≡ᵒ-refl refl)
                           (≡ᵒ-sym (fixpointᵒ aux-ℰ⇐⊎𝒱⇐ (X₁ V)))))))
               (≡ᵒ-refl refl)

𝒱⇐-dyn-dyn : ∀{G}{V}{V′}
  → 𝒱⇐⟦ ★ , ★ , unk⊑unk ⟧ (V ⟨ G !⟩) (V′ ⟨ G !⟩)
    ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ
           ×ᵒ ▷ᵒ (𝒱⇐⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V V′)
𝒱⇐-dyn-dyn {G}{V}{V′} =
  𝒱⇐⟦ ★ , ★ , unk⊑unk ⟧ (V ⟨ G !⟩) (V′ ⟨ G !⟩)
         ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⇐⊎𝒱⇐ X₁
         ⩦⟨ fixpointᵒ aux-ℰ⇐⊎𝒱⇐ X₁ ⟩
  # (aux-ℰ⇐⊎𝒱⇐ X₁) (ℰ⇐⊎𝒱⇐ , ttᵖ)
         ⩦⟨ EQ ⟩
  (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⇐⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V V′) ∎
  where
  X₁ = inj₁ ((★ , ★ , unk⊑unk) , (V ⟨ G !⟩) , (V′ ⟨ G !⟩)) 
  EQ : # (aux-ℰ⇐⊎𝒱⇐ X₁) (ℰ⇐⊎𝒱⇐ , ttᵖ)
       ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ 
           ×ᵒ ▷ᵒ (𝒱⇐⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V V′)
  EQ
      with G ≡ᵍ G
  ... | yes refl = ≡ᵒ-refl refl
  ... | no neq = ⊥-elim (neq refl)

𝒱⇐-dyn-any : ∀{G}{A′}{V}{V′}
   → (G⊑A′ : gnd⇒ty G ⊑ A′)
   → 𝒱⇐⟦ ★ , A′ , unk⊑any{G} G⊑A′ ⟧ (V ⟨ G !⟩) V′
     ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⇐⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V V′)
𝒱⇐-dyn-any {G}{A′}{V}{V′} G⊑A′ =
  𝒱⇐⟦ ★ , A′ , unk⊑any{G} G⊑A′ ⟧ (V ⟨ G !⟩) V′
                ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⇐⊎𝒱⇐ (X₁ G A′ G⊑A′)
                ⩦⟨ fixpointᵒ aux-ℰ⇐⊎𝒱⇐ (X₁ G A′ G⊑A′) ⟩
  # (aux-ℰ⇐⊎𝒱⇐ (X₁ G A′ G⊑A′)) (ℰ⇐⊎𝒱⇐ , ttᵖ)
                ⩦⟨ EQ G⊑A′ ⟩
  (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⇐⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V V′)
                ∎ 
  where
  X₁ = λ G A′ G⊑A′ → inj₁ ((★ , A′ , unk⊑any{G} G⊑A′) , (V ⟨ G !⟩) , V′)
  EQ : ∀{G}{A′}
     → (G⊑A′ : gnd⇒ty G ⊑ A′)
     → # (aux-ℰ⇐⊎𝒱⇐ (X₁ G A′ G⊑A′)) (ℰ⇐⊎𝒱⇐ , ttᵖ)
       ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ (𝒱⇐⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V V′)
  EQ {G} {A′} G⊑A′
      with G ≡ᵍ G
  ... | yes refl = cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
            (≡ᵒ-sym (fixpointᵒ aux-ℰ⇐⊎𝒱⇐
                 (inj₁ ((gnd⇒ty G , A′ , G⊑A′) , V , V′)) )))
  ... | no neq = ⊥-elim (neq refl)

𝒱⇐-base : ∀{ι}{c}{c′}
  → 𝒱⇐⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ ($ c) ($ c′) ≡ᵒ (c ≡ c′) ᵒ
𝒱⇐-base{ι}{c}{c′} = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

𝒱⇐-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{N}{N′}
   → (𝒱⇐⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ (ƛ N) (ƛ N′))
      ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((𝒱⇐⟦ A , A′ , A⊑A′ ⟧ W W′)
                         →ᵒ (ℰ⇐⟦ B , B′ , B⊑B′ ⟧ (N [ W ]) (N′ [ W′ ]))))
𝒱⇐-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{N}{N′} =
   let X₁ = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , ƛ N , ƛ N′) in
   let X₂ = λ W W′ → inj₁ ((A , A′ , A⊑A′) , W , W′) in
   let X₃ = λ W W′ → inj₂ ((B , B′ , B⊑B′) , N [ W ] , N′ [ W′ ]) in
   (𝒱⇐⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ (ƛ N) (ƛ N′))
            ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⇐⊎𝒱⇐ X₁
            ⩦⟨ fixpointᵒ aux-ℰ⇐⊎𝒱⇐ X₁ ⟩
   # (aux-ℰ⇐⊎𝒱⇐ X₁) (ℰ⇐⊎𝒱⇐ , ttᵖ)
            ⩦⟨ cong-∀ (λ W → cong-∀ λ W′ →
                  cong-→ (≡ᵒ-sym (fixpointᵒ aux-ℰ⇐⊎𝒱⇐ (X₂ W W′)))
                       (≡ᵒ-sym (fixpointᵒ aux-ℰ⇐⊎𝒱⇐ (X₃ W W′)))) ⟩
   (∀ᵒ[ W ] ∀ᵒ[ W′ ] (𝒱⇐⟦ A , A′ , A⊑A′ ⟧ W W′
                    →ᵒ ℰ⇐⟦ B , B′ , B⊑B′ ⟧ (N [ W ]) (N′ [ W′ ])))
            ∎

𝒱⇐-base-elim : ∀{𝒫}{V}{V′}{R}{ι}
  → 𝒫 ⊢ᵒ 𝒱⇐⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ V V′
  → (∀ c → V ≡ $ c → V′ ≡ $ c → 𝒫 ⊢ᵒ R)
  → 𝒫 ⊢ᵒ R
𝒱⇐-base-elim {𝒫}{V}{V′}{R}{ι} ⊢𝒱⇐VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱⇐VV′ λ 𝒱⇐VV′ → aux 𝒱⇐VV′ cont
  where
  aux : ∀{𝒫}{V}{V′}{R}{k}{ι}
    → #(𝒱⇐⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ V V′) (suc k)
    → (∀ c → V ≡ $ c → V′ ≡ $ c → 𝒫 ⊢ᵒ R)
    → 𝒫 ⊢ᵒ R
  aux {𝒫}{$ c}{$ c′}{R}{k}{ι} refl cont = cont c refl refl

𝒱⇐-dyn-dyn-elim : ∀{𝒫}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⇐⟦ ★ , ★ , unk⊑unk ⟧ V V′
   → (∀ V₁ V′₁ G → Value V₁ → Value V′₁ → V ≡ V₁ ⟨ G !⟩ → V′ ≡ V′₁ ⟨ G !⟩
       → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⇐⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V′₁ → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱⇐-dyn-dyn-elim {𝒫}{V}{V′}{R} ⊢𝒱⇐VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱⇐VV′ λ 𝒱⇐VV′ → aux 𝒱⇐VV′ ⊢𝒱⇐VV′ cont
  where
  aux : ∀{𝒫}{V}{V′}{R}{k}
     → #(𝒱⇐⟦ ★ , ★ , unk⊑unk ⟧ V V′) (suc k)
     → 𝒫 ⊢ᵒ 𝒱⇐⟦ ★ , ★ , unk⊑unk ⟧ V V′
     → (∀ V₁ V′₁ G → Value V₁ → Value V′₁ → V ≡ V₁ ⟨ G !⟩ → V′ ≡ V′₁ ⟨ G !⟩
         → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⇐⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V′₁ → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  aux {𝒫}{V ⟨ G !⟩}{V′ ⟨ H !⟩}{R} 𝒱⇐VV′ ⊢𝒱⇐VV′ cont
      with G ≡ᵍ H | 𝒱⇐VV′
  ... | yes refl | (v , v′ , _) =
        let ▷𝒱⇐VV′ = proj₂ᵒ (proj₂ᵒ (substᵒ 𝒱⇐-dyn-dyn ⊢𝒱⇐VV′)) in
        cont V V′ G v v′ refl refl ▷𝒱⇐VV′
  ... | no neq | ()

𝒱⇐-dyn-any-elim : ∀{𝒫}{V}{V′}{G}{A′}{R}
   → (G⊑A′ : gnd⇒ty G ⊑ A′)
   → 𝒫 ⊢ᵒ 𝒱⇐⟦ ★ , A′ , unk⊑any G⊑A′ ⟧ V V′
   → (∀ V₁ G → Value V₁ → V ≡ V₁ ⟨ G !⟩ → Value V′ → (G⊑A′ : gnd⇒ty G ⊑ A′)
       → 𝒫 ⊢ᵒ 𝒱⇐⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V₁ V′
       → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱⇐-dyn-any-elim {𝒫}{V}{V′}{G}{A′}{R} G⊑A′ ⊢𝒱⇐VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱⇐VV′ λ 𝒱⇐VV′ → aux G⊑A′ 𝒱⇐VV′ ⊢𝒱⇐VV′ cont
  where
  aux : ∀{𝒫}{V}{V′}{G}{A′}{R}{k}
     → (G⊑A′ : gnd⇒ty G ⊑ A′)
     → #(𝒱⇐⟦ ★ , A′ , unk⊑any G⊑A′ ⟧ V V′) (suc k)
     → 𝒫 ⊢ᵒ 𝒱⇐⟦ ★ , A′ , unk⊑any G⊑A′ ⟧ V V′
     → (∀ V₁ G → Value V₁ → V ≡ V₁ ⟨ G !⟩ → Value V′ → (G⊑A′ : gnd⇒ty G ⊑ A′)
         → 𝒫 ⊢ᵒ 𝒱⇐⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V₁ V′
         → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  aux {𝒫} {V ⟨ H !⟩} {V′} {G}{A′} {R} {k} G⊑A′ 𝒱⇐VV′ ⊢𝒱⇐VV′ cont
      with G ≡ᵍ H
  ... | no neq = ⊥-elim 𝒱⇐VV′
  ... | yes refl =
        let 𝒱⇐VV′₂ = proj₂ᵒ (proj₂ᵒ (substᵒ (𝒱⇐-dyn-any G⊑A′) ⊢𝒱⇐VV′)) in
        cont V G (proj₁ 𝒱⇐VV′) refl (proj₁ (proj₂ 𝒱⇐VV′)) G⊑A′ 𝒱⇐VV′₂
        
𝒱⇐-fun-elim : ∀{𝒫}{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⇐⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
   → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀ W W′ → 𝒫 ⊢ᵒ (𝒱⇐⟦ A , A′ , c ⟧ W W′)
                            →ᵒ (ℰ⇐⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ])))
             → 𝒫 ⊢ᵒ R)
     --------------------------------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱⇐-fun-elim {𝒫}{A}{B}{A′}{B′}{c}{d}{V}{V′}{R} ⊢𝒱⇐VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱⇐VV′ λ { 𝒱⇐VV′sn → aux {V}{V′} 𝒱⇐VV′sn ⊢𝒱⇐VV′ cont }
  where
  aux : ∀{V}{V′}{n}
     → # (𝒱⇐⟦  A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⇐⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
     → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀ W W′ → 𝒫 ⊢ᵒ (𝒱⇐⟦ A , A′ , c ⟧ W W′)
                             →ᵒ (ℰ⇐⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ])))
             → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  aux {ƛ N}{ƛ N′}{n} 𝒱⇐VV′ ⊢𝒱⇐VV′ cont = cont N N′ refl refl λ W W′ →
     instᵒ (instᵒ (substᵒ 𝒱⇐-fun ⊢𝒱⇐VV′) W) W′ 

{------------------- Relate Open Terms -------------------------------------}

𝓖⇐⟦_⟧ : (Γ : List Prec) → Subst → Subst → List Setᵒ
𝓖⇐⟦ [] ⟧ σ σ′ = []
𝓖⇐⟦ c ∷ Γ ⟧ σ σ′ = (𝒱⇐⟦ c ⟧ (σ 0) (σ′ 0))
                     ∷ 𝓖⇐⟦ Γ ⟧ (λ x → σ (suc x)) (λ x → σ′ (suc x))

_⊢⇐_⊑_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊢⇐ M ⊑ M′ ⦂ c = ∀ (γ γ′ : Subst)
   → wtsub γ (map proj₁ Γ) []
   → wtsub γ′ (map (λ x → proj₁ (proj₂ x)) Γ) []
   → 𝓖⇐⟦ Γ ⟧ γ γ′ ⊢ᵒ ℰ⇐⟦ c ⟧ (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′)

{------------------- Related values are syntactic values ----------------------}

𝒱⇐→Value : ∀ {k} c M M′
   → # (𝒱⇐⟦ c ⟧ M M′) (suc k)
     ------------------------
   → Value M × Value M′
𝒱⇐→Value {k} (.★ , .★ , unk⊑unk) (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱⇐MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱⇐MM′
... | yes refl
    with 𝒱⇐MM′
... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
𝒱⇐→Value {k} (.★ , A′ , unk⊑any{G} G⊑A′) (V ⟨ H !⟩) V′ 𝒱⇐MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱⇐MM′
... | yes refl
    with 𝒱⇐MM′
... | v , v′ , _ = (v 〈 G 〉) , v′
𝒱⇐→Value {k} ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) refl = ($̬ c) , ($̬ c)
𝒱⇐→Value {k} ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) 𝒱⇐VV′ =
    (ƛ̬ N) , (ƛ̬ N′)

{--------- Related values are related expressions -----------------------------}

𝒱⇐→ℰ⇐ : ∀{c : Prec}{𝒫}{V}{V′}
   → 𝒫 ⊢ᵒ 𝒱⇐⟦ c ⟧ V V′
     -----------------
   → 𝒫 ⊢ᵒ ℰ⇐⟦ c ⟧ V V′
𝒱⇐→ℰ⇐ {c} {𝒫} {V} {V′} ⊢𝒱VV′ =
  substᵒ (≡ᵒ-sym ℰ⇐-stmt) (inj₁ᵒ
  (⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ →
  let (v , v′) = 𝒱⇐→Value c V V′ 𝒱VV′ in
  constᵒI v′ ,ᵒ
  ⊢ᵒ-∃-intro-new (λ X → (V —↠ X)ᵒ ×ᵒ (Value X)ᵒ ×ᵒ 𝒱⇐⟦ c ⟧ X V′)
  V
  (constᵒI (V END) ,ᵒ (constᵒI v ,ᵒ ⊢𝒱VV′))))

{---------- Blame is more precise than any term -------------------------------}

ℰ-blame : ∀{𝒫}{c}{M} → 𝒫 ⊢ᵒ ℰ⇐⟦ c ⟧ M blame
ℰ-blame {𝒫} {c} {M} =
  substᵒ (≡ᵒ-sym ℰ⇐-stmt) (inj₂ᵒ (inj₂ᵒ (constᵒI isBlame)))

{---------- Compatibility Lemmas ----------------------------------------------}

compatible-nat : ∀{Γ}{n : ℕ}
   → Γ ⊢⇐ $ (Num n) ⊑ $ (Num n) ⦂ ($ₜ ′ℕ , $ₜ ′ℕ , base⊑)
compatible-nat {Γ}{n} γ γ′ ⊢γ ⊢γ′ =
  𝒱⇐→ℰ⇐ (substᵒ (≡ᵒ-sym 𝒱⇐-base) (constᵒI refl))

compatible-bool : ∀{Γ}{b : 𝔹}
   → Γ ⊢⇐ $ (Bool b) ⊑ $ (Bool b) ⦂ ($ₜ ′𝔹 , $ₜ ′𝔹 , base⊑)
compatible-bool {Γ}{b} γ γ′ ⊢γ ⊢γ′ =
  𝒱⇐→ℰ⇐ (substᵒ (≡ᵒ-sym 𝒱⇐-base) (constᵒI refl))

compatible-blame : ∀{Γ}{A}{M}
   → map proj₁ Γ ⊢ M ⦂ A
     -------------------------------
   → Γ ⊢⇐ M ⊑ blame ⦂ (A , A , Refl⊑)
compatible-blame ⊢M γ γ′ ⊢γ ⊢γ′ = ℰ-blame

lookup-𝓖⇐ : (Γ : List Prec) → (γ γ′ : Subst)
  → ∀ {A}{A′}{A⊑A′}{y} → Γ ∋ y ⦂ (A , A′ , A⊑A′)
  → 𝓖⇐⟦ Γ ⟧ γ γ′ ⊢ᵒ 𝒱⇐⟦ (A , A′ , A⊑A′) ⟧ (γ y) (γ′ y)
lookup-𝓖⇐ (.(A , A′ , A⊑A′) ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {zero} refl = Zᵒ
lookup-𝓖⇐ (B ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {suc y} ∋y =
   Sᵒ (lookup-𝓖⇐ Γ (λ x → γ (suc x)) (λ x → γ′ (suc x)) ∋y)

compatibility-var : ∀ {Γ A A′ A⊑A′ x}
  → Γ ∋ x ⦂ (A , A′ , A⊑A′)
    -------------------------------
  → Γ ⊢⇐ ` x ⊑ ` x ⦂ (A , A′ , A⊑A′)
compatibility-var {Γ}{A}{A′}{A⊑A′}{x} ∋x γ γ′ ⊢γ ⊢γ′
    rewrite sub-var γ x | sub-var γ′ x = 𝒱⇐→ℰ⇐ (lookup-𝓖⇐ Γ γ γ′ ∋x)

compatible-lambda : ∀{Γ : List Prec}{A}{B}{C}{D}{N N′ : Term}
     {c : A ⊑ C}{d : B ⊑ D}
   → ((A , C , c) ∷ Γ) ⊢⇐ N ⊑ N′ ⦂ (B , D , d)
     -----------------------------------------------
   → Γ ⊢⇐ (ƛ N) ⊑ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
compatible-lambda{Γ}{A}{B}{C}{D}{N}{N′}{c}{d} ⊢⇐N⊑N′ γ γ′ ⊢γ ⊢γ′ = ⊢ℰ⇐λNλN′
 where
 ⊢ℰ⇐λNλN′ : 𝓖⇐⟦ Γ ⟧ γ γ′
            ⊢ᵒ ℰ⇐⟦ A ⇒ B , C ⇒ D , fun⊑ c d ⟧ (⟪ γ ⟫ (ƛ N)) (⟪ γ′ ⟫ (ƛ N′))
 ⊢ℰ⇐λNλN′ = 𝒱⇐→ℰ⇐ (substᵒ (≡ᵒ-sym 𝒱⇐-fun) (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI 𝓔N[W]N′[W′]))
  where
  𝓔N[W]N′[W′] : ∀{W W′} → 𝒱⇐⟦ A , C , c ⟧ W W′ ∷ 𝓖⇐⟦ Γ ⟧ γ γ′
       ⊢ᵒ  ℰ⇐⟦ B , D , d ⟧ ((⟪ ext γ ⟫ N) [ W ]) ((⟪ ext γ′ ⟫ N′) [ W′ ])
  𝓔N[W]N′[W′] {W}{W′} = appᵒ (Sᵒ (→ᵒI (⊢⇐N⊑N′ (W • γ) (W′ • γ′) {!!} {!!}))) Zᵒ

compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊢⇐ L ⊑ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d)
   → Γ ⊢⇐ M ⊑ M′ ⦂ (A , A′ , c)
     ----------------------------------
   → Γ ⊢⇐ L · M ⊑ L′ · M′ ⦂ (B , B′ , d)
compatible-app {Γ}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′}
  ⊢⇐L⊑L′ ⊢⇐M⊑M′ γ γ′ ⊢γ ⊢γ′ = {!!}

compatible-inj-L : ∀{Γ : List Prec}{G A′}{c : gnd⇒ty G ⊑ A′}{M M′ : Term}
   → Γ ⊩ M ⊑ M′ ⦂ c
   → Γ ⊢⇐ M ⊑ M′ ⦂ (gnd⇒ty G , A′ , c)
     ------------------------------------------
   → Γ ⊢⇐ M ⟨ G !⟩ ⊑ M′ ⦂ (★ , A′ , unk⊑any c)
compatible-inj-L{Γ}{G}{A′}{c}{M}{M′} ⊢M⊑M′ ⊢⇐M⊑M′ γ γ′ ⊢γ ⊢γ′
    with precision→typed ⊢M⊑M′
... | ⊢M , ⊢M′
    with progress (sub-pres-type{σ = γ′} ⊢M′ ⊢γ′)
... | error b = substᵒ (≡ᵒ-sym ℰ⇐-stmt) (inj₂ᵒ (inj₂ᵒ (constᵒI b)))
... | step M′—→N = {!!}
compatible-inj-L{Γ}{G}{A′}{c}{M}{M′} ⊢M⊑M′ ⊢⇐M⊑M′ γ γ′ ⊢γ ⊢γ′
    | ⊢M , ⊢M′
    | done m′ = substᵒ (≡ᵒ-sym ℰ⇐-stmt) (inj₁ᵒ (constᵒI m′ ,ᵒ Catchup))
  where
  Catchup : 𝓖⇐⟦ Γ ⟧ γ γ′ ⊢ᵒ (∃ᵒ[ V ] (⟪ γ ⟫ M ⟨ G !⟩ —↠ V)ᵒ ×ᵒ (Value V)ᵒ
                                ×ᵒ 𝒱⇐⟦ ★ , A′ , unk⊑any c ⟧ V (⟪ γ′ ⟫ M′))
  Catchup =
   case3ᵒ (substᵒ ℰ⇐-stmt (⊢⇐M⊑M′ γ γ′ ⊢γ ⊢γ′))
   {- Case 1: M′ is a value, M catches up -}
   (⊢ᵒ-∃-elim-new (λ V → (⟪ γ ⟫ M —↠ V)ᵒ ×ᵒ (Value V)ᵒ
                         ×ᵒ 𝒱⇐⟦ gnd⇒ty G , A′ , c ⟧ V (⟪ γ′ ⟫ M′))
     (proj₂ᵒ Zᵒ)
     λ V →
     ⊢ᵒ-∃-intro-new (λ V₁ → ((⟪ γ ⟫ M ⟨ G !⟩) —↠ V₁) ᵒ ×ᵒ Value V₁ ᵒ
                            ×ᵒ 𝒱⇐⟦ ★ , A′ , unk⊑any c ⟧ V₁ (⟪ γ′ ⟫ M′))
     (V ⟨ G !⟩)
     (⊢ᵒ-sucP (proj₁ᵒ (proj₂ᵒ Zᵒ)) λ v →
     (⊢ᵒ-sucP (proj₁ᵒ Zᵒ) λ M—↠V →
     (constᵒI (ξ* □⟨ G !⟩ M—↠V) ,ᵒ (constᵒI (v 〈 _ 〉) ,ᵒ
     substᵒ (≡ᵒ-sym (𝒱⇐-dyn-any c))
            (constᵒI v ,ᵒ (constᵒI m′ ,ᵒ (proj₂ᵒ (proj₂ᵒ Zᵒ))))
     )))))
   {- Case 2: M′ can take a step, contradiction! -}
   (⊢ᵒ-∃-elim-new (λ N′ → (⟪ γ′ ⟫ M′ —→ N′)ᵒ ×ᵒ
                ▷ᵒ (ℰ⇐⟦ gnd⇒ty G , A′ , c ⟧ (⟪ γ ⟫ M) N′)) Zᵒ
     λ N′ →
     ⊢ᵒ-sucP (proj₁ᵒ Zᵒ) λ M′—→N′ →
     ⊥-elim (value-irreducible m′ M′—→N′))
   {- Case 3: M′ is blame, contradiction! -}
   (⊢ᵒ-sucP Zᵒ λ b → ⊥-elim (blame-not-value m′ (blame-eq-blame b)))
     where
     blame-eq-blame : ∀{M} → Blame M → M ≡ blame
     blame-eq-blame {.blame} isBlame = refl

compatible-inj-R : ∀{Γ}{G}{c : ★ ⊑ gnd⇒ty G }{M M′}
   → Γ ⊢⇐ M ⊑ M′ ⦂ (★ , gnd⇒ty G , c)
   → Γ ⊢⇐ M ⊑ M′ ⟨ G !⟩ ⦂ (★ , ★ , unk⊑unk)
compatible-inj-R{Γ}{G}{unk⊑}{M}{M′} ⊢⇐M⊑M′ γ γ′ ⊢γ ⊢γ′ = {!!}

compatible-proj-L : ∀{Γ}{H}{A′}{c : gnd⇒ty H ⊑ A′}{M}{M′}
   → Γ ⊢⇐ M ⊑ M′ ⦂ (★ , A′ ,  unk⊑any c)
   → Γ ⊢⇐ M ⟨ H ?⟩ ⊑ M′ ⦂ (gnd⇒ty H , A′ , c)
compatible-proj-L {Γ}{H}{A′}{c}{M}{M′} ⊢⇐M⊑M′ γ γ′ ⊢γ ⊢γ′ =
  substᵒ (≡ᵒ-sym ℰ⇐-stmt) {!!}

compatible-proj-R : ∀{Γ}{H′}{c : ★ ⊑ gnd⇒ty H′}{M}{M′}
   → Γ ⊢⇐ M ⊑ M′ ⦂ (★ , ★ , unk⊑unk)
   → Γ ⊢⇐ M ⊑ M′ ⟨ H′ ?⟩ ⦂ (★ , gnd⇒ty H′ , c)
compatible-proj-R {Γ}{H′}{c}{M}{M′} ⊢⇐M⊑M′ γ γ′ ⊢γ ⊢γ′ = {!!}


fundamental : ∀ {Γ}{A}{A′}{A⊑A′ : A ⊑ A′} → (M M′ : Term)
  → Γ ⊩ M ⊑ M′ ⦂ A⊑A′
    ----------------------------
  → Γ ⊢⇐ M ⊑ M′ ⦂ (A , A′ , A⊑A′)
fundamental {Γ} {A} {A′} {A⊑A′} .(` _) .(` _) (⊑-var ∋x) =
   compatibility-var ∋x
fundamental {Γ} {_} {_} {base⊑} ($ (Num n)) ($ (Num n)) ⊑-lit =
   compatible-nat
fundamental {Γ} {_} {_} {base⊑} ($ (Bool b)) ($ (Bool b)) ⊑-lit =
   compatible-bool
fundamental {Γ} {A} {A′} {A⊑A′} (L · M) (L′ · M′) (⊑-app ⊢L⊑L′ ⊢M⊑M′) =
    compatible-app{L = L}{L′}{M}{M′} (fundamental L L′ ⊢L⊑L′)
                                     (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {.(_ ⇒ _)} {.(_ ⇒ _)} {.(fun⊑ _ _)} (ƛ N)(ƛ N′) (⊑-lam ⊢N⊑N′) =
    compatible-lambda{N = N}{N′} (fundamental N N′ ⊢N⊑N′)
fundamental {Γ} {★} {A′} {unk⊑} (M ⟨ G !⟩) M′ (⊑-inj-L ⊢M⊑M′) =
    compatible-inj-L{G =  G}{M = M}{M′} ⊢M⊑M′ (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {★} {★} {.unk⊑unk} M (M′ ⟨ G !⟩) (⊑-inj-R ⊢M⊑M′) =
    compatible-inj-R{Γ}{G = G}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {_} {A′} {A⊑A′} (M ⟨ H ?⟩) M′ (⊑-proj-L ⊢M⊑M′) =
    compatible-proj-L{Γ}{H}{A′}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.(gnd⇒ty _)} {A⊑A′} M (M′ ⟨ H′ ?⟩) (⊑-proj-R ⊢M⊑M′) =
    compatible-proj-R{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.A} {.Refl⊑} M .blame (⊑-blame ⊢M∶A) =
   compatible-blame ⊢M∶A

