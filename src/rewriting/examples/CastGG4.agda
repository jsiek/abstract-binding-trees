{-# OPTIONS --rewriting #-}
module rewriting.examples.CastGG4 where

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
open import rewriting.examples.CastBigStep
open import rewriting.examples.StepIndexedLogic2

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Prec × Term × Term) ⊎ (Prec × Term × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

ℰˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A⊑B ⟧ M M′ = (inj₂ (A⊑B , M , M′)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A⊑B ⟧ V V′ = (inj₁ (A⊑B , V , V′)) ∈ zeroˢ

pre-ℰ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)


pre-𝒱 (★ , ★ , unk⊑) (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl =
      let g = gnd⇒ty G in
      (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ (▷ˢ (𝒱ˢ⟦ (g , g , Refl⊑) ⟧ V V′))
... | no neq = ⊥ ˢ
pre-𝒱 (.★ , $ₜ ι , unk⊑any lt′) (V ⟨ G !⟩) V′
    with gnd⇒ty G ⊑? ($ₜ ι)
... | yes lt = (Value V)ˢ ×ˢ (Value V′)ˢ
                  ×ˢ ▷ˢ (𝒱ˢ⟦ (gnd⇒ty G , $ₜ ι , lt) ⟧ V V′)
... | no nlt = ⊥ ˢ
pre-𝒱 (.★ , A′ ⇒ B′ , unk⊑any lt′) (V ⟨ G !⟩) V′
    with gnd⇒ty G ⊑? (A′ ⇒ B′)
... | yes lt = (Value V)ˢ ×ˢ (Value V′)ˢ
                   ×ˢ ▷ˢ (𝒱ˢ⟦ (gnd⇒ty G , A′ ⇒ B′ , lt) ⟧ V V′)
... | no nlt = ⊥ ˢ
pre-𝒱 ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) = (c ≡ c′) ˢ
pre-𝒱 ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] (pre-𝒱 (A , A′ , A⊑A′) W W′)
                      →ˢ (pre-ℰ (B , B′ , B⊑B′) (N [ W ]) (N′ [ W′ ]))
pre-𝒱 (A , A′ , A⊑A′) V V′ = ⊥ ˢ

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

pre-ℰ c M M′ = (∀ˢ[ V′ ] (M′ ⇓ V′)ˢ →ˢ (Value V′)ˢ
                →ˢ (▷ˢ (∃ˢ[ V ] (M ⇓ V)ˢ ×ˢ (Value V)ˢ ×ˢ (𝒱ˢ⟦ c ⟧ V V′))))

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (c , V , V′)) = pre-𝒱 c V V′
pre-ℰ⊎𝒱 (inj₂ (c , M , M′)) = pre-ℰ c M M′

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X

𝒱⟦_⟧ : (c : Prec)  → Term → Term → Setᵒ
𝒱⟦ c ⟧ V V′ = ℰ⊎𝒱 (inj₁ (c , V , V′))

ℰ⟦_⟧ : (c : Prec) → Term → Term → Setᵒ
ℰ⟦ c ⟧ M M′ = ℰ⊎𝒱 (inj₂ (c , M , M′))

{------------- Equations for ℰ and 𝒱 -----------------------------------------}

⇓⇒⇓𝒱 : Prec → Term → Term → Setᵒ
⇓⇒⇓𝒱 c M M′ = ∀ᵒ[ V′ ] (M′ ⇓ V′)ᵒ →ᵒ (Value V′)ᵒ
               →ᵒ (▷ᵒ (∃ᵒ[ V ] (M ⇓ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ 𝒱⟦ c ⟧ V V′))

ℰ-def : Prec → Term → Term → Setᵒ
ℰ-def c M M′ = (⇓⇒⇓𝒱 c M M′)

{- Names for parts of ⇓⇒⇓𝒱 -}
∃V𝒱 : Prec → Term → Term → Term → Setᵒ
∃V𝒱 c M V V′ = (M ⇓ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ 𝒱⟦ c ⟧ V V′

∀V′→∃V𝒱 : Prec → Term → Term → Term → Setᵒ
∀V′→∃V𝒱 c M M′ V′ = (M′ ⇓ V′)ᵒ →ᵒ (Value V′)ᵒ →ᵒ ▷ᵒ (∃ᵒ[ V ] ∃V𝒱 c M V V′)


ℰ-stmt : ∀{c}{M M′} → ℰ⟦ c ⟧ M M′ ≡ᵒ ℰ-def c M M′
ℰ-stmt {c}{M}{M′} =
  let X₂ = inj₂ (c , M , M′) in
  ℰ⟦ c ⟧ M M′                                      ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 X₂                                    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₂ ⟩
  # (pre-ℰ⊎𝒱 X₂) (ℰ⊎𝒱 , ttᵖ)                       ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ-def c M M′                                      ∎
{-
where
  EQ = cong-∀ λ V′ →
        cong-→{S = (M′ ⇓ V′)ᵒ} (≡ᵒ-refl refl)
        (cong-→{S = (Value V′)ᵒ} (≡ᵒ-refl refl)
          (cong-▷
          (cong-∃ λ V → cong-×ᵒ (≡ᵒ-refl refl)
            (cong-×ᵒ (≡ᵒ-refl refl)
            (≡ᵒ-refl refl)
            ))))
            --(≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (_ , V , V′))))
-}

𝒱-dyn-dyn : ∀{G}{V}{V′}
  → 𝒱⟦ ★ , ★ , unk⊑unk ⟧ (V ⟨ G !⟩) (V′ ⟨ G !⟩)
    ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ
       ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V V′)
𝒱-dyn-dyn {G}{V}{V′} =
  𝒱⟦ ★ , ★ , unk⊑unk ⟧ (V ⟨ G !⟩) (V′ ⟨ G !⟩)        ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X₁                                             ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₁ ⟩
  # (pre-ℰ⊎𝒱 X₁) (ℰ⊎𝒱 , ttᵖ)                        ⩦⟨ EQ ⟩
  (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V V′) ∎
  where
  X₁ = inj₁ ((★ , ★ , unk⊑unk) , (V ⟨ G !⟩) , (V′ ⟨ G !⟩)) 
  EQ : # (pre-ℰ⊎𝒱 X₁) (ℰ⊎𝒱 , ttᵖ)
       ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ 
           ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V V′)
  EQ
      with G ≡ᵍ G
  ... | yes refl = ≡ᵒ-refl refl
  ... | no neq = ⊥-elim (neq refl)

𝒱-dyn-any : ∀{G}{A′}{V}{V′}
   → (G⊑A′ : gnd⇒ty G ⊑ A′)
   → 𝒱⟦ ★ , A′ , unk⊑any G⊑A′ ⟧ (V ⟨ G !⟩) V′
     ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V V′)
𝒱-dyn-any {G}{A′}{V}{V′} G⊑A′ =
  𝒱⟦ ★ , A′ , unk⊑any _ ⟧ (V ⟨ G !⟩) V′                         ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 (X₁ G A′)                               ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 (X₁ G A′) ⟩
  # (pre-ℰ⊎𝒱 (X₁ G A′)) (ℰ⊎𝒱 , ttᵖ)                               ⩦⟨ EQ G⊑A′ ⟩
  (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V V′)  ∎ 
  where
  X₁ = λ G A′ → inj₁ ((★ , A′ , unk⊑any _) , (V ⟨ G !⟩) , V′)
  EQ : ∀{G}{A′}
     → (G⊑A′ : gnd⇒ty G ⊑ A′)
     → # (pre-ℰ⊎𝒱 (X₁ G A′)) (ℰ⊎𝒱 , ttᵖ)
       ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V V′)
  EQ {$ᵍ ι} {.($ₜ ι)} base⊑
      with ($ₜ ι) ⊑? ($ₜ ι)
  ... | no nlt = ⊥-elim (nlt base⊑)
  ... | yes base⊑ = ≡ᵒ-refl refl
  EQ {★⇒★} {.(_ ⇒ _)} (fun⊑ unk⊑unk unk⊑unk) = ≡ᵒ-refl refl

𝒱-base : ∀{ι}{c}{c′}
  → 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ ($ c) ($ c′) ≡ᵒ (c ≡ c′) ᵒ
𝒱-base{ι}{c}{c′} = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

𝒱-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{N}{N′}
   → (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ (ƛ N) (ƛ N′))
      ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((𝒱⟦ A , A′ , A⊑A′ ⟧ W W′)
                         →ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ (N [ W ]) (N′ [ W′ ]))))
𝒱-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{N}{N′} =
   let X₁ = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , ƛ N , ƛ N′) in
   let X₂ = λ W W′ → inj₁ ((A , A′ , A⊑A′) , W , W′) in
   let X₃ = λ W W′ → inj₂ ((B , B′ , B⊑B′) , N [ W ] , N′ [ W′ ]) in
   (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ (ƛ N) (ƛ N′))    ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X₁                                            ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₁ ⟩
   # (pre-ℰ⊎𝒱 X₁) (ℰ⊎𝒱 , ttᵖ)
     ⩦⟨ cong-∀ (λ W → cong-∀ λ W′ →
           cong-→ (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (X₂ W W′)))
                  (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (X₃ W W′)))) ⟩
   (∀ᵒ[ W ] ∀ᵒ[ W′ ] (𝒱⟦ A , A′ , A⊑A′ ⟧ W W′
                    →ᵒ ℰ⟦ B , B′ , B⊑B′ ⟧ (N [ W ]) (N′ [ W′ ])))    ∎

{------------- Intro for 𝒱 ---------------------------------------------------}

𝒱-base-intro : ∀{𝒫}{ι}{c} → 𝒫 ⊢ᵒ 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ ($ c) ($ c)
𝒱-base-intro{ι}{c} = substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl)

{------------- Elim for ℰ ----------------------------------------------------}

ℰ-converge : ∀{𝒫}{c}{M}{M′}{V′}{R}
   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ M M′
   → 𝒫 ⊢ᵒ (M′ ⇓ V′)ᵒ
   → 𝒫 ⊢ᵒ (Value V′)ᵒ
   → (𝒫 ⊢ᵒ ▷ᵒ (∃ᵒ[ V ] (M ⇓ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ 𝒱⟦ c ⟧ V V′)
        → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
ℰ-converge {𝒫}{c}{M}{M′}{V′}{R} ℰMM′ M′⇓V′ v′ cont =
  let ex = appᵒ (appᵒ (instᵒ (substᵒ ℰ-stmt ℰMM′) V′) M′⇓V′) v′ in
  cont ex


{------------- Elim for 𝒱, by cases on A ⊑ A′ --------------------------------}

𝒱-base-elim : ∀{𝒫}{V}{V′}{R}{ι}
  → 𝒫 ⊢ᵒ 𝒱⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ V V′
  → (∀ c → V ≡ $ c → V′ ≡ $ c → 𝒫 ⊢ᵒ R)
  → 𝒫 ⊢ᵒ R
𝒱-base-elim {𝒫}{V}{V′}{R}{ι} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ → aux 𝒱VV′ cont
  where
  aux : ∀{𝒫}{V}{V′}{R}{k}{ι}
    → #(𝒱⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ V V′) (suc k)
    → (∀ c → V ≡ $ c → V′ ≡ $ c → 𝒫 ⊢ᵒ R)
    → 𝒫 ⊢ᵒ R
  aux {𝒫}{$ c}{$ c′}{R}{k}{ι} refl cont = cont c refl refl

𝒱-dyn-dyn-elim : ∀{𝒫}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑unk ⟧ V V′
   → (∀ V₁ V′₁ G → Value V₁ → Value V′₁ → V ≡ V₁ ⟨ G !⟩ → V′ ≡ V′₁ ⟨ G !⟩
       → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V′₁ → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱-dyn-dyn-elim {𝒫}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ → aux 𝒱VV′ ⊢𝒱VV′ cont
  where
  aux : ∀{𝒫}{V}{V′}{R}{k}
     → #(𝒱⟦ ★ , ★ , unk⊑unk ⟧ V V′) (suc k)
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑unk ⟧ V V′
     → (∀ V₁ V′₁ G → Value V₁ → Value V′₁ → V ≡ V₁ ⟨ G !⟩ → V′ ≡ V′₁ ⟨ G !⟩
         → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V′₁ → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  aux {𝒫}{V ⟨ G !⟩}{V′ ⟨ H !⟩}{R} 𝒱VV′ ⊢𝒱VV′ cont
      with G ≡ᵍ H | 𝒱VV′
  ... | yes refl | (v , v′ , _) =
        let ▷𝒱VV′ = proj₂ᵒ (proj₂ᵒ (substᵒ 𝒱-dyn-dyn ⊢𝒱VV′)) in
        cont V V′ G v v′ refl refl ▷𝒱VV′
  ... | no neq | ()

𝒱-dyn-any-elim : ∀{𝒫}{V}{V′}{A′}{R}
   → A′ ≢ ★
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , A′ , unk⊑any _ ⟧ V V′
   → (∀ V₁ G → Value V₁ → V ≡ V₁ ⟨ G !⟩ → Value V′ → (G⊑A′ : gnd⇒ty G ⊑ A′)
       → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V₁ V′
       → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱-dyn-any-elim {𝒫}{V}{V′}{A′}{R} And ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ → aux 𝒱VV′ And ⊢𝒱VV′ cont
  where
  aux : ∀{𝒫}{V}{V′}{A′}{R}{k}{lt′}
     → #(𝒱⟦ ★ , A′ , unk⊑any lt′ ⟧ V V′) (suc k)
     → A′ ≢ ★
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , A′ , unk⊑any lt′ ⟧ V V′
     → (∀ V₁ G → Value V₁ → V ≡ V₁ ⟨ G !⟩ → Value V′ → (G⊑A′ : gnd⇒ty G ⊑ A′)
         → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V₁ V′
         → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  aux {𝒫} {V} {V′} {★}  {R} {k} 𝒱VV′ nd ⊢𝒱VV′ cont =
     ⊥-elim (nd refl)
  aux {𝒫} {V ⟨ G !⟩} {V′} {$ₜ ι}  {R} {k}{lt′}  𝒱VV′ nd ⊢𝒱VV′ cont
      with gnd⇒ty G ⊑? ($ₜ ι) | 𝒱VV′
  ... | yes lt | (v , v′ , _) =
        let ▷𝒱VV′ = proj₂ᵒ (proj₂ᵒ (substᵒ (𝒱-dyn-any lt′) ⊢𝒱VV′)) in
        cont V G v refl v′ lt ▷𝒱VV′
  ... | no nlt | ()
  aux {𝒫} {V ⟨ G !⟩} {V′} {A′ ⇒ B′}  {R} {k} {lt′} 𝒱VV′ nd ⊢𝒱VV′ cont
      with gnd⇒ty G ⊑? (A′ ⇒ B′) | 𝒱VV′
  ... | yes lt | (v , v′ , _) =
        let ▷𝒱VV′ = proj₂ᵒ (proj₂ᵒ (substᵒ (𝒱-dyn-any lt′) ⊢𝒱VV′)) in
        cont V G v refl v′ lt ▷𝒱VV′
  ... | no nlt | ()

𝒱-fun-elim : ∀{𝒫}{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
   → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀ W W′ → 𝒫 ⊢ᵒ (𝒱⟦ A , A′ , c ⟧ W W′)
                            →ᵒ (ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ])))
             → 𝒫 ⊢ᵒ R)
     --------------------------------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-fun-elim {𝒫}{A}{B}{A′}{B′}{c}{d}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ { 𝒱VV′sn → aux {V}{V′} 𝒱VV′sn ⊢𝒱VV′ cont }
  where
  aux : ∀{V}{V′}{n}
     → # (𝒱⟦  A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
     → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀ W W′ → 𝒫 ⊢ᵒ (𝒱⟦ A , A′ , c ⟧ W W′)
                             →ᵒ (ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ])))
             → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  aux {ƛ N}{ƛ N′}{n} 𝒱VV′ ⊢𝒱VV′ cont = cont N N′ refl refl λ W W′ →
     instᵒ (instᵒ (substᵒ 𝒱-fun ⊢𝒱VV′) W) W′ 

{------------------- Relate Open Terms -------------------------------------}

𝓖⟦_⟧ : (Γ : List Prec) → Subst → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ σ′ = []
𝓖⟦ c ∷ Γ ⟧ σ σ′ = (𝒱⟦ c ⟧ (σ 0) (σ′ 0))
                     ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x)) (λ x → σ′ (suc x))

_⊨_⊑_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊨ M ⊑ M′ ⦂ c = ∀ (γ γ′ : Subst)
   → 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ℰ⟦ c ⟧ (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′)

{------------------- Related values are syntactic values ----------------------}

𝒱⇒Value : ∀ {k} c M M′
   → # (𝒱⟦ c ⟧ M M′) (suc k)
     ------------------------
   → Value M × Value M′
𝒱⇒Value {k} (.★ , ★ , unk⊑unk) (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
𝒱⇒Value {k} (.★ , $ₜ ι , unk⊑any _) (V ⟨ G !⟩) V′ 𝒱MM′
    with (gnd⇒ty G) ⊑? ($ₜ ι)
... | no nlt = ⊥-elim 𝒱MM′
... | yes lt
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , v′
𝒱⇒Value {k} (.★ , (A′ ⇒ B′) , unk⊑any _) (V ⟨ G !⟩) V′ 𝒱MM′
    with (gnd⇒ty G) ⊑? (A′ ⇒ B′)
... | no nlt = ⊥-elim 𝒱MM′
... | yes lt
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , v′
𝒱⇒Value {k} ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) refl = ($̬ c) , ($̬ c)
𝒱⇒Value {k} ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) 𝒱VV′ =
    (ƛ̬ N) , (ƛ̬ N′)

{- Related values are related expressions -}

𝒱⇒ℰ : ∀{c : Prec}{𝒫}{V}{V′}
   → 𝒫 ⊢ᵒ 𝒱⟦ c ⟧ V V′
     -----------------
   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ V V′
𝒱⇒ℰ {c} {𝒫} {V} {V′} ⊢𝒱VV′ =
  substᵒ (≡ᵒ-sym ℰ-stmt)
  (Λᵒ[ W′ ] →ᵒI{P = (V′ ⇓ W′)ᵒ} (→ᵒI{P = (Value W′)ᵒ}
  (⊢ᵒ-sucP (Sᵒ (Sᵒ ⊢𝒱VV′)) λ 𝒱VV′ →
  let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′ in
  let 𝒫₁ = Value W′ ᵒ ∷ (V′ ⇓ W′) ᵒ ∷ 𝒫 in
  let ⊢V′⇓W′ : 𝒫₁ ⊢ᵒ (V′ ⇓ W′)ᵒ
      ⊢V′⇓W′ = Sᵒ Zᵒ in
  ⊢ᵒ-sucP ⊢V′⇓W′ λ V′⇓W′ →
  let eq = (⇓-determ (⇓-value V′ v′) V′⇓W′) in
  subst (λ W′ → Value W′ ᵒ ∷ (V′ ⇓ W′) ᵒ ∷ 𝒫
               ⊢ᵒ ▷ᵒ (∃ᵒ[ W ] (V ⇓ W)ᵒ ×ᵒ (Value W)ᵒ ×ᵒ (𝒱⟦ c ⟧ W W′)))
        eq
  (monoᵒ (⊢ᵒ-∃-intro-new (λ W → (V ⇓ W) ᵒ ×ᵒ Value W ᵒ ×ᵒ (𝒱⟦ c ⟧ W V′)) V
    (constᵒI (⇓-value V v) ,ᵒ (constᵒI v ,ᵒ (Sᵒ (Sᵒ ⊢𝒱VV′))))))
  )))

{---------- Blame is more precise than any term -------------------------------}

ℰ-blame : ∀{𝒫}{c}{M} → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ M blame
ℰ-blame {𝒫} {c} {M} = substᵒ (≡ᵒ-sym ℰ-stmt) (Λᵒ[ V′ ] (→ᵒI{P = (blame ⇓ V′)ᵒ}
  (⊢ᵒ-sucP Zᵒ λ b⇓V′ → Goal b⇓V′)))
  where
  Goal : ∀{V′} → blame ⇓ V′
     → ((blame ⇓ V′)ᵒ) ∷ 𝒫 ⊢ᵒ ((Value V′)ᵒ) →ᵒ ▷ᵒ (∃ᵒ[ V ] (∃V𝒱 c M V V′))
  Goal {V′} b⇓V′
      with ⇓-determ b⇓V′ blame⇓
  ... | refl = →ᵒI {P = (Value blame)ᵒ} (⊢ᵒ-sucP Zᵒ λ ())
    
{---------- Compatibility Lemmas ----------------------------------------------}

compatible-nat : ∀{Γ}{n : ℕ}
   → Γ ⊨ $ (Num n) ⊑ $ (Num n) ⦂ ($ₜ ′ℕ , $ₜ ′ℕ , base⊑)
compatible-nat {Γ}{n} γ γ′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))

compatible-bool : ∀{Γ}{b : 𝔹}
   → Γ ⊨ $ (Bool b) ⊑ $ (Bool b) ⦂ ($ₜ ′𝔹 , $ₜ ′𝔹 , base⊑)
compatible-bool {Γ}{b} γ γ′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))

compatible-blame : ∀{Γ}{A}{M}
   → map proj₁ Γ ⊢ M ⦂ A
     -------------------------------
   → Γ ⊨ M ⊑ blame ⦂ (A , A , Refl⊑)
compatible-blame ⊢M γ γ′ = ℰ-blame

lookup-𝓖 : (Γ : List Prec) → (γ γ′ : Subst)
  → ∀ {A}{A′}{A⊑A′}{y} → Γ ∋ y ⦂ (A , A′ , A⊑A′)
  → 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ 𝒱⟦ (A , A′ , A⊑A′) ⟧ (γ y) (γ′ y)
lookup-𝓖 (.(A , A′ , A⊑A′) ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {zero} refl = Zᵒ
lookup-𝓖 (B ∷ Γ) γ γ′ {A} {A′} {A⊑A′} {suc y} ∋y =
   Sᵒ (lookup-𝓖 Γ (λ x → γ (suc x)) (λ x → γ′ (suc x)) ∋y)

compatibility-var : ∀ {Γ A A′ A⊑A′ x}
  → Γ ∋ x ⦂ (A , A′ , A⊑A′)
    -------------------------------
  → Γ ⊨ ` x ⊑ ` x ⦂ (A , A′ , A⊑A′)
compatibility-var {Γ}{A}{A′}{A⊑A′}{x} ∋x γ γ′
    rewrite sub-var γ x | sub-var γ′ x = 𝒱⇒ℰ (lookup-𝓖 Γ γ γ′ ∋x)

compatible-lambda : ∀{Γ : List Prec}{A}{B}{C}{D}{N N′ : Term}
     {c : A ⊑ C}{d : B ⊑ D}
   → ((A , C , c) ∷ Γ) ⊨ N ⊑ N′ ⦂ (B , D , d)
     -----------------------------------------------
   → Γ ⊨ (ƛ N) ⊑ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
compatible-lambda{Γ}{A}{B}{C}{D}{N}{N′}{c}{d} ⊨N⊑N′ γ γ′ = ⊢ℰλNλN′
 where
 ⊢ℰλNλN′ : 𝓖⟦ Γ ⟧ γ γ′
            ⊢ᵒ ℰ⟦ A ⇒ B , C ⇒ D , fun⊑ c d ⟧ (⟪ γ ⟫ (ƛ N)) (⟪ γ′ ⟫ (ƛ N′))
 ⊢ℰλNλN′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI 𝓔N[W]N′[W′]))
  where
  𝓔N[W]N′[W′] : ∀{W W′} → 𝒱⟦ A , C , c ⟧ W W′ ∷ 𝓖⟦ Γ ⟧ γ γ′
       ⊢ᵒ  ℰ⟦ B , D , d ⟧ ((⟪ ext γ ⟫ N) [ W ]) ((⟪ ext γ′ ⟫ N′) [ W′ ])
  𝓔N[W]N′[W′] {W}{W′} = appᵒ (Sᵒ (→ᵒI (⊨N⊑N′ (W • γ) (W′ • γ′)))) Zᵒ

compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊨ L ⊑ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d)
   → Γ ⊨ M ⊑ M′ ⦂ (A , A′ , c)
     ----------------------------------
   → Γ ⊨ L · M ⊑ L′ · M′ ⦂ (B , B′ , d)
compatible-app {Γ}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′} ⊨L⊑L′ ⊨M⊑M′ γ γ′ =
  substᵒ (≡ᵒ-sym ℰ-stmt) ToValue
  where
  ToValue :
     𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ (∀ᵒ[ V′ ] (∀V′→∃V𝒱 (B , B′ , d)  (⟪ γ ⟫ (L · M))
                              (⟪ γ′ ⟫ (L′ · M′)) V′))
  ToValue = Λᵒ[ V′ ] →ᵒI{P = ((⟪ γ′ ⟫ (L′ · M′)) ⇓ V′)ᵒ} (→ᵒI{P = (Value V′)ᵒ}
    (⊢ᵒ-sucP Zᵒ λ v′ →  (⊢ᵒ-sucP (Sᵒ Zᵒ) λ LM′⇓V′ → {!!})))
    where
    Goal : ∀{V′}
       → Value V′
       → (⟪ γ′ ⟫ (L′ · M′)) ⇓ V′
       → (Value V′)ᵒ ∷ ((⟪ γ′ ⟫ (L′ · M′)) ⇓ V′)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
            ⊢ᵒ ∃ᵒ[ V ] (∃V𝒱 (B , B′ , d) (⟪ γ ⟫ (L · M)) V V′)
    Goal {V′} v′ (app⇓{N = N′}{W′} L′⇓λN′ M′⇓W′ w′ NW′⇓V′) =
     {!!}
{-     
     ℰ-converge (Sᵒ (Sᵒ (⊨L⊑L′ γ γ′))) (constᵒI L′⇓λN′) (constᵒI (ƛ̬ N′)) λ V →
     ℰ-converge (Sᵒ (Sᵒ (Sᵒ (⊨M⊑M′ γ γ′)))) (constᵒI M′⇓W′) (constᵒI w′) λ W →
     let 𝒱VV′ = proj₂ᵒ (proj₂ᵒ (Sᵒ Zᵒ)) in
     {!!}
     𝒱-fun-elim 𝒱VV′ λ {N N″ refl refl body →
     let 𝒱WW′ = proj₂ᵒ (proj₂ᵒ Zᵒ) in
     ℰ-converge (appᵒ (body W W′) 𝒱WW′) (constᵒI NW′⇓V′) (constᵒI v′) λ U → 
     ⊢ᵒ-∃-intro-new (λ V → (∃V𝒱 (B , B′ , d) (⟪ γ ⟫ (L · M)) V V′)) U
     let u = proj₁ᵒ (proj₂ᵒ Zᵒ) in
     ⊢ᵒ-sucP (proj₁ᵒ (Sᵒ (Sᵒ Zᵒ))) λ L⇓ →
     ⊢ᵒ-sucP (proj₁ᵒ (Sᵒ Zᵒ)) λ M⇓ →
     ⊢ᵒ-sucP (proj₁ᵒ (proj₂ᵒ (Sᵒ Zᵒ))) λ w →
     ⊢ᵒ-sucP (proj₁ᵒ Zᵒ) λ NW⇓U →
     (constᵒI (app⇓ L⇓ M⇓ w NW⇓U) ,ᵒ (u ,ᵒ proj₂ᵒ (proj₂ᵒ Zᵒ)))
     }
-}

compatible-inj-L : ∀{Γ}{G A′}{c : gnd⇒ty G ⊑ A′}{M M′}
   → Γ ⊨ M ⊑ M′ ⦂ (gnd⇒ty G , A′ , c)
     ----------------------------------------
   → Γ ⊨ M ⟨ G !⟩ ⊑ M′ ⦂ (★ , A′ , unk⊑any c)
compatible-inj-L{Γ}{G}{A′}{c}{M}{M′} ⊨M⊑M′ γ γ′ =
  substᵒ (≡ᵒ-sym ℰ-stmt) ToValue
  where
  ToValue : 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ⇓⇒⇓𝒱 (★ , A′ , unk⊑any c) ((⟪ γ ⟫ M) ⟨ G !⟩)(⟪ γ′ ⟫ M′)
  ToValue = Λᵒ[ V′ ] (→ᵒI {P = ((⟪ γ′ ⟫ M′) ⇓ V′)ᵒ} (→ᵒI {P = (Value V′)ᵒ}
    (⊢ᵒ-sucP Zᵒ λ v′ → 
    (⊢ᵒ-sucP (Sᵒ Zᵒ) λ M′⇓V′ →
    {!!}
    ))))
{-    
    ℰ-converge (Sᵒ (Sᵒ (⊨M⊑M′ γ γ′))) (constᵒI M′⇓V′) (constᵒI v′) λ V →
    ⊢ᵒ-∃-intro-new (λ W → (⟪ γ ⟫ M ⟨ G !⟩ ⇓ W)ᵒ ×ᵒ (Value W)ᵒ
                            ×ᵒ ▷ᵒ (𝒱⟦ ★ , A′ , unk⊑ ⟧ W V′))
    (V ⟨ G !⟩)
    (⊢ᵒ-sucP (proj₁ᵒ Zᵒ) λ M⇓V →
    (⊢ᵒ-sucP (proj₁ᵒ (proj₂ᵒ Zᵒ)) λ v →
    (constᵒI (inj⇓ M⇓V v) ,ᵒ (constᵒI (v 〈 _ 〉) ,ᵒ
      monoᵒ (substᵒ (≡ᵒ-sym (𝒱-dyn-any c))
        (constᵒI v ,ᵒ (constᵒI v′ ,ᵒ proj₂ᵒ (proj₂ᵒ Zᵒ))))
      ))))))))
-}

compatible-inj-R : ∀{Γ}{G}{c : ★ ⊑ gnd⇒ty G }{M M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , gnd⇒ty G , c)
   → Γ ⊨ M ⊑ M′ ⟨ G !⟩ ⦂ (★ , ★ , unk⊑unk)
compatible-inj-R{Γ}{G}{unk⊑}{M}{M′} ⊨M⊑M′ γ γ′ =
  substᵒ (≡ᵒ-sym ℰ-stmt) ToValue
  where
  ToValue : 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ⇓⇒⇓𝒱 (★ , ★ , unk⊑unk) (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′ ⟨ G !⟩)
  ToValue = Λᵒ[ V′ ] (→ᵒI {P = ((⟪ γ′ ⟫ M′ ⟨ G !⟩) ⇓ V′)ᵒ}
    (→ᵒI {P = (Value V′)ᵒ}
    (⊢ᵒ-sucP Zᵒ λ v′ → 
    (⊢ᵒ-sucP (Sᵒ Zᵒ) λ {(inj⇓{V = W′} M′⇓W′ w′) →
    {!!}
{-    
    ℰ-converge (Sᵒ (Sᵒ (⊨M⊑M′ γ γ′))) (constᵒI M′⇓W′) (constᵒI w′) λ V →
    ⊢ᵒ-∃-intro-new (λ W → (⟪ γ ⟫ M ⇓ W)ᵒ ×ᵒ (Value W)ᵒ
                            ×ᵒ ▷ᵒ (𝒱⟦ ★ , ★ , unk⊑ ⟧ W V′))
    V
    (proj₁ᵒ Zᵒ ,ᵒ {!!})
    -- (𝒱-dyn-any-elim (gnd-not-dyn{G}) (proj₂ᵒ (proj₂ᵒ Zᵒ))
    -- λ {V₁ G′ v₁ refl w″ G′⊑A′ ▷𝒱V₁V′ →
    -- proj₁ᵒ Zᵒ ,ᵒ (constᵒI (v₁ 〈 _ 〉) ,ᵒ Goal v₁ w″ G′⊑A′ ▷𝒱V₁V′)})}))))
    -}
    }))))
    
    where
    𝒫₁ = λ V₁ G′ W′ → (⟪ γ ⟫ M ⇓ (V₁ ⟨ G′ !⟩)) ᵒ ×ᵒ
              Value (V₁ ⟨ G′ !⟩) ᵒ ×ᵒ 𝒱⟦ ★ , gnd⇒ty G , unk⊑ ⟧ (V₁ ⟨ G′ !⟩) W′
          ∷  Value (W′ ⟨ G !⟩) ᵒ ∷ ((⟪ γ′ ⟫ M′ ⟨ G !⟩) ⇓ (W′ ⟨ G !⟩)) ᵒ
          ∷ 𝓖⟦ Γ ⟧ γ γ′
    Goal : ∀{V₁ G′ W′}
       → Value V₁
       → Value W′
       → (G′⊑A′ : gnd⇒ty G′ ⊑ gnd⇒ty G)
       → 𝒫₁ V₁ G′ W′ ⊢ᵒ (▷ᵒ 𝒱⟦ gnd⇒ty G′ , gnd⇒ty G , G′⊑A′ ⟧ V₁ W′)
       → 𝒫₁ V₁ G′ W′ ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑unk ⟧ (V₁ ⟨ G′ !⟩) (W′ ⟨ G !⟩)
    Goal {V₁}{G′}{W′} v₁ w′ G′⊑A′ ▷𝒱V₁V′
        with ⊑-gnd-unique G′⊑A′
    ... | refl
        with A⊑A-unique G′⊑A′
    ... | refl = (substᵒ (≡ᵒ-sym (𝒱-dyn-dyn{G′}))
                    (constᵒI v₁ ,ᵒ (constᵒI w′ ,ᵒ ▷𝒱V₁V′)))

above-gnd-not-dyn : ∀{H}{A′}
  → gnd⇒ty H ⊑ A′
  → A′ ≢ ★
above-gnd-not-dyn {$ᵍ ι} {.($ₜ ι)} base⊑ = λ ()
above-gnd-not-dyn {★⇒★} {.(_ ⇒ _)} (fun⊑ H⊑A′ H⊑A′₁) = λ ()

compatible-proj-L : ∀{Γ}{H}{A′}{c : gnd⇒ty H ⊑ A′}{M}{M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , A′ ,  unk⊑any c)
   → Γ ⊨ M ⟨ H ?⟩ ⊑ M′ ⦂ (gnd⇒ty H , A′ , c)
compatible-proj-L {Γ}{H}{A′}{c}{M}{M′} ⊨M⊑M′ γ γ′ =
  substᵒ (≡ᵒ-sym ℰ-stmt) ToValue
  where
  ToValue : 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ⇓⇒⇓𝒱(gnd⇒ty H , A′ , c)(⟪ γ ⟫ M ⟨ H ?⟩)(⟪ γ′ ⟫ M′)
  ToValue = Λᵒ[ V′ ] (→ᵒI {P = (⟪ γ′ ⟫ M′ ⇓ V′)ᵒ} (→ᵒI{P = (Value V′)ᵒ}
    (ℰ-converge (Sᵒ (Sᵒ (⊨M⊑M′ γ γ′))) (Sᵒ Zᵒ) Zᵒ λ ⊢▷∃VM⇓Vv𝒱VV′ →
     ▷→▷ ⊢▷∃VM⇓Vv𝒱VV′
     (⊢ᵒ-∃-elim-L (λ V → (⟪ γ ⟫ M ⇓ V) ᵒ ×ᵒ Value V ᵒ
                           ×ᵒ 𝒱⟦ ★ , A′ , unk⊑any c ⟧ V V′)
      λ V →
      𝒱-dyn-any-elim (above-gnd-not-dyn c) (proj₂ᵒ (proj₂ᵒ Zᵒ))
      λ {V₁ G v₁ refl v′ G⊑A′ ⊢▷𝒱V₁V′ →
       Goal G⊑A′ ⊢▷𝒱V₁V′
    }))))
    where
    𝒫₁ = λ V₁ G V′ → (⟪ γ ⟫ M ⇓ (V₁ ⟨ G !⟩)) ᵒ ×ᵒ
                Value (V₁ ⟨ G !⟩) ᵒ ×ᵒ 𝒱⟦ ★ , A′ , unk⊑any c ⟧ (V₁ ⟨ G !⟩) V′
          ∷ Value V′ ᵒ ∷ (⟪ γ′ ⟫ M′ ⇓ V′) ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
    Goal : ∀{V₁ G V′}
       → (G⊑A′ : gnd⇒ty G ⊑ A′)
       → 𝒫₁ V₁ G V′ ⊢ᵒ (▷ᵒ 𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V₁ V′)
       → 𝒫₁ V₁ G V′ ⊢ᵒ ∃ᵒ[ V ] ∃V𝒱 (gnd⇒ty H , A′ , c) (⟪ γ ⟫ M ⟨ H ?⟩) V V′
    Goal{V₁}{G}{V′} G⊑A′ ⊢▷𝒱V₁V′
        with gnd-unique G⊑A′ c
    ... | refl = 
     ⊢ᵒ-∃-intro-new (λ V → ∃V𝒱 (gnd⇒ty H , A′ , c) (⟪ γ ⟫ M ⟨ H ?⟩) V V′)
     V₁
     (⊢ᵒ-sucP (proj₁ᵒ Zᵒ) λ M⇓V₁! →
     (⊢ᵒ-sucP (proj₁ᵒ (proj₂ᵒ Zᵒ)) λ { (v₁ 〈 _ 〉) →
      (constᵒI (collapse⇓ M⇓V₁!) ,ᵒ (constᵒI v₁ ,ᵒ {!!}))}))



compatible-proj-R : ∀{Γ}{H′}{c : ★ ⊑ gnd⇒ty H′}{M}{M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , ★ , unk⊑unk)
   → Γ ⊨ M ⊑ M′ ⟨ H′ ?⟩ ⦂ (★ , gnd⇒ty H′ , c)
compatible-proj-R {Γ}{H′}{c}{M}{M′} ⊨M⊑M′ γ γ′ =
 substᵒ (≡ᵒ-sym ℰ-stmt) ToValue
 where
 ToValue : 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ⇓⇒⇓𝒱(★ , gnd⇒ty H′ , c)(⟪ γ ⟫ M)(⟪ γ′ ⟫ M′ ⟨ H′ ?⟩)
 ToValue = {!!}

fundamental : ∀ {Γ}{A}{A′}{A⊑A′ : A ⊑ A′} → (M M′ : Term)
  → Γ ⊩ M ⊑ M′ ⦂ A⊑A′
    ----------------------------
  → Γ ⊨ M ⊑ M′ ⦂ (A , A′ , A⊑A′)
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
fundamental {Γ} {★} {A′} {unk⊑any c} (M ⟨ G !⟩) M′ (⊑-inj-L ⊢M⊑M′) =
    compatible-inj-L{G =  G}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {★} {★} {.unk⊑unk} M (M′ ⟨ G !⟩) (⊑-inj-R ⊢M⊑M′) =
    compatible-inj-R{Γ}{G = G}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {_} {A′} {A⊑A′} (M ⟨ H ?⟩) M′ (⊑-proj-L ⊢M⊑M′) =
    compatible-proj-L{Γ}{H}{A′}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.(gnd⇒ty _)} {A⊑A′} M (M′ ⟨ H′ ?⟩) (⊑-proj-R ⊢M⊑M′) =
    compatible-proj-R{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.A} {.Refl⊑} M .blame (⊑-blame ⊢M∶A) =
   compatible-blame ⊢M∶A

