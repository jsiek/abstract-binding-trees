{-# OPTIONS --rewriting #-}
module rewriting.examples.CastGradualGuarantee2 where

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
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.CastBigStep
open import rewriting.examples.CastBigStepLogic
open import rewriting.examples.StepIndexedLogic2

infix 8 _⇓ᵒ_
_⇓ᵒ_ : Term → Term → Setᵒ
M ⇓ᵒ N = record { # = M ⇓ N
                ; down = downClosed⇓ M N
                ; tz = zero⇓
                }

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
pre-ℛ : Prec → Dir → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)

pre-𝒱 (★ , ★ , unk⊑) d (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl =
      let g = gnd⇒ty G in
      (Value V)ˢ ×ˢ (Value V′)ˢ ×ˢ (▷ˢ (𝒱ˢ⟦ (g , g , Refl⊑) ⟧ d V V′))
... | no neq = ⊥ ˢ
pre-𝒱 (.★ , $ₜ ι , unk⊑) d (V ⟨ G !⟩) V′
    with gnd⇒ty G ⊑? ($ₜ ι)
... | yes lt = (Value V)ˢ ×ˢ ▷ˢ (𝒱ˢ⟦ (gnd⇒ty G , $ₜ ι , lt) ⟧ d V V′)
... | no nlt = ⊥ ˢ
pre-𝒱 (.★ , A′ ⇒ B′ , unk⊑) d (V ⟨ G !⟩) V′
    with gnd⇒ty G ⊑? (A′ ⇒ B′)
... | yes lt = (Value V)ˢ ×ˢ ▷ˢ (𝒱ˢ⟦ (gnd⇒ty G , A′ ⇒ B′ , lt) ⟧ d V V′)
... | no nlt = ⊥ ˢ
pre-𝒱 ($ₜ ι , $ₜ ι , base⊑) d ($ c) ($ c′) = (c ≡ c′) ˢ
pre-𝒱 ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) d (ƛ N) (ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] (pre-𝒱 (A , A′ , A⊑A′) d W W′)
                      →ˢ (pre-ℰ (B , B′ , B⊑B′) d (N [ W ]) (N′ [ W′ ]))
pre-𝒱 (A , A′ , A⊑A′) d V V′ = ⊥ ˢ

pre-ℛ c dir R R′ = (pre-𝒱 c dir R R′) ⊎ˢ (R′ ≡ blame)ˢ 

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

pre-ℰ c ↪ M M′ =
      (∀ˢ[ R ] (M ⇓ᵒ R)ⁱ →ˢ (∃ˢ[ R′ ] (M′ ⇓ᵒ R′)ⁱ ×ˢ pre-ℛ c ↪ R R′))
pre-ℰ c ↩ M M′ =
      (∀ˢ[ R′ ] (M′ ⇓ᵒ R′)ⁱ →ˢ (∃ˢ[ R ] (M ⇓ᵒ R)ⁱ ×ˢ pre-ℛ c ↩ R R′))

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (c , d , V , V′)) = pre-𝒱 c d V V′
pre-ℰ⊎𝒱 (inj₂ (c , d , M , M′)) = pre-ℰ c d M M′

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X

𝒱⟦_⟧ : (c : Prec) → Dir → Term → Term → Setᵒ
𝒱⟦ c ⟧ d V V′ = ℰ⊎𝒱 (inj₁ (c , d , V , V′))

ℰ⟦_⟧ : (c : Prec) → Dir → Term → Term → Setᵒ
ℰ⟦ c ⟧ d M M′ = ℰ⊎𝒱 (inj₂ (c , d , M , M′))

ℛ⟦_⟧ : (c : Prec) → Dir → Term → Term → Setᵒ
ℛ⟦ c ⟧ d M M′ = (𝒱⟦ c ⟧ d M M′) ⊎ᵒ (M′ ≡ blame)ᵒ

ℰ↪-def : Prec → Term → Term → Setᵒ
ℰ↪-def c M M′ = (∀ᵒ[ R ] M ⇓ᵒ R →ᵒ (∃ᵒ[ R′ ] M′ ⇓ᵒ R′ ×ᵒ ℛ⟦ c ⟧ ↪ R R′))

ℰ↪-stmt : ∀{c}{M M′} → ℰ⟦ c ⟧ ↪ M M′ ≡ᵒ ℰ↪-def c M M′
ℰ↪-stmt {c}{M}{M′} =
  let X₂ = inj₂ (c , ↪ , M , M′) in
  ℰ⟦ c ⟧ ↪ M M′                                    ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 X₂                                    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₂ ⟩
  # (pre-ℰ⊎𝒱 X₂) (ℰ⊎𝒱 , ttᵖ)                       ⩦⟨ EQ ⟩
  ℰ↪-def c M M′                                      ∎
  where
  EQ = cong-∀ λ R → cong-→{S = M ⇓ᵒ R} (≡ᵒ-refl refl)
        (cong-∃ λ R′ → cong-×ᵒ{S = M′ ⇓ᵒ R′} (≡ᵒ-refl refl)
        (cong-⊎ᵒ ((≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (c , ↪ , R , R′)))))
        (≡ᵒ-refl refl)))

ℰ↩-def : Prec → Term → Term → Setᵒ
ℰ↩-def c M M′ = (∀ᵒ[ R′ ] M′ ⇓ᵒ R′ →ᵒ (∃ᵒ[ R ] M ⇓ᵒ R ×ᵒ ℛ⟦ c ⟧ ↩ R R′))

{------------- Equations for ℰ and 𝒱 -----------------------------------------}

ℰ↩-stmt : ∀{c}{M M′}
   → ℰ⟦ c ⟧ ↩ M M′ ≡ᵒ (∀ᵒ[ R′ ] M′ ⇓ᵒ R′ →ᵒ (∃ᵒ[ R ] M ⇓ᵒ R ×ᵒ ℛ⟦ c ⟧ ↩ R R′))
ℰ↩-stmt {c}{M}{M′} =
  let X₂ = inj₂ (c , ↩ , M , M′) in
  ℰ⟦ c ⟧ ↩ M M′                                    ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 X₂                                    ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₂ ⟩
  # (pre-ℰ⊎𝒱 X₂) (ℰ⊎𝒱 , ttᵖ)                       ⩦⟨ EQ ⟩
  ℰ↩-def c M M′                                      ∎
  where
  EQ = cong-∀ λ R′ → cong-→{S = M′ ⇓ᵒ R′} (≡ᵒ-refl refl)
        (cong-∃ λ R → cong-×ᵒ{S = M ⇓ᵒ R} (≡ᵒ-refl refl)
        (cong-⊎ᵒ ((≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (c , ↩ , R , R′)))))
        (≡ᵒ-refl refl)))

𝒱-dyn-dyn : ∀{G}{d}{V}{V′}
  → 𝒱⟦ ★ , ★ , unk⊑ ⟧ d (V ⟨ G !⟩) (V′ ⟨ G !⟩)
    ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ
       ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ d V V′)
𝒱-dyn-dyn {G}{d}{V}{V′} =
  𝒱⟦ ★ , ★ , unk⊑ ⟧ d (V ⟨ G !⟩) (V′ ⟨ G !⟩)        ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X₁                                             ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₁ ⟩
  # (pre-ℰ⊎𝒱 X₁) (ℰ⊎𝒱 , ttᵖ)                        ⩦⟨ EQ ⟩
  (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ d V V′) ∎
  where
  X₁ = inj₁ ((★ , ★ , unk⊑) , d , (V ⟨ G !⟩) , (V′ ⟨ G !⟩)) 
  EQ : # (pre-ℰ⊎𝒱 X₁) (ℰ⊎𝒱 , ttᵖ)
       ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ 
           ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ d V V′)
  EQ
      with G ≡ᵍ G
  ... | yes refl = ≡ᵒ-refl refl
  ... | no neq = ⊥-elim (neq refl)

𝒱-dyn-any : ∀{G}{A′}{d}{V}{V′}
   → (G⊑A′ : gnd⇒ty G ⊑ A′)
   → 𝒱⟦ ★ , A′ , unk⊑ ⟧ d (V ⟨ G !⟩) V′
     ≡ᵒ (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ d V V′)
𝒱-dyn-any {G}{A′}{d}{V}{V′} G⊑A′ =
  𝒱⟦ ★ , A′ , unk⊑ ⟧ d (V ⟨ G !⟩) V′                         ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 (X₁ G A′)                               ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 (X₁ G A′) ⟩
  # (pre-ℰ⊎𝒱 (X₁ G A′)) (ℰ⊎𝒱 , ttᵖ)                               ⩦⟨ EQ G⊑A′ ⟩
  (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ d V V′)  ∎ 
  where
  X₁ = λ G A′ → inj₁ ((★ , A′ , unk⊑) , d , (V ⟨ G !⟩) , V′)
  EQ : ∀{G}{A′}
     → (G⊑A′ : gnd⇒ty G ⊑ A′)
     → # (pre-ℰ⊎𝒱 (X₁ G A′)) (ℰ⊎𝒱 , ttᵖ)
       ≡ᵒ (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ d V V′)
  EQ {$ᵍ ι} {.($ₜ ι)} base⊑
      with ($ₜ ι) ⊑? ($ₜ ι)
  ... | no nlt = ⊥-elim (nlt base⊑)
  ... | yes base⊑ = ≡ᵒ-refl refl
  EQ {★⇒★} {.(_ ⇒ _)} (fun⊑ unk⊑ unk⊑) = ≡ᵒ-refl refl

𝒱-base : ∀{ι}{d}{c}{c′}
  → 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ d ($ c) ($ c′) ≡ᵒ (c ≡ c′) ᵒ
𝒱-base{ι}{d}{c}{c′} = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

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

{------------- Intro for 𝒱 ---------------------------------------------------}

𝒱-base-intro : ∀{𝒫}{ι}{d}{c} → 𝒫 ⊢ᵒ 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ d ($ c) ($ c)
𝒱-base-intro{ι}{d}{c} = substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl)

{------------- Elim for 𝒱, by cases on A ⊑ A′ --------------------------------}

𝒱-base-elim : ∀{𝒫}{V}{V′}{dir}{R}{k}{ι}
  → #(𝒱⟦ $ₜ ι , $ₜ ι , base⊑ ⟧ dir V V′) (suc k)
  → (∀ c → V ≡ $ c → V′ ≡ $ c → 𝒫 ⊢ᵒ R)
  → 𝒫 ⊢ᵒ R
𝒱-base-elim {𝒫}{$ c}{$ c′}{dir}{R}{k}{ι} refl cont = cont c refl refl

𝒱-dyn-dyn-elim : ∀{𝒫}{V}{V′}{dir}{R}{k}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑ ⟧ dir V V′
   → #(𝒱⟦ ★ , ★ , unk⊑ ⟧ dir V V′) (suc k)
   → (∀ V₁ V′₁ G → Value V₁ → Value V′₁ → V ≡ V₁ ⟨ G !⟩ → V′ ≡ V′₁ ⟨ G !⟩
       → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ dir V₁ V′₁ → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱-dyn-dyn-elim {𝒫}{V ⟨ G !⟩}{V′ ⟨ H !⟩}{dir}{R} ⊢𝒱VV′ 𝒱VV′ cont
    with G ≡ᵍ H | 𝒱VV′
... | yes refl | (v , v′ , _) =
      let ▷𝒱VV′ = proj₂ᵒ (proj₂ᵒ (substᵒ 𝒱-dyn-dyn ⊢𝒱VV′)) in
      cont V V′ G v v′ refl refl ▷𝒱VV′
... | no neq | ()

𝒱-dyn-any-elim : ∀{𝒫}{V}{V′}{A′}{dir}{R}{k}
   → A′ ≢ ★
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , A′ , unk⊑ ⟧ dir V V′
   → #(𝒱⟦ ★ , A′ , unk⊑ ⟧ dir V V′) (suc k)
   → (∀ V₁ G → Value V₁ → V ≡ V₁ ⟨ G !⟩ → (G⊑A′ : gnd⇒ty G ⊑ A′)
       → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ dir V₁ V′
       → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱-dyn-any-elim {𝒫} {V} {V′} {★} {dir} {R} {k} nd ⊢𝒱VV′ 𝒱VV′ cont =
   ⊥-elim (nd refl)
𝒱-dyn-any-elim {𝒫} {V ⟨ G !⟩} {V′} {$ₜ ι} {dir} {R} {k} nd ⊢𝒱VV′ 𝒱VV′ cont
    with gnd⇒ty G ⊑? ($ₜ ι) | 𝒱VV′
... | yes lt | (v , _) =
      let ▷𝒱VV′ = proj₂ᵒ (substᵒ (𝒱-dyn-any lt) ⊢𝒱VV′) in
      cont V G v refl lt ▷𝒱VV′
... | no nlt | ()
𝒱-dyn-any-elim {𝒫} {V ⟨ G !⟩} {V′} {A′ ⇒ B′} {dir} {R} {k} nd ⊢𝒱VV′ 𝒱VV′ cont
    with gnd⇒ty G ⊑? (A′ ⇒ B′) | 𝒱VV′
... | yes lt | (v , _) =
      let ▷𝒱VV′ = proj₂ᵒ (substᵒ (𝒱-dyn-any lt) ⊢𝒱VV′) in
      cont V G v refl lt ▷𝒱VV′
... | no nlt | ()

𝒱-fun-elim : ∀{𝒫}{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{dir}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ dir V V′
   → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀ W W′ → 𝒫 ⊢ᵒ (𝒱⟦ A , A′ , c ⟧ dir W W′)
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
             → (∀ W W′ → 𝒫 ⊢ᵒ (𝒱⟦ A , A′ , c ⟧ dir W W′)
                             →ᵒ (ℰ⟦ B , B′ , d ⟧ dir (N [ W ]) (N′ [ W′ ])))
             → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G {ƛ N}{ƛ N′}{n} 𝒱VV′ ⊢𝒱VV′ cont = cont N N′ refl refl λ W W′ →
     instᵒ (instᵒ (substᵒ 𝒱-fun ⊢𝒱VV′) W) W′ 

{- Relate Open Terms -}

𝓖⟦_⟧ : (Γ : List Prec) → Dir → Subst → Subst → List Setᵒ
𝓖⟦ [] ⟧ d σ σ′ = []
𝓖⟦ c ∷ Γ ⟧ d σ σ′ = (𝒱⟦ c ⟧ d (σ 0) (σ′ 0))
                     ∷ 𝓖⟦ Γ ⟧ d (λ x → σ (suc x)) (λ x → σ′ (suc x))

_∣_⊨_⊑_⦂_ : List Prec → Dir → Term → Term → Prec → Set
Γ ∣ d ⊨ M ⊑ M′ ⦂ c = ∀ (γ γ′ : Subst)
   → 𝓖⟦ Γ ⟧ d γ γ′ ⊢ᵒ ℰ⟦ c ⟧ d (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′)

-- {- Related values are syntactic values -}

-- 𝒱⇒Value : ∀ {k}{d} c M M′
--    → # (𝒱⟦ c ⟧ d M M′) (suc k)
--      ------------------------
--    → Value M × Value M′
-- 𝒱⇒Value {k} (.★ , ★ , unk⊑) (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱MM′
--     with G ≡ᵍ H
-- ... | no neq = ⊥-elim 𝒱MM′
-- ... | yes refl
--     with 𝒱MM′
-- ... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
-- 𝒱⇒Value {k}{d} (.★ , A′ , unk⊑) (V ⟨ G !⟩) V′ 𝒱MM′
--     with  gnd⇒ty G ⊑? A′
-- ... | no nlt = {!!}
-- ... | yes lt = {!!}
-- --     with 𝒱MM′
-- -- ... | v , _ = (v 〈 _ 〉) , ?
-- -- 𝒱⇒Value {k} (.★ , A′ ⇒ B′ , unk⊑) (V ⟨ ★⇒★ !⟩) V′ 𝒱VV′
-- --     with 𝒱VV′
-- -- ... | v , v′ , _ = (v 〈 ★⇒★ 〉) , v′
-- 𝒱⇒Value {k} ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) refl = ($̬ c) , ($̬ c)
-- 𝒱⇒Value {k} ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) 𝒱VV′ =
--     (ƛ̬ N) , (ƛ̬ N′)

-- {- Related values are related expressions -}

-- 𝒱⇒ℰ-pred : Prec → Dir → Setᵒ
-- 𝒱⇒ℰ-pred c d = ∀ᵒ[ V ] ∀ᵒ[ V′ ] (𝒱⟦ c ⟧ d V V′) →ᵒ (ℰ⟦ c ⟧ d V V′)

-- 𝒱⇒ℰ-aux : ∀{c : Prec}{d}{𝒫}
--    → 𝒫 ⊢ᵒ 𝒱⇒ℰ-pred c d
-- 𝒱⇒ℰ-aux {c}{d}{𝒫} =
--   let F₁ = λ V → ∀ᵒ[ V′ ] (𝒱⟦ c ⟧ d V V′) →ᵒ (ℰ⟦ c ⟧ d V V′) in
--   let F₂ = λ V V′ → (𝒱⟦ c ⟧ d V V′) →ᵒ (ℰ⟦ c ⟧ d V V′) in
--   lobᵒ (⊢ᵒ-∀-intro-new F₁ λ V → ⊢ᵒ-∀-intro-new (F₂ V) λ V′ → (→ᵒI
--     (⊢ᵒ-sucP Zᵒ λ 𝒱VV′sn →
--      let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′sn in
--      Goal 𝒱VV′sn v v′)))
--   where
--   Goal : ∀{V}{V′}{c}{d}{n}
--      → #(𝒱⟦ c ⟧ d V V′) (suc n)
--      → Value V → Value V′
--      → 𝒱⟦ c ⟧ d V V′ ∷ ▷ᵒ 𝒱⇒ℰ-pred c d ∷ 𝒫 ⊢ᵒ ℰ⟦ c ⟧ d V V′
--   Goal {.(_ ⟨ G !⟩)} {.(_ ⟨ G₁ !⟩)} {.★ , ★ , unk⊑} {d} 𝒱VV′ (v 〈 G 〉) (v′ 〈 G₁ 〉) = {!!}
--   Goal {V} {V′} {.★ , $ₜ ι , unk⊑} {d} 𝒱VV′ v v′ = {!!}
--   Goal {V} {V′} {.★ , A′ ⇒ A′₁ , unk⊑} {d} 𝒱VV′ v v′ = {!!}
--   Goal {V} {V′} {.($ₜ _) , .($ₜ _) , base⊑} {d} 𝒱VV′ v v′ = {!!}
--   Goal {V} {V′} {.(_ ⇒ _) , .(_ ⇒ _) , fun⊑ A⊑A′ A⊑A′₁} {d} 𝒱VV′ v v′ = {!!}

--   -- substᵒ (≡ᵒ-sym ℰ↪-stmt) (Λᵒ[ R ] (→ᵒI{P = V ⇓ᵒ R}
--   --   let 𝒫₁ = V ⇓ᵒ R ∷ 𝒱⟦ c ⟧ d V V′ ∷ ▷ᵒ 𝒱⇒ℰ-pred c d ∷ 𝒫 in
--   --   ⊢ᵒ-sucP Zᵒ λ V⇓Rsn →
--   --   ⊢ᵒ-sucP (Sᵒ Zᵒ) λ 𝒱VV′sn →
--   --   let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′sn in
--   --   {!!}))
--   -- Goal {V}{V′}{↩} v v′ = substᵒ (≡ᵒ-sym ℰ↩-stmt) {!!}


-- 𝒱⇒ℰ : ∀{c : Prec}{d}{𝒫}{V V′}
--    → 𝒫 ⊢ᵒ 𝒱⟦ c ⟧ d V V′
--      -------------------
--    → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ d V V′
-- 𝒱⇒ℰ {c}{↪}{𝒫}{V}{V′} ⊢𝒱VV′ = substᵒ (≡ᵒ-sym ℰ↪-stmt) {!!}

-- --   (G ,ᵒ (B ,ᵒ D))
-- --   where
-- --   G : 𝒫 ⊢ᵒ ∀↪⇓𝒱 c V V′
-- --   G = Λᵒ[ V₁ ] (→ᵒI{P = (Value V₁)ᵒ} (→ᵒI{P = (V ⇓ V₁)ᵒ}
-- --       (⊢ᵒ-sucP (Sᵒ (Sᵒ ⊢𝒱VV′)) (λ 𝒱VV′ →
-- --       (⊢ᵒ-sucP Zᵒ (λ V⇓V₁ →
-- --       let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′ in
-- --       let F = (λ V′₁ → (Value V′₁)ᵒ ×ᵒ (V′ ⇓ V′₁)ᵒ ×ᵒ 𝒱⟦ c ⟧ ↪ V₁ V′₁) in
-- --       (inj₁ᵒ (⊢ᵒ-∃-intro{P = F} V′ ((constᵒI v′)
-- --                 ,ᵒ ((constᵒI (⇓-value V′ v′)
-- --                 ,ᵒ subst (λ X → (V ⇓ V₁)ᵒ ∷ (Value V₁)ᵒ ∷ 𝒫 ⊢ᵒ 𝒱⟦ c ⟧ ↪ X V′)
-- --                          (sym (⇓-value-eq v V⇓V₁))
-- --                          (Sᵒ (Sᵒ ⊢𝒱VV′)))))))
-- --       ))))))
-- --   B : 𝒫 ⊢ᵒ (V ⇓ blame)ᵒ →ᵒ (V′ ⇓ blame)ᵒ
-- --   B = →ᵒI{P = (V ⇓ blame)ᵒ} (⊢ᵒ-sucP Zᵒ λ V⇓ →
-- --       (⊢ᵒ-sucP (⊢ᵒ-weaken ⊢𝒱VV′) (λ 𝒱VV′ →
-- --       let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′ in
-- --       let blame=V = ⇓-value-eq v V⇓ in
-- --       ⊥-elim (blame-not-value (subst (λ X → Value X) (sym blame=V) v) refl))))

-- --   D : 𝒫 ⊢ᵒ (⇑ᵒ V) →ᵒ (⇑ᵒ V′) ⊎ᵒ (V′ ⇓ blame)ᵒ
-- --   D : 𝒫 ⊢ᵒ (⇑ᵒ V) →ᵒ (⇑ᵒ V′) ⊎ᵒ (V′ ⇓ blame)ᵒ

-- --   D∀ : 𝒫 ⊢ᵒ Λᵒ[ V ] (⇑ᵒ V) →ᵒ (⇑ᵒ V′) ⊎ᵒ (V′ ⇓ blame)ᵒ
-- --   D∀ = lobᵒ (→ᵒI{P = ⇑ᵒ V} (⊢ᵒ-sucP Zᵒ λ V⇑ →
-- --         {!!}
-- --       ))
-- --       where
-- --       Goal : ∀{V}{n} → ⇑ V (suc n) → Value V 
-- --         → ⇑ᵒ V ∷ (▷ᵒ (⇑ᵒ V →ᵒ ⇑ᵒ V′ ⊎ᵒ (V′ ⇓ blame) ᵒ)) ∷ 𝒫
-- --           ⊢ᵒ (⇑ᵒ V′) ⊎ᵒ (V′ ⇓ blame)ᵒ
-- --       Goal{V ⟨ G !⟩}{n} (inj⇑ ⇑Vn) (v 〈 _ 〉) = {!!}
-- -- {-  
-- --       →ᵒI{P = (V ⇑)ᵒ} (⊢ᵒ-sucP Zᵒ λ V⇑ →
-- --       (⊢ᵒ-sucP (⊢ᵒ-weaken ⊢𝒱VV′) (λ 𝒱VV′ →
-- --       let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′ in
-- --       ⊥-elim (values-dont-diverge v V⇑))))
-- -- -}      

-- 𝒱⇒ℰ {c}{↩}{𝒫}{V}{V′} ⊢𝒱VV′ = substᵒ (≡ᵒ-sym ℰ↩-stmt) {!!}

-- --   where
-- --   G : 𝒫 ⊢ᵒ ∀↩⇓𝒱 c V V′
-- --   G = Λᵒ[ V′₁ ] →ᵒI{P = (Value V′₁)ᵒ} (→ᵒI{P = (V′ ⇓ V′₁)ᵒ}
-- --       (⊢ᵒ-sucP (Sᵒ (Sᵒ ⊢𝒱VV′)) (λ 𝒱VV′ →
-- --       (⊢ᵒ-sucP Zᵒ (λ V′⇓V′₁ →
-- --       let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′ in
-- --       let xx = subst (λ X → (V′ ⇓ V′₁)ᵒ ∷ (Value V′₁)ᵒ ∷ 𝒫 ⊢ᵒ 𝒱⟦ c ⟧ ↩ V X)
-- --                          (sym (⇓-value-eq v′ V′⇓V′₁))
-- --                          (Sᵒ (Sᵒ ⊢𝒱VV′)) in
-- --       let F = (λ V₁ → (Value V₁)ᵒ ×ᵒ (V ⇓ V₁)ᵒ ×ᵒ 𝒱⟦ c ⟧ ↩ V₁ V′₁) in
-- --       (⊢ᵒ-∃-intro{P = F} V (constᵒI v ,ᵒ (constᵒI (⇓-value V v) ,ᵒ xx)))
-- --       )))))

-- --   D : 𝒫 ⊢ᵒ (⇑ᵒ V′) →ᵒ (⇑ᵒ V)
-- --   D = {!!}
-- --   {-
-- --       →ᵒI{P = (V′ ⇑)ᵒ} (⊢ᵒ-sucP Zᵒ λ V′⇑ →
-- --       (⊢ᵒ-sucP (⊢ᵒ-weaken ⊢𝒱VV′) (λ 𝒱VV′ →
-- --       let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′ in
-- --       ⊥-elim (values-dont-diverge v′ V′⇑))))
-- --       -}

-- -- {- Blame is more precise than any term -}

-- -- ℰ-blame : ∀{𝒫}{c}{d}{M} → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ d M blame
-- -- ℰ-blame {𝒫} {c} {↪} {M} = substᵒ (≡ᵒ-sym ℰ↪-stmt) (G ,ᵒ (B ,ᵒ D))
-- --   where
-- --   G : 𝒫 ⊢ᵒ ∀↪⇓𝒱 c M blame
-- --   G = Λᵒ[ V₁ ] (→ᵒI{P = (Value V₁)ᵒ} (→ᵒI{P = (M ⇓ V₁)ᵒ}
-- --                  (inj₂ᵒ (constᵒI blame⇓))))

-- --   B : 𝒫 ⊢ᵒ (M ⇓ blame)ᵒ →ᵒ (blame ⇓ blame)ᵒ
-- --   B = →ᵒI{P = (M ⇓ blame)ᵒ} (constᵒI blame⇓)

-- --   D : 𝒫 ⊢ᵒ (⇑ᵒ M) →ᵒ (⇑ᵒ blame) ⊎ᵒ (blame ⇓ blame)ᵒ
-- --   D = →ᵒI{P = (⇑ᵒ M)} (inj₂ᵒ (constᵒI blame⇓))

-- -- ℰ-blame {𝒫} {c} {↩} {M} = substᵒ (≡ᵒ-sym ℰ↩-stmt) (G ,ᵒ D)
-- --   where
-- --   G : 𝒫 ⊢ᵒ ∀↩⇓𝒱 c M blame
-- --   G = Λᵒ[ V′₁ ] →ᵒI{P = (Value V′₁)ᵒ} (→ᵒI{P = (blame ⇓ V′₁)ᵒ}
-- --       (⊢ᵒ-sucP Zᵒ λ blame⇓V′₁ →
-- --       (⊢ᵒ-sucP (Sᵒ Zᵒ) λ v′₁ →
-- --       let V′₁=blame = ⇓-determ blame⇓V′₁ blame⇓ in
-- --       ⊥-elim (blame-not-value v′₁ V′₁=blame))))

-- --   D : 𝒫 ⊢ᵒ (⇑ᵒ blame) →ᵒ (⇑ᵒ M)
-- --   D = {!!}
-- --   {-
-- --     →ᵒI{P = (blame ⇑)ᵒ} (⊢ᵒ-sucP Zᵒ λ blame⇑ →
-- --     ⊥-elim (blame-doesnt-diverge blame⇑))
-- -- -}

-- -- compatible-nat : ∀{Γ}{n : ℕ}{d}
-- --    → Γ ∣ d ⊨ $ (Num n) ⊑ $ (Num n) ⦂ ($ₜ ′ℕ , $ₜ ′ℕ , base⊑)
-- -- compatible-nat {Γ}{n} γ γ′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))

-- -- compatible-bool : ∀{Γ}{b : 𝔹}{d}
-- --    → Γ ∣ d ⊨ $ (Bool b) ⊑ $ (Bool b) ⦂ ($ₜ ′𝔹 , $ₜ ′𝔹 , base⊑)
-- -- compatible-bool {Γ}{b} γ γ′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))

-- -- compatible-blame : ∀{Γ}{A}{M}{d}
-- --    → map proj₁ Γ ⊢ M ⦂ A
-- --      -------------------------------
-- --    → Γ ∣ d ⊨ M ⊑ blame ⦂ (A , A , Refl⊑)
-- -- compatible-blame ⊢M γ γ′ = ℰ-blame

-- -- lookup-𝓖 : (Γ : List Prec) → (d : Dir) → (γ γ′ : Subst)
-- --   → ∀ {A}{A′}{A⊑A′}{y} → Γ ∋ y ⦂ (A , A′ , A⊑A′)
-- --   → 𝓖⟦ Γ ⟧ d γ γ′ ⊢ᵒ 𝒱⟦ (A , A′ , A⊑A′) ⟧ d (γ y) (γ′ y)
-- -- lookup-𝓖 (.(A , A′ , A⊑A′) ∷ Γ) d γ γ′ {A} {A′} {A⊑A′} {zero} refl = Zᵒ
-- -- lookup-𝓖 (B ∷ Γ) d γ γ′ {A} {A′} {A⊑A′} {suc y} ∋y =
-- --    Sᵒ (lookup-𝓖 Γ d (λ x → γ (suc x)) (λ x → γ′ (suc x)) ∋y)

-- -- compatibility-var : ∀ {Γ d A A′ A⊑A′ x}
-- --   → Γ ∋ x ⦂ (A , A′ , A⊑A′)
-- --     -------------------------------
-- --   → Γ ∣ d ⊨ ` x ⊑ ` x ⦂ (A , A′ , A⊑A′)
-- -- compatibility-var {Γ}{d}{A}{A′}{A⊑A′}{x} ∋x γ γ′
-- --     rewrite sub-var γ x | sub-var γ′ x = 𝒱⇒ℰ (lookup-𝓖 Γ d γ γ′ ∋x)

-- -- compatible-lambda : ∀{Γ : List Prec}{dir}{A}{B}{C}{D}{N N′ : Term}
-- --      {c : A ⊑ C}{d : B ⊑ D}
-- --    → ((A , C , c) ∷ Γ) ∣ dir ⊨ N ⊑ N′ ⦂ (B , D , d)
-- --      ------------------------------------------------
-- --    → Γ ∣ dir ⊨ (ƛ N) ⊑ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
-- -- compatible-lambda{Γ}{dir}{A}{B}{C}{D}{N}{N′}{c}{d} ⊨N⊑N′ γ γ′ = ⊢ℰλNλN′
-- --  where
-- --  ⊢ℰλNλN′ : 𝓖⟦ Γ ⟧ dir γ γ′ ⊢ᵒ ℰ⟦ A ⇒ B , C ⇒ D , fun⊑ c d ⟧ dir (⟪ γ ⟫ (ƛ N))
-- --                                                          (⟪ γ′ ⟫ (ƛ N′))
-- --  ⊢ℰλNλN′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI 𝓔N[W]N′[W′]))
-- --   where
-- --   𝓔N[W]N′[W′] : ∀{W W′} → 𝒱⟦ A , C , c ⟧ dir W W′ ∷ 𝓖⟦ Γ ⟧ dir γ γ′
-- --        ⊢ᵒ  ℰ⟦ B , D , d ⟧ dir ((⟪ ext γ ⟫ N) [ W ]) ((⟪ ext γ′ ⟫ N′) [ W′ ])
-- --   𝓔N[W]N′[W′] {W}{W′} = appᵒ (Sᵒ (→ᵒI (⊨N⊑N′ (W • γ) (W′ • γ′)))) Zᵒ

-- -- ℰ↪⇓-elim : ∀{𝒫}{A}{A′}{c : A ⊑ A′}{M}{M′}{V}{R}
-- --    → 𝒫 ⊢ᵒ ℰ⟦ A , A′ , c ⟧ ↪ M M′
-- --    → M ⇓ V
-- --    → Value V
-- --    → (∀ V′ → (M′ ⇓ V′) → (Value V′) → 𝒱⟦ (A , A′ , c) ⟧ ↪ V V′ ∷ 𝒫 ⊢ᵒ R)
-- --    → (M′ ⇓ blame → 𝒫 ⊢ᵒ R)
-- --    → 𝒫 ⊢ᵒ R
-- -- ℰ↪⇓-elim {𝒫}{A}{A′}{c}{M}{M′}{V}{V′} ⊢ℰMM′ M⇓V v cont cont2 =
-- --   let X : 𝒫 ⊢ᵒ (∃ᵒ[ V′ ] v′×⇓×𝒱 V (A , A′ , c) M′ V′) ⊎ᵒ (M′ ⇓ blame)ᵒ 
-- --       X = (appᵒ (appᵒ (instᵒ{P = ↪⇓𝒱 (A , A′ , c) M M′}
-- --                  (proj₁ᵒ (substᵒ ℰ↪-stmt ⊢ℰMM′))
-- --                       V) (constᵒI v)) (constᵒI M⇓V)) in
-- --   caseᵒ X
-- --   (⊢ᵒ-∃-elim-L (v′×⇓×𝒱 V (A , A′ , c) M′) λ V′ →
-- --    ×-elim-L (⊢ᵒ-swap (×-elim-L (constᵒE-L (λ M′⇓V′ →
-- --       ⊢ᵒ-swap (constᵒE-L (cont V′ M′⇓V′)))))))
-- --   (constᵒE Zᵒ λ M′⇓blame → Sᵒ (cont2 M′⇓blame))

-- -- ℰ↪⇓blame-elim : ∀{𝒫}{A}{A′}{c : A ⊑ A′}{M}{M′}{R}
-- --    → 𝒫 ⊢ᵒ ℰ⟦ A , A′ , c ⟧ ↪ M M′
-- --    → M ⇓ blame
-- --    → (M′ ⇓ blame → 𝒫 ⊢ᵒ R)
-- --    → 𝒫 ⊢ᵒ R
-- -- ℰ↪⇓blame-elim {𝒫}{A}{A′}{c}{M}{M′} ⊢ℰMM′ M⇓blame cont = 
-- --   let X = (appᵒ (proj₁ᵒ (proj₂ᵒ (substᵒ ℰ↪-stmt ⊢ℰMM′)))
-- --                  (constᵒI M⇓blame)) in
-- --   constᵒE X λ M′⇓blame → cont M′⇓blame

-- -- compatible-app : ∀{Γ}{dir}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
-- --    → Γ ∣ dir ⊨ L ⊑ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d)
-- --    → Γ ∣ dir ⊨ M ⊑ M′ ⦂ (A , A′ , c)
-- --      ----------------------------------
-- --    → Γ ∣ dir ⊨ L · M ⊑ L′ · M′ ⦂ (B , B′ , d)
-- -- compatible-app {Γ}{↪}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′}
-- --  ⊨L⊑L′ ⊨M⊑M′ γ γ′ = substᵒ (≡ᵒ-sym ℰ↪-stmt) (Rd ,ᵒ (Bl ,ᵒ {!!}))
-- --  where
-- --  Rd : 𝓖⟦ Γ ⟧ ↪ γ γ′ ⊢ᵒ ∀↪⇓𝒱 (B , B′ , d) (⟪ γ ⟫ (L · M)) (⟪ γ′ ⟫ (L′ · M′))
-- --  Rd = Λᵒ[ V ] (→ᵒI (→ᵒI (constᵒE-L λ LM⇓V → (constᵒE-L λ v → G V LM⇓V v))))
-- --    where
-- --    G : ∀ V
-- --       → ⟪ γ ⟫ (L · M) ⇓ V
-- --       → Value V
-- --       → 𝓖⟦ Γ ⟧ ↪ γ γ′ ⊢ᵒ
-- --            ((∃ᵒ[ V′ ] v′×⇓×𝒱 V (B , B′ , d) (⟪ γ′ ⟫ (L′ · M′)) V′)
-- --             ⊎ᵒ ((⟪ γ′ ⟫ (L′ · M′)) ⇓ blame)ᵒ)
-- --    G V (app⇓{N = N}{W = W} L⇓λN M⇓W w NW⇓V) v =
-- --      ℰ↪⇓-elim (⊨L⊑L′ γ γ′) L⇓λN (ƛ̬ N)
-- --      (λ V′ L′⇓V′ v′ →
-- --         𝒱-fun-elim Zᵒ λ {N₁ N′ refl refl body →
-- --         ℰ↪⇓-elim (Sᵒ (⊨M⊑M′ γ γ′)) M⇓W w
-- --         (λ W′ M′⇓W′ w′ →
-- --           ℰ↪⇓-elim (appᵒ (Sᵒ (body W W′)) Zᵒ) NW⇓V v
-- --           (λ V′ NW′⇓V′ v′ → 
-- --             inj₁ᵒ (⊢ᵒ-∃-intro-new
-- --                     (λ V′ → v′×⇓×𝒱 V (B , B′ , d) (⟪ γ′ ⟫ (L′ · M′)) V′) V′
-- --                     (constᵒI v′ ,ᵒ
-- --                       (constᵒI (app⇓ L′⇓V′ M′⇓W′ w′ NW′⇓V′) ,ᵒ Zᵒ))))
-- --           (λ NW′⇓blame → inj₂ᵒ (constᵒI (app⇓ L′⇓V′ M′⇓W′ w′ NW′⇓blame))))
-- --         (λ M′⇓blame → inj₂ᵒ (constᵒI (app⇓-blame-R L′⇓V′ v′ M′⇓blame)))})
-- --      (λ L′⇓blame → inj₂ᵒ (constᵒI (app⇓-blame-L L′⇓blame)))
 
-- --  Bl : 𝓖⟦ Γ ⟧ ↪ γ γ′ ⊢ᵒ ((⟪ γ ⟫ (L · M)) ⇓ blame)ᵒ
-- --                      →ᵒ ((⟪ γ′ ⟫ (L′ · M′)) ⇓ blame)ᵒ
-- --  Bl = →ᵒI (⊢ᵒ-sucP Zᵒ (λ LM⇓blame → G LM⇓blame))
-- --   where
-- --   𝒫₁ = ((⟪ γ ⟫ (L · M)) ⇓ blame)ᵒ ∷ 𝓖⟦ Γ ⟧ ↪ γ γ′
-- --   G : ⟪ γ ⟫ (L · M) ⇓ blame
-- --      → 𝒫₁ ⊢ᵒ ((⟪ γ′ ⟫ (L′ · M′)) ⇓ blame)ᵒ
-- --   G LM⇓blame
-- --       with LM⇓blame
-- --   ... | app⇓{N = N}{W} L⇓λN M⇓W w NW⇓blame =
-- --       ℰ↪⇓-elim (Sᵒ (⊨L⊑L′ γ γ′)) L⇓λN (ƛ̬ N)
-- --       (λ V′ L′⇓V′ v′ →
-- --         𝒱-fun-elim Zᵒ λ {N₁ N′ refl refl body →
-- --         ℰ↪⇓-elim (Sᵒ (Sᵒ (⊨M⊑M′ γ γ′))) M⇓W w
-- --         (λ W′ M′⇓W′ w′ →
-- --           ℰ↪⇓blame-elim (appᵒ (Sᵒ (body W W′)) Zᵒ) NW⇓blame
-- --           λ N′W′⇓blame →
-- --           constᵒI (app⇓ L′⇓V′ M′⇓W′ w′ N′W′⇓blame))
-- --         (λ M′⇓blame → constᵒI (app⇓-blame-R L′⇓V′ v′ M′⇓blame))
-- --         })
-- --       (λ L′⇓blame → constᵒI (app⇓-blame-L L′⇓blame))
-- --   ... | app⇓-blame-L L⇓blame =
-- --       let ⊢L′⇓blame = Sᵒ (appᵒ (proj₁ᵒ (proj₂ᵒ (substᵒ ℰ↪-stmt (⊨L⊑L′ γ γ′))))
-- --                                 (constᵒI L⇓blame)) in
-- --       ⊢ᵒ-sucP ⊢L′⇓blame λ L′⇓blame → constᵒI (app⇓-blame-L L′⇓blame)
-- --   ... | app⇓-blame-R{V = V} L⇓V v M⇓blame =
-- --       ℰ↪⇓-elim (Sᵒ (⊨L⊑L′ γ γ′)) L⇓V v
-- --       (λ V′ L′⇓V′ v′ →
-- --         ℰ↪⇓blame-elim (Sᵒ (Sᵒ (⊨M⊑M′ γ γ′))) M⇓blame λ M′⇓blame → 
-- --         constᵒI (app⇓-blame-R L′⇓V′ v′ M′⇓blame))
-- --       (λ L′⇓blame → constᵒI (app⇓-blame-L L′⇓blame))

-- --  Div : 𝓖⟦ Γ ⟧ ↪ γ γ′ ⊢ᵒ (⇑ᵒ (⟪ γ ⟫ (L · M)))
-- --                         →ᵒ (⇑ᵒ (⟪ γ′ ⟫ (L′ · M′)))
-- --  Div = {!!}
-- --    --→ᵒI (constᵒE-L (λ LM⇑ → constᵒI (D LM⇑)))
-- --    -- where
-- --    -- D : (⟪ γ ⟫ (L · M)) ⇑
-- --    --    → (⟪ γ′ ⟫ (L′ · M′)) ⇑
-- --    -- D LM⇑ zero = ⇑zero
-- --    -- D LM⇑ (suc k)
-- --    --     with LM⇑ (suc k)
-- --    -- ... | app⇑ L⇓λN M⇓W w NW⇑k = {!!}
-- --    -- ... | app⇑-L L⇑k =
-- --    --       {!!}
-- --    -- ... | app⇑-R L⇓λN M⇑k = {!!}

-- -- compatible-app {Γ}{↩}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′}
-- --     ⊨L⊑L′ ⊨M⊑M′ γ γ′ = {!!}
