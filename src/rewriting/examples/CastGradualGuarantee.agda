{-# OPTIONS --rewriting #-}
module rewriting.examples.CastGradualGuarantee where

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
open import rewriting.examples.CastDeterministic
open import rewriting.examples.StepIndexedLogic2

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Prec × Term × Term) ⊎ (Prec × Term × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

ℰˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A⊑B ⟧ M M′ = (inj₂ (A⊑B , M , M′)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A⊑B ⟧ V V′ = (inj₁ (A⊑B , V , V′)) ∈ zeroˢ

pre-𝒱 : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 (.★ , .★ , unk⊑unk) (V ⟨ G !⟩) (V′ ⟨ H !⟩)
    with G ≡ᵍ H
... | yes refl = let g = gnd⇒ty G in
                 (Value V)ˢ ×ˢ (Value V′)ˢ
                 ×ˢ (▷ˢ (𝒱ˢ⟦ (g , g , Refl⊑) ⟧ V V′))
... | no neq = ⊥ ˢ
pre-𝒱 (.★ , .A′ , unk⊑any{G}{A′} G⊑A′) (V ⟨ H !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                      ×ˢ ▷ˢ (𝒱ˢ⟦ (gnd⇒ty G , A′ , G⊑A′) ⟧ V V′)
... | no new = ⊥ ˢ
pre-𝒱 ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) = (c ≡ c′) ˢ
pre-𝒱 ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] ▷ˢ (𝒱ˢ⟦ (A , A′ , A⊑A′) ⟧ W W′)
                  →ˢ ▷ˢ (ℰˢ⟦ (B , B′ , B⊑B′) ⟧ (N [ W ]) (N′ [ W′ ])) 
pre-𝒱 (A , A′ , A⊑A′) V V′ = ⊥ ˢ

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

{- Right-to-left version -}
pre-ℰ : Prec → Term → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ c M M′ = 
    ((Value M′)ˢ ×ˢ (∃ˢ[ V ] (M —↠ V)ˢ ×ˢ (Value V)ˢ ×ˢ pre-𝒱 c V M′))
  ⊎ˢ (∃ˢ[ N′ ] (M′ —→ N′)ˢ ×ˢ ▷ˢ (ℰˢ⟦ c ⟧ M N′))
  ⊎ˢ (Blame M′)ˢ

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (c , V , V′)) = pre-𝒱 c V V′
pre-ℰ⊎𝒱 (inj₂ (c , M , M′)) = pre-ℰ c M M′

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X

𝒱⟦_⟧ : (c : Prec) → Term → Term → Setᵒ
𝒱⟦ c ⟧ V V′ = ℰ⊎𝒱 (inj₁ (c , V , V′))

ℰ⟦_⟧ : (c : Prec) → Term → Term → Setᵒ
ℰ⟦ c ⟧ M M′ = ℰ⊎𝒱 (inj₂ (c , M , M′))

preserve-L : Prec → Term → Term → Setᵒ
preserve-L c M M′ = (∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ c ⟧ N M′)))

preserve-R : Prec → Term → Term → Setᵒ
preserve-R c M M′ = (∀ᵒ[ N′ ] ((M′ —→ N′)ᵒ →ᵒ ▷ᵒ (ℰ⟦ c ⟧ M N′)))

ℰ-stmt : ∀{c}{M M′}
  → ℰ⟦ c ⟧ M M′ ≡ᵒ
        (((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ 𝒱⟦ c ⟧ V M′))
         ⊎ᵒ (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (ℰ⟦ c ⟧ M N′))
         ⊎ᵒ (Blame M′)ᵒ)
ℰ-stmt {c}{M}{M′} =
  let X₁ = inj₁ (c , M , M′) in
  let X₂ = inj₂ (c , M , M′) in
  ℰ⟦ c ⟧ M M′                                                 ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 X₂                                      ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₂ ⟩
  # (pre-ℰ⊎𝒱 X₂) (ℰ⊎𝒱 , ttᵖ)
                                  ⩦⟨ EQ ⟩
        (((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ 𝒱⟦ c ⟧ V M′))
         ⊎ᵒ (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (ℰ⟦ c ⟧ M N′))
         ⊎ᵒ (Blame M′)ᵒ)
  ∎
  where
  X₁ = λ V → (inj₁ (c , V , M′))
  X₂ = inj₂ (c , M , M′)
  EQ = cong-⊎ᵒ (cong-×ᵒ (≡ᵒ-refl refl) (cong-∃ (λ V → cong-×ᵒ (≡ᵒ-refl refl)
                   (cong-×ᵒ (≡ᵒ-refl refl)
                           (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (X₁ V)))))))
               (≡ᵒ-refl refl)

𝒱-dyn-dyn : ∀{G}{V}{V′}
  → 𝒱⟦ ★ , ★ , unk⊑unk ⟧ (V ⟨ G !⟩) (V′ ⟨ G !⟩)
    ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ
           ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V V′)
𝒱-dyn-dyn {G}{V}{V′} =
  𝒱⟦ ★ , ★ , unk⊑unk ⟧ (V ⟨ G !⟩) (V′ ⟨ G !⟩)
         ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 X₁
         ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₁ ⟩
  # (pre-ℰ⊎𝒱 X₁) (ℰ⊎𝒱 , ttᵖ)
         ⩦⟨ EQ ⟩
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
   → 𝒱⟦ ★ , A′ , unk⊑any{G} G⊑A′ ⟧ (V ⟨ G !⟩) V′
     ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V V′)
𝒱-dyn-any {G}{A′}{V}{V′} G⊑A′ =
  𝒱⟦ ★ , A′ , unk⊑any{G} G⊑A′ ⟧ (V ⟨ G !⟩) V′
                ⩦⟨ ≡ᵒ-refl refl ⟩
  ℰ⊎𝒱 (X₁ G A′ G⊑A′)
                ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 (X₁ G A′ G⊑A′) ⟩
  # (pre-ℰ⊎𝒱 (X₁ G A′ G⊑A′)) (ℰ⊎𝒱 , ttᵖ)
                ⩦⟨ EQ G⊑A′ ⟩
  (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V V′)
                ∎ 
  where
  X₁ = λ G A′ G⊑A′ → inj₁ ((★ , A′ , unk⊑any{G} G⊑A′) , (V ⟨ G !⟩) , V′)
  EQ : ∀{G}{A′}
     → (G⊑A′ : gnd⇒ty G ⊑ A′)
     → # (pre-ℰ⊎𝒱 (X₁ G A′ G⊑A′)) (ℰ⊎𝒱 , ttᵖ)
       ≡ᵒ (Value V)ᵒ ×ᵒ (Value V′)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V V′)
  EQ {G} {A′} G⊑A′
      with G ≡ᵍ G
  ... | yes refl = cong-×ᵒ (≡ᵒ-refl refl) (cong-×ᵒ (≡ᵒ-refl refl)
            (cong-▷ (≡ᵒ-refl refl)))
  ... | no neq = ⊥-elim (neq refl)

𝒱-base : ∀{ι}{c}{c′} → 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ ($ c) ($ c′) ≡ᵒ (c ≡ c′) ᵒ
𝒱-base{ι}{c}{c′} = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

𝒱-base-intro : ∀{𝒫}{ι}{c} → 𝒫 ⊢ᵒ 𝒱⟦ ($ₜ ι , $ₜ ι , base⊑) ⟧ ($ c) ($ c)
𝒱-base-intro{ι}{c} = substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl)

𝒱-fun : ∀{A B A′ B′}{A⊑A′ : A ⊑ A′}{B⊑B′ : B ⊑ B′}{N}{N′}
   → (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ (ƛ N) (ƛ N′))
      ≡ᵒ (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (𝒱⟦ A , A′ , A⊑A′ ⟧ W W′))
                         →ᵒ (▷ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ (N [ W ]) (N′ [ W′ ])))))
𝒱-fun {A}{B}{A′}{B′}{A⊑A′}{B⊑B′}{N}{N′} =
   let X = inj₁ ((A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′) , ƛ N , ƛ N′) in
   (𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ A⊑A′ B⊑B′ ⟧ (ƛ N) (ƛ N′))      ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                              ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                                 ⩦⟨ ≡ᵒ-refl refl ⟩
   (∀ᵒ[ W ] ∀ᵒ[ W′ ] ((▷ᵒ (𝒱⟦ A , A′ , A⊑A′ ⟧ W W′))
                      →ᵒ (▷ᵒ (ℰ⟦ B , B′ , B⊑B′ ⟧ (N [ W ]) (N′ [ W′ ])))))    ∎

𝒱-fun-elim : ∀{𝒫}{A}{B}{A′}{B′}{c : A ⊑ A′}{d : B ⊑ B′}{V}{V′}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
   → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀{W W′} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A , A′ , c ⟧ W W′))
                             →ᵒ (▷ᵒ (ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ]))))
             → 𝒫 ⊢ᵒ R)
     --------------------------------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-fun-elim {𝒫}{A}{B}{A′}{B′}{c}{d}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ { 𝒱VV′sn → G {V}{V′} 𝒱VV′sn ⊢𝒱VV′ cont }
  where
  G : ∀{V}{V′}{n}
     → # (𝒱⟦  A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
     → (∀ N N′ → V ≡ ƛ N → V′ ≡ ƛ N′ 
             → (∀{W W′} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A , A′ , c ⟧ W W′))
                             →ᵒ (▷ᵒ (ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ]))))
             → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G {ƛ N}{ƛ N′}{n} 𝒱VV′ ⊢𝒱VV′ cont = cont N N′ refl refl λ {W}{W′} →
     instᵒ (instᵒ (substᵒ 𝒱-fun ⊢𝒱VV′) W) W′ 

{- Relate Open Terms -}

𝓖⟦_⟧ : (Γ : List Prec) → Subst → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ σ′ = []
𝓖⟦ c ∷ Γ ⟧ σ σ′ = (𝒱⟦ c ⟧ (σ 0) (σ′ 0))
                     ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x)) (λ x → σ′ (suc x))

_⊨_⊑_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊨ M ⊑ M′ ⦂ c = ∀ (γ γ′ : Subst) → 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ℰ⟦ c ⟧ (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′)

{- Related values are syntactic values -}

𝒱⇒Value : ∀ {k} c M M′
   → # (𝒱⟦ c ⟧ M M′) (suc k)
     ------------------------
   → Value M × Value M′
𝒱⇒Value {k} (.★ , .★ , unk⊑unk) (V ⟨ G !⟩) (V′ ⟨ H !⟩) 𝒱MM′
    with G ≡ᵍ H
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
    with 𝒱MM′
... | v , v′ , _ = (v 〈 G 〉) , (v′ 〈 G 〉)
𝒱⇒Value {k} (.★ , .A′ , unk⊑any{G}{A′} G⊑A′) (V ⟨ H !⟩) V′ 𝒱MM′
    with  G ≡ᵍ H
... | no neq = ⊥-elim 𝒱MM′
... | yes refl
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
  substᵒ (≡ᵒ-sym ℰ-stmt) (inj₁ᵒ
  (⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ →
  let (v , v′) = 𝒱⇒Value c V V′ 𝒱VV′ in
  constᵒI v′ ,ᵒ
  ⊢ᵒ-∃-intro-new (λ X → (V —↠ X)ᵒ ×ᵒ (Value X)ᵒ ×ᵒ 𝒱⟦ c ⟧ X V′)
  V
  (constᵒI (V END) ,ᵒ (constᵒI v ,ᵒ ⊢𝒱VV′))))

{- ℰ-bind (Monadic Bind Lemma) -}

data PEFrame : Set where
  `_ : Frame → PEFrame
  □ : PEFrame

_⦉_⦊ : PEFrame → Term → Term
(` F) ⦉ M ⦊ = F ⟦ M ⟧
□ ⦉ M ⦊ = M

𝒱→ℰF : Prec → Prec → PEFrame → PEFrame → Term → Term → Setᵒ
𝒱→ℰF c d F F′ M M′ = ∀ᵒ[ V ] ∀ᵒ[ V′ ] (M —↠ V)ᵒ →ᵒ (M′ —↠ V′)ᵒ
                   →ᵒ 𝒱⟦ d ⟧ V V′ →ᵒ ℰ⟦ c ⟧ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)

𝒱→ℰF-expansion-L : ∀{𝒫}{c}{d}{F}{F′}{M}{M′}{N}
   → M —→ N
   → 𝒫 ⊢ᵒ 𝒱→ℰF c d F F′ M M′
     -------------------------
   → 𝒫 ⊢ᵒ 𝒱→ℰF c d F F′ N M′
𝒱→ℰF-expansion-L {𝒫}{c}{d}{F}{F′}{M}{M′}{N} M→N 𝒱→ℰF[MM′] =
  Λᵒ[ V ] Λᵒ[ V′ ]
  let 𝒱→ℰF[NM′] : 𝒱⟦ d ⟧ V V′ ∷ (M′ —↠ V′)ᵒ ∷ (N —↠ V)ᵒ ∷ 𝒫
               ⊢ᵒ ℰ⟦ c ⟧  (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)
      𝒱→ℰF[NM′] = ⊢ᵒ-sucP (Sᵒ Zᵒ) λ M′—↠V′ →
               ⊢ᵒ-sucP (Sᵒ (Sᵒ Zᵒ)) λ N—↠V →
               let M—↠V = constᵒI (M —→⟨ M→N ⟩ N—↠V) in
               let 𝒱→ℰF[MM′]VV′ = ⊢ᵒ-weaken (⊢ᵒ-weaken (⊢ᵒ-weaken
                                    (instᵒ (instᵒ 𝒱→ℰF[MM′] V) V′)))
               in appᵒ (appᵒ (appᵒ 𝒱→ℰF[MM′]VV′ M—↠V) (constᵒI M′—↠V′)) Zᵒ
  in →ᵒI (→ᵒI (→ᵒI 𝒱→ℰF[NM′]))

𝒱→ℰF-expansion-R : ∀{𝒫}{c}{d}{F}{F′}{M}{M′}{N′}
   → M′ —→ N′
   → 𝒫 ⊢ᵒ 𝒱→ℰF c d F F′ M M′
     -------------------------
   → 𝒫 ⊢ᵒ 𝒱→ℰF c d F F′ M N′
𝒱→ℰF-expansion-R {𝒫}{c}{d}{F}{F′}{M}{M′}{N′} M′→N′ 𝒱→ℰF[MM′] =
  Λᵒ[ V ] Λᵒ[ V′ ]
  let 𝒱→ℰF[MN′] : 𝒱⟦ d ⟧ V V′ ∷ (N′ —↠ V′)ᵒ ∷ (M —↠ V)ᵒ ∷ 𝒫
               ⊢ᵒ ℰ⟦ c ⟧  (F ⦉ V ⦊) (F′ ⦉ V′ ⦊)
      𝒱→ℰF[MN′] = ⊢ᵒ-sucP (Sᵒ Zᵒ) λ N′—↠V′ →
               ⊢ᵒ-sucP (Sᵒ (Sᵒ Zᵒ)) λ M—↠V →
               let M′—↠V′ = constᵒI (M′ —→⟨ M′→N′ ⟩ N′—↠V′) in
               let 𝒱→ℰF[MM′]VV′ = ⊢ᵒ-weaken (⊢ᵒ-weaken (⊢ᵒ-weaken
                                    (instᵒ (instᵒ 𝒱→ℰF[MM′] V) V′)))
               in appᵒ (appᵒ (appᵒ 𝒱→ℰF[MM′]VV′ (constᵒI M—↠V)) M′—↠V′) Zᵒ
  in →ᵒI (→ᵒI (→ᵒI 𝒱→ℰF[MN′]))


ℰ-blame : ∀{𝒫}{c}{M} → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ M blame
ℰ-blame {𝒫}{c}{M} = substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₂ᵒ (constᵒI isBlame)))

ξ′ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : PEFrame)
    → M′ ≡ F ⦉ M ⦊
    → N′ ≡ F ⦉ N ⦊
    → M —→ N
      --------
    → M′ —→ N′
ξ′ (` F) refl refl M→N = ξ F M→N
ξ′ □ refl refl M→N = M→N

ξ′-blame : ∀ {M′ : Term}
   → (F : PEFrame)
   → M′ ≡ F ⦉ blame ⦊
     ------------------------
   → M′ —→ blame ⊎ M′ ≡ blame
ξ′-blame (` F) refl = inj₁ (ξ-blame F)
ξ′-blame □ refl = inj₂ refl

frame-inv3 : ∀{L N : Term}{F : PEFrame}
   → reducible L
   → F ⦉ L ⦊ —→ N
   → ∃[ L′ ] ((L —→ L′) × (N ≡ F ⦉ L′ ⦊))
frame-inv3 {L}{N}{□} rL FL→N = _ , (FL→N , refl)
frame-inv3 {L}{N}{` F} rL FL→N = frame-inv2 rL FL→N

blame-frame2 : ∀{F}{N}
   → (F ⦉ blame ⦊) —→ N
   → N ≡ blame
blame-frame2 {□}{N} Fb→N = ⊥-elim (blame-irreducible Fb→N)
blame-frame2 {` F}{N} Fb→N = blame-frame Fb→N

ℰ-bind-M : Prec → Prec → PEFrame → PEFrame → Term → Term → Setᵒ
ℰ-bind-M c d F F′ M M′ = ℰ⟦ d ⟧ M M′ →ᵒ 𝒱→ℰF c d F F′ M M′
    →ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)

ℰ-bind-prop : Prec → Prec → PEFrame → PEFrame → Setᵒ
ℰ-bind-prop c d F F′ = ∀ᵒ[ M ] ∀ᵒ[ M′ ] ℰ-bind-M c d F F′ M M′

ℰ-bind-aux : ∀{𝒫}{c}{d}{F}{F′} → 𝒫 ⊢ᵒ ℰ-bind-prop c d F F′
ℰ-bind-aux {𝒫}{c}{d}{F}{F′} = lobᵒ Goal
 where     
 Goal : ▷ᵒ ℰ-bind-prop c d F F′ ∷ 𝒫 ⊢ᵒ ℰ-bind-prop c d F F′
 Goal = Λᵒ[ M ] Λᵒ[ M′ ] →ᵒI (→ᵒI Goal′)
  where
  Goal′ : ∀{M}{M′}
     → (𝒱→ℰF c d F F′ M M′) ∷ ℰ⟦ d ⟧ M M′ ∷ ▷ᵒ ℰ-bind-prop c d F F′ ∷ 𝒫
        ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
  Goal′{M}{M′} = case3ᵒ (substᵒ ℰ-stmt (Sᵒ Zᵒ)) Catchup Eval (Mblame{F′ = F′})
     --Mval MredL MredR (Mblame{F′ = F′})
   where
   𝒫′ = (𝒱→ℰF c d F F′ M M′) ∷ ℰ⟦ d ⟧ M M′ ∷ ▷ᵒ ℰ-bind-prop c d F F′ ∷ 𝒫

   Catchup : ((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ 𝒱⟦ d ⟧ V M′))
             ∷ 𝒫′ ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
   Catchup = substᵒ (≡ᵒ-sym ℰ-stmt) {!!}

   Eval : (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (ℰ⟦ d ⟧ M N′))
             ∷ 𝒫′ ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
   Eval = {!!}

{-
   Mval : 𝒱⟦ d ⟧ M M′ ∷ 𝒫′ ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
   Mval =
     let Cont = λ V → ∀ᵒ[ V′ ] (M —↠ V)ᵒ →ᵒ (M′ —↠ V′)ᵒ
                   →ᵒ 𝒱⟦ d ⟧ V V′ →ᵒ ℰ⟦ c ⟧ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊) in
     let Cont′ = λ V′ → (M —↠ M)ᵒ →ᵒ (M′ —↠ V′)ᵒ
                   →ᵒ 𝒱⟦ d ⟧ M V′ →ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ V′ ⦊) in
     appᵒ (appᵒ (appᵒ (instᵒ{P = Cont′} (instᵒ{P = Cont} (Sᵒ Zᵒ) M) M′)
                      (constᵒI (M END)))
                (constᵒI (M′ END)))
          Zᵒ 

   MredL : reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′ ⊢ᵒ ℰ⟦ c ⟧(F ⦉ M ⦊)(F′ ⦉ M′ ⦊)
   MredL = substᵒ (≡ᵒ-sym ℰ-stmt) {!!} -- (inj₂ᵒ (inj₁ᵒ (redFM ,ᵒ presFM)))
    where
    redFM : reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′ ⊢ᵒ reducible (F ⦉ M ⦊) ᵒ
    redFM = constᵒE (proj₁ᵒ Zᵒ) λ {(N , M→N) → constᵒI (F ⦉ N ⦊ , ξ′ F refl refl M→N)}
    
    presFM : reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′
              ⊢ᵒ preserve-L c (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
    presFM = Λᵒ[ N ] →ᵒI ▷ℰFM′
     where
     ▷ℰFM′ : ∀{N} → (F ⦉ M ⦊ —→ N)ᵒ ∷ reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′
             ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ N (F′ ⦉ M′ ⦊))
     ▷ℰFM′ {N} =
       constᵒE Zᵒ λ FM→N →
       constᵒE (proj₁ᵒ (Sᵒ Zᵒ)) λ rM →
       let 𝒫″ = (F ⦉ M ⦊ —→ N)ᵒ ∷ reducible M ᵒ ×ᵒ preserve-L d M M′ ∷ 𝒫′ in
       let finv = frame-inv3{F = F} rM FM→N in
       let N₁ = proj₁ finv in
       let M→N₁ = proj₁ (proj₂ finv) in
       let N≡ = proj₂ (proj₂ finv) in
       {-
               M   —→  N₁
           F ⟦ M ⟧ —→  F ⟦ N₁ ⟧  ≡  N
       -}
       let ▷ℰN₁M′ : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ d ⟧ N₁ M′)
           ▷ℰN₁M′ = appᵒ (instᵒ{P = λ N → ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ d ⟧ N M′))}
                              (proj₂ᵒ{𝒫″} (Sᵒ Zᵒ)) N₁) (constᵒI M→N₁) in
       let ▷M′→V→𝒱→ℰF : 𝒫″ ⊢ᵒ ▷ᵒ (𝒱→ℰF c d F F′ N₁ M′)
           ▷M′→V→𝒱→ℰF = monoᵒ (𝒱→ℰF-expansion-L{𝒫″}{c}{d}{F}{F′} M→N₁
                                  (Sᵒ (Sᵒ Zᵒ))) in
       let IH : 𝒫″ ⊢ᵒ ▷ᵒ ℰ-bind-prop c d F F′
           IH = Sᵒ (Sᵒ (Sᵒ (Sᵒ Zᵒ))) in
       let IH[N₁,M′] : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ-bind-M c d F F′ N₁ M′)
           IH[N₁,M′] =
             let F₁ = λ M → (▷ᵒ (∀ᵒ[ M′ ] ℰ-bind-M c d F F′ M M′)) in
             instᵒ (▷∀ (instᵒ{P = F₁} (▷∀ IH) N₁)) M′ in
       let ▷ℰFN₁FM′ : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ (F ⦉ N₁ ⦊) (F′ ⦉ M′ ⦊))
           ▷ℰFN₁FM′ = appᵒ (▷→ (appᵒ (▷→ IH[N₁,M′]) ▷ℰN₁M′)) ▷M′→V→𝒱→ℰF  in
       subst (λ N → 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ N (F′ ⦉ M′ ⦊))) (sym N≡) ▷ℰFN₁FM′
     
   MredR : reducible M′ ᵒ ×ᵒ preserve-R d M M′ ∷ 𝒫′
             ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
   MredR = substᵒ (≡ᵒ-sym ℰ-stmt) {!!}
     -- (inj₂ᵒ (inj₂ᵒ (inj₁ᵒ (redFM′ ,ᵒ presFM′))))
    where
    redFM′ : reducible M′ ᵒ ×ᵒ preserve-R d M M′ ∷ 𝒫′ ⊢ᵒ reducible (F′ ⦉ M′ ⦊) ᵒ
    redFM′ = constᵒE (proj₁ᵒ Zᵒ) λ {(N , M′→N) → constᵒI (F′ ⦉ N ⦊ , ξ′ F′ refl refl M′→N)}

    presFM′ : reducible M′ ᵒ ×ᵒ preserve-R d M M′ ∷ 𝒫′
              ⊢ᵒ preserve-R c (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
    presFM′ = Λᵒ[ N′ ] →ᵒI ▷ℰFMN′
     where
     ▷ℰFMN′ : ∀{N′} → (F′ ⦉ M′ ⦊ —→ N′)ᵒ ∷ reducible M′ ᵒ ×ᵒ preserve-R d M M′
                      ∷ 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ (F ⦉ M ⦊) N′)
     ▷ℰFMN′ {N′} =
       constᵒE Zᵒ λ FM′→N′ →
       constᵒE (proj₁ᵒ (Sᵒ Zᵒ)) λ rM′ →
       let 𝒫″ =(F′ ⦉ M′ ⦊ —→ N′)ᵒ ∷ reducible M′ ᵒ ×ᵒ preserve-R d M M′ ∷ 𝒫′ in
       let finv = frame-inv3{F = F′} rM′ FM′→N′ in
       let N₁ = proj₁ finv in
       let M′→N₁ = proj₁ (proj₂ finv) in
       let N′≡F[N₁] = proj₂ (proj₂ finv) in
       let ▷ℰMN₁ : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ d ⟧ M N₁)
           ▷ℰMN₁ = appᵒ (instᵒ{P = λ N′ → ((M′ —→ N′)ᵒ →ᵒ ▷ᵒ (ℰ⟦ d ⟧ M N′))}
                              (proj₂ᵒ{𝒫″} (Sᵒ Zᵒ)) N₁) (constᵒI M′→N₁) in
       let ▷𝒱→ℰF[M,N₁] : 𝒫″ ⊢ᵒ ▷ᵒ (𝒱→ℰF c d F F′ M N₁)
           ▷𝒱→ℰF[M,N₁] = monoᵒ (𝒱→ℰF-expansion-R{𝒫″}{c}{d}{F}{F′} M′→N₁
                                  (Sᵒ (Sᵒ Zᵒ))) in
       let IH : 𝒫″ ⊢ᵒ ▷ᵒ ℰ-bind-prop c d F F′
           IH = Sᵒ (Sᵒ (Sᵒ (Sᵒ Zᵒ))) in
       let IH[M,N₁] : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ-bind-M c d F F′ M N₁)
           IH[M,N₁] =
             let F₁ = λ M → (▷ᵒ (∀ᵒ[ M′ ] ℰ-bind-M c d F F′ M M′)) in
             let F₂ = λ M′ → ▷ᵒ ℰ-bind-M c d F F′ M M′ in
             instᵒ{P = F₂} (▷∀ (instᵒ{P = F₁} (▷∀ IH) M)) N₁ in
       let ▷ℰFMFN₁ : 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ N₁ ⦊))
           ▷ℰFMFN₁ = appᵒ (▷→ (appᵒ (▷→ IH[M,N₁]) ▷ℰMN₁)) ▷𝒱→ℰF[M,N₁] in
       subst(λ N′ → 𝒫″ ⊢ᵒ ▷ᵒ (ℰ⟦ c ⟧ (F ⦉ M ⦊) N′)) (sym N′≡F[N₁]) ▷ℰFMFN₁ 
-}
   Mblame : ∀{F′} → Blame M′ ᵒ ∷ 𝒫′ ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
   Mblame {F′}
      with F′
   ... | □ = substᵒ (≡ᵒ-sym ℰ-stmt) {!!} -- (inj₂ᵒ (inj₂ᵒ (inj₂ᵒ Zᵒ)))
   ... | ` F′ =
    substᵒ (≡ᵒ-sym ℰ-stmt) {!!}
      -- (inj₂ᵒ (inj₂ᵒ (inj₁ᵒ
      --                      (constᵒE Zᵒ λ {isBlame → redFblame ,ᵒ presFblame}))))
    where
    redFblame : (Blame blame)ᵒ ∷ 𝒫′ ⊢ᵒ (reducible (F′ ⟦ blame ⟧))ᵒ
    redFblame =
     constᵒE Zᵒ λ {isBlame → constᵒI (_ , (ξ-blame F′)) }
    
    presFblame : (Blame blame)ᵒ ∷ 𝒫′ ⊢ᵒ preserve-R c (F ⦉ M ⦊) (F′ ⟦ blame ⟧)
    presFblame = Λᵒ[ N′ ] →ᵒI (constᵒE Zᵒ λ Fb→N′ →
      let eq = blame-frame{F = F′} Fb→N′ in
      let 𝒫″ = (F′ ⟦ blame ⟧ —→ N′)ᵒ ∷ (Blame blame)ᵒ ∷ 𝒫′ in
      subst (λ N′ → 𝒫″ ⊢ᵒ ▷ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) N′) (sym eq) (monoᵒ ℰ-blame))

ℰ-bind : ∀{𝒫}{c d : Prec}{F}{F′}{M}{M′}
   → 𝒫 ⊢ᵒ ℰ⟦ d ⟧ M M′ 
   → 𝒫 ⊢ᵒ (∀ᵒ[ V ] ∀ᵒ[ V′ ] (M —↠ V)ᵒ →ᵒ (M′ —↠ V′)ᵒ
              →ᵒ 𝒱⟦ d ⟧ V V′ →ᵒ ℰ⟦ c ⟧ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊))
     ----------------------------------------------------------
   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)
ℰ-bind {𝒫}{c}{d}{F}{F′}{M}{M′} ⊢ℰMM′ ⊢𝒱V→ℰFV =
  let F₁ = λ M → ∀ᵒ[ M′ ] ℰ-bind-M c d F F′ M M′ in
  let F₂ = λ M′ → ℰ-bind-M c d F F′ M M′ in
  let xx = instᵒ{P = F₂} (instᵒ{𝒫}{P = F₁} (ℰ-bind-aux{F = F}{F′}) M) M′ in
  appᵒ (appᵒ xx ⊢ℰMM′) ⊢𝒱V→ℰFV

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
     ------------------------------------------------
   → Γ ⊨ (ƛ N) ⊑ (ƛ N′) ⦂ (A ⇒ B , C ⇒ D , fun⊑ c d)
compatible-lambda{Γ}{A}{B}{C}{D}{N}{N′}{c}{d} ⊨N⊑N′ γ γ′ = ⊢ℰλNλN′
 where
 ⊢ℰλNλN′ : 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ℰ⟦ A ⇒ B , C ⇒ D , fun⊑ c d ⟧ (⟪ γ ⟫ (ƛ N))
                                                         (⟪ γ′ ⟫ (ƛ N′))
 ⊢ℰλNλN′ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] Λᵒ[ W′ ] →ᵒI ▷𝓔N[W]N′[W′]))
  where
  ▷𝓔N[W]N′[W′] : ∀{W W′} → ▷ᵒ 𝒱⟦ A , C , c ⟧ W W′ ∷ 𝓖⟦ Γ ⟧ γ γ′
          ⊢ᵒ  ▷ᵒ ℰ⟦ B , D , d ⟧ ((⟪ ext γ ⟫ N) [ W ]) ((⟪ ext γ′ ⟫ N′) [ W′ ])
  ▷𝓔N[W]N′[W′] {W}{W′} =
      appᵒ (Sᵒ (▷→ (monoᵒ (→ᵒI (⊨N⊑N′ (W • γ) (W′ • γ′)))))) Zᵒ

compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊨ L ⊑ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d)
   → Γ ⊨ M ⊑ M′ ⦂ (A , A′ , c)
     ----------------------------------
   → Γ ⊨ L · M ⊑ L′ · M′ ⦂ (B , B′ , d)
compatible-app {Γ}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′} ⊨L⊑L′ ⊨M⊑M′ γ γ′ = {!!}

{-
compatible-app : ∀{Γ}{A A′ B B′}{c : A ⊑ A′}{d : B ⊑ B′}{L L′ M M′}
   → Γ ⊨ L ⊑ L′ ⦂ (A ⇒ B , A′ ⇒ B′ , fun⊑ c d)
   → Γ ⊨ M ⊑ M′ ⦂ (A , A′ , c)
     ----------------------------------
   → Γ ⊨ L · M ⊑ L′ · M′ ⦂ (B , B′ , d)
compatible-app {Γ}{A}{A′}{B}{B′}{c}{d}{L}{L′}{M}{M′} ⊨L⊑L′ ⊨M⊑M′ γ γ′ =
 ⊢ℰLM⊑LM′
 where
 ⊢ℰLM⊑LM′ : 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ℰ⟦ B , B′ , d ⟧ (⟪ γ ⟫ (L · M)) (⟪ γ′ ⟫ (L′ · M′))
 ⊢ℰLM⊑LM′ = ℰ-bind {F = ` (□· (⟪ γ ⟫ M))}{` (□· (⟪ γ′ ⟫ M′))} (⊨L⊑L′ γ γ′)
     (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰVM)))
  where
  𝓟₁ = λ V V′ → 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
           ∷ (⟪ γ′ ⟫ L′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
  ⊢ℰVM : ∀{V}{V′} → 𝓟₁ V V′ ⊢ᵒ ℰ⟦ B , B′ , d ⟧ (V · ⟪ γ ⟫ M) (V′ · ⟪ γ′ ⟫ M′) 
  ⊢ℰVM {V}{V′} = ⊢ᵒ-sucP Zᵒ λ 𝒱VV′sn →
   let (v , v′) = 𝒱⇒Value (A ⇒ B , A′ ⇒ B′ , fun⊑ c d) V V′ 𝒱VV′sn in
   ℰ-bind {F = ` (v ·□)}{F′ = ` (v′ ·□)} (Sᵒ (Sᵒ (Sᵒ (⊨M⊑M′ γ γ′))))
           (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰVWVW′)) )
   where
   𝓟₂ = λ V V′ W W′ → 𝒱⟦ A , A′ , c ⟧ W W′
          ∷ (⟪ γ′ ⟫ M′ —↠ W′)ᵒ ∷ (⟪ γ ⟫ M —↠ W)ᵒ
          ∷ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
          ∷ (⟪ γ′ ⟫ L′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ L —↠ V)ᵒ
          ∷ 𝓖⟦ Γ ⟧ γ γ′ 
   ⊢ℰVWVW′ : ∀{V V′ W W′} → 𝓟₂ V V′ W W′ ⊢ᵒ ℰ⟦ B , B′ , d ⟧ (V · W) (V′ · W′)
   ⊢ℰVWVW′ {V}{V′}{W}{W′} =
    let ⊢𝒱VV′ : 𝓟₂ V V′ W W′ ⊢ᵒ 𝒱⟦ A ⇒ B , A′ ⇒ B′ , fun⊑ c d ⟧ V V′
        ⊢𝒱VV′ = Sᵒ (Sᵒ (Sᵒ Zᵒ)) in
    let ⊢𝒱WW′ : 𝓟₂ V V′ W W′ ⊢ᵒ 𝒱⟦ A , A′ , c ⟧ W W′
        ⊢𝒱WW′ = Zᵒ in
    ⊢ᵒ-sucP ⊢𝒱WW′ λ 𝒱WW′sn →
    let (w , w′) = 𝒱⇒Value (A , A′ , c) W W′ 𝒱WW′sn in
    𝒱-fun-elim ⊢𝒱VV′ λ {N N′ refl refl 𝒱WW′→ℰNW →
    let pres-L : 𝓟₂ (ƛ N) (ƛ N′) W W′
                 ⊢ᵒ preserve-L (B , B′ , d) (ƛ N · W) (ƛ N′ · W′)
        pres-L = Λᵒ[ M₁ ] →ᵒI (constᵒE Zᵒ λ {ƛN·W→M₁ →
         let 𝒫₃ = ((ƛ N · W) —→ M₁)ᵒ ∷ 𝓟₂ (ƛ N) (ƛ N′) W W′ in
         let ⊢▷ℰNWNW′ : 𝓟₂ (ƛ N) (ƛ N′) W W′
                        ⊢ᵒ ▷ᵒ ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ])
             ⊢▷ℰNWNW′ = appᵒ 𝒱WW′→ℰNW (monoᵒ ⊢𝒱WW′) in
         let M₁=N[W] = deterministic ƛN·W→M₁ (β w) in
         let F₁ = (λ X → 𝓟₂ (ƛ N) (ƛ N′) W W′
                         ⊢ᵒ ▷ᵒ ℰ⟦ B , B′ , d ⟧ X (⟪ W′ • id ⟫ N′)) in
         let ⊢▷ℰM₁N[W′] : 𝓟₂ (ƛ N) (ƛ N′) W W′
                          ⊢ᵒ ▷ᵒ ℰ⟦ B , B′ , d ⟧ M₁ (N′ [ W′ ])
             ⊢▷ℰM₁N[W′] = subst F₁ (sym M₁=N[W]) ⊢▷ℰNWNW′ in
         let 𝒫₄ = ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ]) ∷ 𝒫₃ in
         let pres-R : 𝒫₄ ⊢ᵒ preserve-R (B , B′ , d) (N [ W ]) (ƛ N′ · W′)
             pres-R = Λᵒ[ M₁′ ] →ᵒI (constᵒE Zᵒ λ {ƛN′·W′→M₁′ →
              let M₁′=N′[W′] = deterministic ƛN′·W′→M₁′ (β w′) in
              let 𝒫₅ = ((ƛ N′ · W′) —→ M₁′)ᵒ ∷  𝒫₄ in
              let ▷ℰNWN′W′ : 𝒫₅ ⊢ᵒ ▷ᵒ ℰ⟦ (B , B′ , d) ⟧  (N [ W ]) (N′ [ W′ ])
                  ▷ℰNWN′W′ = ⊢ᵒ-weaken (⊢ᵒ-weaken (⊢ᵒ-weaken ⊢▷ℰNWNW′)) in
              let F₂ = λ M → 𝒫₅ ⊢ᵒ ▷ᵒ ℰ⟦ (B , B′ , d) ⟧  (N [ W ]) M in
              subst F₂ (sym M₁′=N′[W′]) ▷ℰNWN′W′
              }) in
         let conc′ : ℰ⟦ B , B′ , d ⟧ (N [ W ]) (N′ [ W′ ]) ∷ 𝒫₃
                     ⊢ᵒ ℰ⟦ B , B′ , d ⟧ (N [ W ]) (ƛ N′ · W′)
             conc′ = substᵒ (≡ᵒ-sym ℰ-stmt) {!!}
                  --(inj₂ᵒ (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , β w′) ,ᵒ pres-R))))
                  in
         let conc : 𝒫₃ ⊢ᵒ ▷ᵒ ℰ⟦ (B , B′ , d) ⟧ (N [ W ]) (ƛ N′ · W′) 
             conc = ▷→▷{𝒫₃}{ℰ⟦ (B , B′ , d) ⟧ (N [ W ]) (N′ [ W′ ])}
                        (⊢ᵒ-weaken ⊢▷ℰNWNW′) conc′ in
         subst (λ M → 𝒫₃ ⊢ᵒ ▷ᵒ ℰ⟦ (B , B′ , d) ⟧ M (ƛ N′ · W′)) (sym M₁=N[W])
               conc
         }) in
    substᵒ (≡ᵒ-sym ℰ-stmt) {!!}
     --(inj₂ᵒ (inj₁ᵒ (constᵒI (_ , (β w)) ,ᵒ pres-L)))
    }

𝒱-base-elim : ∀{𝒫}{ι}{ι′}{c}{V}{V′}{R}
  → 𝒫 ⊢ᵒ 𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ V V′
  → (∀ k → ι ≡ ι′ → V ≡ $ k → V′ ≡ $ k → 𝒫 ⊢ᵒ R)
    -------------------------------------------
  → 𝒫 ⊢ᵒ R
𝒱-base-elim{𝒫}{ι}{ι′}{c}{V}{V′}{R} ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ → G 𝒱VV′ ⊢𝒱VV′ cont
  where
  G : ∀{ι}{ι′}{c}{V}{V′}{n} →  #(𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ V V′) (suc n)
    → 𝒫 ⊢ᵒ 𝒱⟦ $ₜ ι , $ₜ ι′ , c ⟧ V V′
    → (∀ k → ι ≡ ι′ → V ≡ $ k → V′ ≡ $ k → 𝒫 ⊢ᵒ R)
    → 𝒫 ⊢ᵒ R
  G {ι} {.ι} {base⊑} {$ k} {$ k′} {n} refl ⊢𝒱kk cont = cont k refl refl refl

Value-inj-inv : ∀{V}{G}
   → Value (V ⟨ G !⟩)
   → Value V
Value-inj-inv {V} {G} (v 〈 .G 〉) = v

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

𝒱-dyn-any-elim : ∀{𝒫}{V}{V′}{G}{A′}{R}
   → (G⊑A′ : gnd⇒ty G ⊑ A′)
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , A′ , unk⊑any G⊑A′ ⟧ V V′
   → (∀ V₁ G → Value V₁ → V ≡ V₁ ⟨ G !⟩ → Value V′ → (G⊑A′ : gnd⇒ty G ⊑ A′)
       → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V₁ V′
       → 𝒫 ⊢ᵒ R)
   → 𝒫 ⊢ᵒ R
𝒱-dyn-any-elim {𝒫}{V}{V′}{G}{A′}{R} G⊑A′ ⊢𝒱VV′ cont =
  ⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ → aux G⊑A′ 𝒱VV′ ⊢𝒱VV′ cont
  where
  aux : ∀{𝒫}{V}{V′}{G}{A′}{R}{k}
     → (G⊑A′ : gnd⇒ty G ⊑ A′)
     → #(𝒱⟦ ★ , A′ , unk⊑any G⊑A′ ⟧ V V′) (suc k)
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , A′ , unk⊑any G⊑A′ ⟧ V V′
     → (∀ V₁ G → Value V₁ → V ≡ V₁ ⟨ G !⟩ → Value V′ → (G⊑A′ : gnd⇒ty G ⊑ A′)
         → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V₁ V′
         → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  aux {𝒫} {V ⟨ H !⟩} {V′} {G}{A′} {R} {k} G⊑A′ 𝒱VV′ ⊢𝒱VV′ cont
      with G ≡ᵍ H
  ... | no neq = ⊥-elim 𝒱VV′
  ... | yes refl =
        let 𝒱VV′₂ = proj₂ᵒ (proj₂ᵒ (substᵒ (𝒱-dyn-any G⊑A′) ⊢𝒱VV′)) in
        cont V G (proj₁ 𝒱VV′) refl (proj₁ (proj₂ 𝒱VV′)) G⊑A′ 𝒱VV′₂

dyn-gnd-inv : ∀{G}
  → (c : ★ ⊑ gnd⇒ty G)
  → c ≡ unk⊑any {G} Refl⊑
dyn-gnd-inv {$ᵍ ι} (unk⊑any {$ᵍ .ι} base⊑) = refl
dyn-gnd-inv {★⇒★} (unk⊑any {★⇒★} (fun⊑ c d))
  rewrite A⊑A-unique c | A⊑A-unique d = refl

𝒱-dyn-R : ∀{𝒫}{G}{c : ★ ⊑ gnd⇒ty G}{V}{V′}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , gnd⇒ty G , c ⟧ V V′
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑unk ⟧ V (V′ ⟨ G !⟩)
𝒱-dyn-R {𝒫} {G} {c} {V} {V′} ⊢𝒱VV′ rewrite dyn-gnd-inv c =
  𝒱-dyn-any-elim Refl⊑ ⊢𝒱VV′
  λ {V₁ H v₁ refl v′ H⊑G ⊢▷𝒱V₁V → Goal V₁ H v₁ v′ H⊑G ⊢▷𝒱V₁V }
  where
  Goal : ∀ V₁ H
     → Value V₁
     → Value V′
     → (H⊑G : gnd⇒ty H ⊑ gnd⇒ty G)
     → 𝒫 ⊢ᵒ (▷ᵒ 𝒱⟦ gnd⇒ty H , gnd⇒ty G , H⊑G ⟧ V₁ V′)
     → 𝒫 ⊢ᵒ 𝒱⟦ ★ , ★ , unk⊑unk ⟧ (V₁ ⟨ H !⟩) (V′ ⟨ G !⟩)
  Goal V₁ H v₁ v′ H⊑G ⊢▷𝒱V₁V
      with ⊑-gnd-unique H⊑G 
  ... | refl rewrite A⊑A-unique H⊑G = 
      substᵒ (≡ᵒ-sym (𝒱-dyn-dyn)) (constᵒI v₁ ,ᵒ (constᵒI v′ ,ᵒ ⊢▷𝒱V₁V))

𝒱-dyn-L : ∀{𝒫}{G}{A′}{c : gnd⇒ty G ⊑ A′}{V}{V′}
   → 𝒫 ⊢ᵒ 𝒱⟦ gnd⇒ty G , A′ , c ⟧ V V′
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ , A′ , unk⊑any c ⟧ (V ⟨ G !⟩) V′
𝒱-dyn-L {𝒫} {G} {A′} {c} {V} {V′} ⊢𝒱VV′ =
  substᵒ (≡ᵒ-sym (𝒱-dyn-any c))
  (⊢ᵒ-sucP ⊢𝒱VV′ λ 𝒱VV′ →
  let (v , v′) = 𝒱⇒Value (gnd⇒ty G , A′ , c) V V′ 𝒱VV′ in
  (constᵒI v ,ᵒ (constᵒI v′ ,ᵒ monoᵒ ⊢𝒱VV′)))
  
compatible-inj-L : ∀{Γ}{G A′}{c : gnd⇒ty G ⊑ A′}{M M′}
   → Γ ⊨ M ⊑ M′ ⦂ (gnd⇒ty G , A′ , c)
     ------------------------------------
   → Γ ⊨ M ⟨ G !⟩ ⊑ M′ ⦂ (★ , A′ , unk⊑any c)
compatible-inj-L{Γ}{G}{A′}{c}{M}{M′} ⊨M⊑M′ γ γ′ =
  ℰ-bind{F = ` □⟨ G !⟩}{□} (⊨M⊑M′ γ γ′)
      (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰV⟨G!⟩V′)))
  where
  𝒫₁ = λ V V′ → 𝒱⟦ gnd⇒ty G , A′ , c ⟧ V V′
               ∷ (⟪ γ′ ⟫ M′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
  ⊢ℰV⟨G!⟩V′ : ∀{V V′} → 𝒫₁ V V′ ⊢ᵒ  ℰ⟦ ★ , A′ , unk⊑any c ⟧ (V ⟨ G !⟩) V′
  ⊢ℰV⟨G!⟩V′ = 𝒱⇒ℰ (𝒱-dyn-L Zᵒ)

compatible-inj-R : ∀{Γ}{G}{c : ★ ⊑ gnd⇒ty G }{M M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , gnd⇒ty G , c)
   → Γ ⊨ M ⊑ M′ ⟨ G !⟩ ⦂ (★ , ★ , unk⊑unk)
compatible-inj-R{Γ}{G}{c }{M}{M′} ⊨M⊑M′ γ γ′ =
  ℰ-bind{F = □}{` □⟨ G !⟩}
    (⊨M⊑M′ γ γ′) (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰVV′⟨G!⟩)))
  where
  𝒫₁ = λ V V′ → 𝒱⟦ ★ , gnd⇒ty G , c ⟧ V V′
               ∷ (⟪ γ′ ⟫ M′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
  ⊢ℰVV′⟨G!⟩ : ∀{V V′} → 𝒫₁ V V′ ⊢ᵒ  ℰ⟦ ★ , ★ , unk⊑unk ⟧ V (V′ ⟨ G !⟩)
  ⊢ℰVV′⟨G!⟩ = 𝒱⇒ℰ (𝒱-dyn-R Zᵒ)

collapse-inv : ∀{V}{N}{G}
   → Value V
   → ((V ⟨ G !⟩) ⟨ G ?⟩) —→ N
   → N ≡ V
collapse-inv {V} {N} v (ξξ □⟨ G ?⟩ refl x₁ r) =
  ⊥-elim (value-irreducible (v 〈 G 〉) r)
collapse-inv {V} {.blame} v (ξξ-blame (□· M) ())
collapse-inv {V} {.blame} v (ξξ-blame (v₁ ·□) ())
collapse-inv {V} {.blame} v (ξξ-blame □⟨ G !⟩ ())
collapse-inv {V} {.blame} v (ξξ-blame □⟨ H ?⟩ ())
collapse-inv {V} {.V} v (collapse x refl) = refl
collapse-inv {V} {.blame} v (collide x x₁ refl) = ⊥-elim (x₁ refl)

collide-inv : ∀{V}{N}{G}{H}
   → G ≢ H
   → Value V
   → ((V ⟨ G !⟩) ⟨ H ?⟩) —→ N
   → N ≡ blame
collide-inv {V} {N} {G} {H} neq v (ξξ □⟨ H₁ ?⟩ refl x₁ red) =
  ⊥-elim (value-irreducible (v 〈 G 〉) red)
collide-inv {V} {.blame} {G} {H} neq v (ξξ-blame (□· M) ())
collide-inv {V} {.blame} {G} {H} neq v (ξξ-blame (v₁ ·□) ())
collide-inv {V} {.blame} {G} {H} neq v (ξξ-blame □⟨ G₁ !⟩ ())
collide-inv {V} {.blame} {G} {H} neq v (ξξ-blame □⟨ H₁ ?⟩ ())
collide-inv {V} {N} {G} {H} neq v (collapse x refl) = ⊥-elim (neq refl)
collide-inv {V} {.blame} {G} {H} neq v (collide x x₁ refl) = refl

compatible-proj-L : ∀{Γ}{H}{A′}{c : gnd⇒ty H ⊑ A′}{M}{M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , A′ ,  unk⊑any c)
   → Γ ⊨ M ⟨ H ?⟩ ⊑ M′ ⦂ (gnd⇒ty H , A′ , c)
compatible-proj-L {Γ}{H}{A′}{c}{M}{M′} ⊨M⊑M′ γ γ′ =
  ℰ-bind{F = ` □⟨ H ?⟩}{□} (⊨M⊑M′ γ γ′)
     (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰV⟨H?⟩V′)))
  where
  𝒫₁ = λ V V′ H A′ (c : gnd⇒ty H ⊑ A′)
          → 𝒱⟦ ★ , A′ , unk⊑any c ⟧ V V′
            ∷ (⟪ γ′ ⟫ M′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′
  ⊢ℰV⟨H?⟩V′ : ∀{V V′ A′ H}{c}
     → 𝒫₁ V V′ H A′ c ⊢ᵒ  ℰ⟦ gnd⇒ty H , A′ , c ⟧ (V ⟨ H ?⟩) V′
  ⊢ℰV⟨H?⟩V′ {V} {V′} {A′} {H} {c} =
    𝒱-dyn-any-elim c Zᵒ Goal
    where
    Goal : (V₁ : Term) (G : Ground) →  Value V₁ → V ≡ (V₁ ⟨ G !⟩)
       → Value V′ → (G⊑A′ : gnd⇒ty G ⊑ A′)
       → 𝒫₁ V V′ H A′ c ⊢ᵒ (▷ᵒ 𝒱⟦ gnd⇒ty G , A′ , G⊑A′ ⟧ V₁ V′)
       → 𝒫₁ V V′ H A′ c ⊢ᵒ ℰ⟦ gnd⇒ty H , A′ , c ⟧ (V ⟨ H ?⟩) V′
    Goal V₁ G v₁ refl v′ G⊑A′ ⊢▷𝒱V₁V′
        with gnd-unique c G⊑A′
    ... | refl
        with gnd-prec-unique c G⊑A′
    ... | refl =
        substᵒ (≡ᵒ-sym ℰ-stmt) {!!}
{-        
          (inj₂ᵒ (inj₁ᵒ ((constᵒI (_ , (collapse v₁ refl))) ,ᵒ
             (Λᵒ[ N ] (→ᵒI{P = (V₁ ⟨ G !⟩ ⟨ G ?⟩ —→ N)ᵒ}
             (⊢ᵒ-sucP Zᵒ λ V₁!?→N →
             let N≡V₁ = collapse-inv v₁ V₁!?→N in
             subst (λ N → (V₁ ⟨ G !⟩ ⟨ G ?⟩ —→ N)ᵒ ∷ 𝒫₁ (V₁ ⟨ G !⟩) V′ G A′ c
                       ⊢ᵒ ▷ᵒ ℰ⟦ gnd⇒ty G , A′ , c ⟧ N V′)
             (sym N≡V₁)
             (▷→▷ (Sᵒ ⊢▷𝒱V₁V′) (𝒱⇒ℰ Zᵒ))))))))
-}
 
        
compatible-proj-R : ∀{Γ}{H′}{c : ★ ⊑ gnd⇒ty H′}{M}{M′}
   → Γ ⊨ M ⊑ M′ ⦂ (★ , ★ , unk⊑unk)
   → Γ ⊨ M ⊑ M′ ⟨ H′ ?⟩ ⦂ (★ , gnd⇒ty H′ , c)
compatible-proj-R {Γ}{H′}{c}{M}{M′} ⊨M⊑M′ γ γ′ =
  ℰ-bind{F = □}{` □⟨ H′ ?⟩} (⊨M⊑M′ γ γ′)
     (Λᵒ[ V ] Λᵒ[ V′ ] →ᵒI (→ᵒI (→ᵒI ⊢ℰVV′⟨H?⟩)))
  where
  𝒫₁ = λ V V′ → 𝒱⟦ ★ , ★ , unk⊑unk ⟧ V V′
                 ∷ (⟪ γ′ ⟫ M′ —↠ V′)ᵒ ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ γ′  
  ⊢ℰVV′⟨H?⟩ : ∀{V V′ H′ c}
     → 𝒫₁ V V′ ⊢ᵒ ℰ⟦ ★ , gnd⇒ty H′ , c ⟧ V (V′ ⟨ H′ ?⟩)
  ⊢ℰVV′⟨H?⟩ {V} {V′} {H′} {c} =
    𝒱-dyn-dyn-elim Zᵒ Goal
    where
    Goal : ∀ V₁ V₁′ G → Value V₁ → Value V₁′
              → V ≡ (V₁ ⟨ G !⟩) → V′ ≡ (V₁′ ⟨ G !⟩)
       → 𝒫₁ V V′ ⊢ᵒ  (▷ᵒ 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V₁′)
       → 𝒫₁ V V′ ⊢ᵒ ℰ⟦ ★ , gnd⇒ty H′ , c ⟧ V (V′ ⟨ H′ ?⟩)
    Goal V₁ V₁′ G v₁ v₁′ refl refl ⊢▷𝒱V₁V₁′
        with G ≡ᵍ H′
    ... | no neq =
        substᵒ (≡ᵒ-sym ℰ-stmt) {!!}
--        (inj₂ᵒ (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , collide v₁′ neq refl)
--          ,ᵒ (Λᵒ[ N′ ] (→ᵒI (Goal2 v₁′)))))))
     where
     Goal2 : ∀{N′}
        → Value V₁′
        → (V′ ⟨ H′ ?⟩ —→ N′)ᵒ ∷ 𝒫₁ V V′
           ⊢ᵒ ▷ᵒ ℰ⟦ ★ , gnd⇒ty H′ , c ⟧ V N′
     Goal2 {N′} v₁′ =
       ⊢ᵒ-sucP Zᵒ λ {red →
       let N′≡blame = collide-inv neq v₁′ red in
       subst (λ N′ → (((V₁′ ⟨ G !⟩) ⟨ H′ ?⟩) —→ N′) ᵒ ∷
                        𝒫₁ (V₁ ⟨ G !⟩) (V₁′ ⟨ G !⟩)
                       ⊢ᵒ (▷ᵒ ℰ⟦ ★ , gnd⇒ty H′ , c ⟧ (V₁ ⟨ G !⟩) N′))
             (sym N′≡blame)
       (monoᵒ ℰ-blame)
       }
       
    Goal V₁ V₁′ G v₁ v₁′ refl refl ⊢▷𝒱V₁V₁′ | yes refl =
        substᵒ (≡ᵒ-sym ℰ-stmt) {!!}
--        (inj₂ᵒ (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , collapse v₁′ refl)
--          ,ᵒ (Λᵒ[ N′ ] (→ᵒI (Goal2 v₁′ ⊢▷𝒱V₁V₁′)))))))
     where
     Goal2 : ∀{N′}
        → Value V₁′
        → 𝒫₁ V V′ ⊢ᵒ  (▷ᵒ 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V₁′)
        → (V′ ⟨ H′ ?⟩ —→ N′)ᵒ ∷ 𝒫₁ V V′
           ⊢ᵒ ▷ᵒ ℰ⟦ ★ , gnd⇒ty H′ , c ⟧ V N′
     Goal2 {N′} v₁′ ⊢▷𝒱V₁V₁′ =
       ⊢ᵒ-sucP Zᵒ λ {red →
       let N′≡V₁′ = collapse-inv v₁′ red in
       subst (λ N′ → (((V₁′ ⟨ G !⟩) ⟨ G ?⟩) —→ N′) ᵒ
                     ∷ 𝒫₁ (V₁ ⟨ G !⟩) (V₁′ ⟨ G !⟩)
                     ⊢ᵒ (▷ᵒ ℰ⟦ ★ , gnd⇒ty G , c ⟧ (V₁ ⟨ G !⟩) N′))
             (sym N′≡V₁′)
       (let 𝒫₂ = 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V₁′
                  ∷  (((V₁′ ⟨ G !⟩) ⟨ G ?⟩) —→ V₁′) ᵒ
                  ∷ 𝒫₁ (V₁ ⟨ G !⟩) (V₁′ ⟨ G !⟩) in
        let 𝒱V₁V′ : 𝒫₂ ⊢ᵒ 𝒱⟦ gnd⇒ty G , gnd⇒ty G , Refl⊑ ⟧ V₁ V₁′
            𝒱V₁V′ = Zᵒ in
        let 𝒱V₁!V′ : 𝒫₂ ⊢ᵒ 𝒱⟦ ★ , gnd⇒ty G , c ⟧ (V₁ ⟨ G !⟩) V₁′
            𝒱V₁!V′ = subst(λ c → 𝒫₂ ⊢ᵒ 𝒱⟦ ★ , gnd⇒ty G , c ⟧ (V₁ ⟨ G !⟩) V₁′)
                       (dyn-prec-unique (unk⊑any Refl⊑) c) (𝒱-dyn-L 𝒱V₁V′) in
        (▷→▷ (Sᵒ ⊢▷𝒱V₁V₁′) (𝒱⇒ℰ 𝒱V₁!V′)))
       }
       
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
fundamental {Γ} {★} {A′} {unk⊑} (M ⟨ G !⟩) M′ (⊑-inj-L ⊢M⊑M′) =
    compatible-inj-L{G =  G}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {★} {★} {.unk⊑unk} M (M′ ⟨ G !⟩) (⊑-inj-R ⊢M⊑M′) =
    compatible-inj-R{Γ}{G = G}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {_} {A′} {A⊑A′} (M ⟨ H ?⟩) M′ (⊑-proj-L ⊢M⊑M′) =
    compatible-proj-L{Γ}{H}{A′}{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.(gnd⇒ty _)} {A⊑A′} M (M′ ⟨ H′ ?⟩) (⊑-proj-R ⊢M⊑M′) =
    compatible-proj-R{M = M}{M′} (fundamental M M′ ⊢M⊑M′)
fundamental {Γ} {A} {.A} {.Refl⊑} M .blame (⊑-blame ⊢M∶A) =
   compatible-blame ⊢M∶A

empty-ctx-▷ : ∀{P}
   → [] ⊢ᵒ ▷ᵒ P
   → [] ⊢ᵒ P
empty-ctx-▷ {P} ⊢▷P = ⊢ᵒ-intro λ {n tt → ⊢ᵒ-elim ⊢▷P (suc n) tt}

diverge : Term → Set
diverge M = ∀ N → M —↠ N → ∃[ N′ ] (N —→ N′)
-}
