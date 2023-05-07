{-# OPTIONS --rewriting #-}
module rewriting.examples.Experiments where

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
pre-𝒱 (.★ , .★ , unk⊑unk) V V′ = ⊥ ˢ
pre-𝒱 (.★ , .A′ , unk⊑any{G}{A′} G⊑A′) (V ⟨ H !⟩) V′
    with G ≡ᵍ H
... | yes refl = (Value V)ˢ ×ˢ (Value V′)ˢ
                      ×ˢ ▷ˢ (𝒱ˢ⟦ (gnd⇒ty G , A′ , G⊑A′) ⟧ V V′)
... | no new = ⊥ ˢ
pre-𝒱 (.★ , .A′ , unk⊑any{G}{A′} G⊑A′) V V′ = ⊥ ˢ
pre-𝒱 ($ₜ ι , $ₜ ι , base⊑) ($ c) ($ c′) = (c ≡ c′) ˢ
pre-𝒱 ($ₜ ι , $ₜ ι , base⊑) V V′ = ⊥ ˢ
pre-𝒱 ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) (ƛ N) (ƛ N′) =
    ∀ˢ[ W ] ∀ˢ[ W′ ] ▷ˢ (𝒱ˢ⟦ (A , A′ , A⊑A′) ⟧ W W′)
                  →ˢ ▷ˢ (ℰˢ⟦ (B , B′ , B⊑B′) ⟧ (N [ W ]) (N′ [ W′ ])) 
pre-𝒱 ((A ⇒ B) , (A′ ⇒ B′) , fun⊑ A⊑A′ B⊑B′) V V′ = ⊥ ˢ 

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

abstract
  𝒱⟦_⟧ : (c : Prec) → Term → Term → Setᵒ
  𝒱⟦ c ⟧ V V′ = ℰ⊎𝒱 (inj₁ (c , V , V′))

  ℰ⟦_⟧ : (c : Prec) → Term → Term → Setᵒ
  ℰ⟦ c ⟧ M M′ = ℰ⊎𝒱 (inj₂ (c , M , M′))

  ℰ-stmt : ∀{c}{M M′}
    → ℰ⟦ c ⟧ M M′ ≡ᵒ
          (((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ 𝒱⟦ c ⟧ V M′))
           ⊎ᵒ (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (ℰ⟦ c ⟧ M N′))
           ⊎ᵒ (Blame M′)ᵒ)
  ℰ-stmt {c}{M}{M′} =
    let X₂ = inj₂ (c , M , M′) in
    ℰ⟦ c ⟧ M M′                                      ⩦⟨ ≡ᵒ-refl refl ⟩
    μᵒ pre-ℰ⊎𝒱 X₂                                  ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X₂ ⟩
    # (pre-ℰ⊎𝒱 X₂) (ℰ⊎𝒱 , ttᵖ)
                                    ⩦⟨ {!!} ⟩
          (((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ 𝒱⟦ c ⟧ V M′))
           ⊎ᵒ (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (ℰ⟦ c ⟧ M N′))
           ⊎ᵒ (Blame M′)ᵒ)
    ∎
{-    
    where
    X₁ = λ V → (inj₁ (c , V , M′))
    EQ = cong-⊎ᵒ (cong-×ᵒ (≡ᵒ-refl refl)
                        (cong-∃ (λ V → cong-×ᵒ (≡ᵒ-refl refl)
                                         (cong-×ᵒ (≡ᵒ-refl refl)
                                   (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (X₁ V)))))))
                 (≡ᵒ-refl refl)
-}

  ℰ-suc  : ∀{c}{M}{M′}{k}
    → #(ℰ⟦ c ⟧ M M′) (suc k) ≡
        #(((Value M′)ᵒ ×ᵒ (∃ᵒ[ V ] (M —↠ V)ᵒ ×ᵒ (Value V)ᵒ ×ᵒ 𝒱⟦ c ⟧ V M′))
         ⊎ᵒ (∃ᵒ[ N′ ] (M′ —→ N′)ᵒ ×ᵒ ▷ᵒ (ℰ⟦ c ⟧ M N′))
         ⊎ᵒ (Blame M′)ᵒ) (suc k)
  ℰ-suc {c}{M}{M′}{k} = refl

{- Relate Open Terms -}

𝓖⟦_⟧ : (Γ : List Prec) → Subst → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ σ′ = []
𝓖⟦ c ∷ Γ ⟧ σ σ′ = (𝒱⟦ c ⟧ (σ 0) (σ′ 0))
                     ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x)) (λ x → σ′ (suc x))

_⊨_⊑_⦂_ : List Prec → Term → Term → Prec → Set
Γ ⊨ M ⊑ M′ ⦂ c = ∀ (γ γ′ : Subst) → 𝓖⟦ Γ ⟧ γ γ′ ⊢ᵒ ℰ⟦ c ⟧ (⟪ γ ⟫ M) (⟪ γ′ ⟫ M′)

{---------- Fundamental Theorem -----------------------------------------------}

fundamental : ∀ {Γ}{A}{A′}{A⊑A′ : A ⊑ A′} → (M M′ : Term)
  → Γ ⊩ M ⊑ M′ ⦂ A⊑A′
    ----------------------------
  → Γ ⊨ M ⊑ M′ ⦂ (A , A′ , A⊑A′)
fundamental {Γ} {A} {A′} {A⊑A′} M⊑M′ = {!!}

{---------- Gradual Guarantee -------------------------------------------------}

ℰ-preserve-multi : ∀{c : Prec}{k}
  → (M M′ N′ : Term)
  → (M′→N′ : M′ —↠ N′)
  → #(ℰ⟦ c ⟧ M M′) (suc (len M′→N′ + k))
  → #(ℰ⟦ c ⟧ M N′) (suc k)
ℰ-preserve-multi{c}{k} M M′ N′ (.M′ END) ℰMM′ = ℰMM′
ℰ-preserve-multi{c}{k} M M′ N′ (.M′ —→⟨ M′→M′₁ ⟩ M′₁→N′) ℰMM′ 
    rewrite ℰ-suc{c}{M}{M′}{suc (len M′₁→N′ + k)}
    with ℰMM′
... | inj₁ (m′ , V , M→V , v , 𝒱VM′) =
      ⊥-elim (value-irreducible m′ M′→M′₁)
... | inj₂ (inj₂ b′) =
      ⊥-elim (blame-irred b′ M′→M′₁)
... | inj₂ (inj₁ (M′₂ , M′→M′₂ , ▷ℰMM′₂))
    rewrite deterministic M′→M′₁ M′→M′₂ =
    ℰ-preserve-multi M M′₂ N′ M′₁→N′ ▷ℰMM′₂

ℰ-catchup : ∀{c}{k}
  → (M V′ : Term)
  → Value V′
  → #(ℰ⟦ c ⟧ M V′) (suc k)
  → ∃[ V ] ((M —↠ V) × (Value V) × #(𝒱⟦ c ⟧ V V′) (suc k))
ℰ-catchup {c}{k} M V′ v′ ℰMV′ 
    rewrite ℰ-suc{c}{M}{V′}{k}
    with ℰMV′
... | inj₂ (inj₂ isBlame) = ⊥-elim (blame-not-value v′ refl)
... | inj₂ (inj₁ (V′₂ , V′→V′₂ , _)) = ⊥-elim (value-irreducible v′ V′→V′₂)
... | inj₁ (v′ , V , M→V , v , 𝒱VV′) = V , M→V , v , 𝒱VV′

{-
  If the more precise term goes to a value, so does the less precise term.
 -}
GG2a : ∀{A}{A′}{A⊑A′ : A ⊑ A′}{M}{M′}{V′}
   → [] ⊩ M ⊑ M′ ⦂ A⊑A′
   → M′ —↠ V′
   → Value V′
   → ∃[ V ] (M —↠ V) × (Value V) × # (𝒱⟦ A , A′ , A⊑A′ ⟧ V V′) 1
GG2a {A}{A′}{A⊑A′}{M}{M′}{V′} M⊑M′ M′→V′ v′ =
  let ⊨M⊑M′ = fundamental M M′ M⊑M′ in
  let ℰMM′ = ⊢ᵒ-elim (⊨M⊑M′ id id) (suc (len M′→V′)) tt in
  let ℰMV′ = ℰ-preserve-multi{k = 0} M M′ V′ M′→V′
             (subst (λ X → # (ℰ⟦ A , A′ , A⊑A′ ⟧ M M′) (suc X))
                (sym (+-identityʳ (len M′→V′))) ℰMM′) in
  ℰ-catchup M V′ v′ ℰMV′

