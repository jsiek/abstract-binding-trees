{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastLogRelLemmas where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
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
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.CastLogRel2

postulate
  determinism : ∀ {M N N′ : Term}
    → M —→ N
    → M —→ N′
    → N ≡ N′

subtract—↠ : ∀{L M N : Term}
   → (lm : L —↠ M)
   → (ln : L —↠ N)
   → len lm ≤ len ln
   → Σ[ r ∈ M —↠ N ] (len r ≡ len ln ∸ len lm)
subtract—↠ {L} {.L} {N} (.L END) L—↠N lt = L—↠N , refl
subtract—↠ {L} {M} {N} (.L —→⟨ L→L₁ ⟩ L₁—↠M) (.L —→⟨ L→L₂ ⟩ L₂—↠N) (s≤s lt)
    with determinism L→L₁ L→L₂
... | refl = subtract—↠ L₁—↠M L₂—↠N lt


lemma1 : ∀ x k y
   → suc (suc x) ≤ k + suc y
   → x < k + y
lemma1 x k y lt = B
    where A : suc (suc x) ≤ suc (k + y)
          A = ≤-trans lt (≤-reflexive (+-suc _ _))
          B : suc x ≤ k + y
          B
              with A
          ... | s≤s lt = lt

𝓔-expansion : ∀{A N N′ k}
   → 𝓔⟦ A ⟧ N′ k
   → (N→N′ : N —↠ N′)
     ------------------------
   → 𝓔⟦ A ⟧ N (k + len N→N′)
𝓔-expansion {A} {N} {.N} {k} 𝓔N′ (.N END) M N→M M→N<k+len[N→N′]
    with 𝓔N′ M N→M (≤-trans M→N<k+len[N→N′] (≤-reflexive (+-identityʳ k)))
... | inj₁ 𝓥M = inj₁ (subst (λ X → 𝓥⟦ A ⟧ M X) EQ 𝓥M)
    where EQ : k ∸ len N→M ≡ (k + 0) ∸ len N→M
          EQ = cong (λ X → X ∸ len N→M) (sym (+-identityʳ k))
... | inj₂ (inj₁ red) = inj₂ (inj₁ red)
... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
𝓔-expansion {A} {N} {N′} {k} 𝓔N′ (.N —→⟨ N→N₁ ⟩ N₁—↠N′) .N (.N END) M→N<k+len[N→N′] = inj₂ (inj₁ (_ , N→N₁))
𝓔-expansion {A} {N} {N′} {k} 𝓔N′ (.N —→⟨ N→M ⟩ M—↠N′) N₁ (.N —→⟨ N→M₁ ⟩ M₁→N₁) lt
    with determinism N→M N→M₁
... | refl
    with 𝓔-expansion 𝓔N′ M—↠N′ N₁ M₁→N₁ (lemma1 _ _ _ lt)
... | inj₁ 𝓥N₁ = inj₁ (mono-𝓥 (≤⇒≤′ (≤-reflexive EQ)) 𝓥N₁)
    where
          open Eq.≡-Reasoning
          EQ : k + suc (len M—↠N′) ∸ suc (len M₁→N₁) ≡ k + len M—↠N′ ∸ len M₁→N₁
          EQ =
            begin
              (k + suc (len M—↠N′)) ∸ suc (len M₁→N₁)
            ≡⟨ cong (λ X → X ∸ suc (len M₁→N₁)) (+-suc k (len M—↠N′)) ⟩
              (suc (k + len M—↠N′)) ∸ suc (len M₁→N₁)
            ≡⟨ refl ⟩
              k + len M—↠N′ ∸ len M₁→N₁
            ∎
... | inj₂ (inj₁ red) = inj₂ (inj₁ red)
... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)

value-unique : ∀{V}
   → (v : Value V)
   → (v′ : Value V)
   → v ≡ v′
value-unique {.(ƛ N)} (ƛ̬ N) (ƛ̬ .N) = refl
value-unique {.($ k)} ($̬ k) ($̬ .k) = refl
value-unique {.(_ ⟨ g !⟩)} (v 〈 g 〉) (v′ 〈 .g 〉) rewrite value-unique v v′ = refl

unique-decomp : ∀{F₁ F₂ N₁ N₂ N₁′ N₂′}
   → F₁ ⟦ N₁ ⟧ ≡ F₂ ⟦ N₂ ⟧
   → N₁ —→ N₁′
   → N₂ —→ N₂′
   → F₁ ≡ F₂ × N₁ ≡ N₂
unique-decomp {□· M} {□· M} refl N₁→N₁′ N₂→N₂′ = refl , refl
unique-decomp {□· M} {v ·□} refl N₁→N₁′ N₂→N₂′ = ⊥-elim (value-irreducible v N₁→N₁′)
unique-decomp {v ·□} {□· M} refl N₁→N₁′ N₂→N₂′ = ⊥-elim (value-irreducible v N₂→N₂′)
unique-decomp {v ·□} {v′ ·□} refl N₁→N₁′ N₂→N₂′ rewrite value-unique v v′ = refl , refl
unique-decomp {□⟨ g !⟩} {□⟨ g₁ !⟩} refl N₁→N₁′ N₂→N₂′ = refl , refl
unique-decomp {□⟨ h ?⟩} {□⟨ h₁ ?⟩} refl N₁→N₁′ N₂→N₂′ = refl , refl

-- frame—↠ : ∀{M M′}
--   → M —↠ M′
--   → (∃[ F ] ∃[ N ] ∃[ N′ ] (M ≡ F ⟦ N ⟧ × (N —↠ N′) × M′ ≡ F ⟦ N′ ⟧))
--   ⊎ (∃[ F ] ∃[ N ] ∃[ V ] (M ≡ F ⟦ N ⟧ × (N —↠ V) × Value V × (F ⟦ V ⟧ —↠ N)))
--   ⊎ M ≡ M′
--   ⊎ M′ ≡ blame
-- frame—↠ {M} {.M} (.M END) = inj₂ (inj₂ (inj₁ refl))
-- frame—↠ {M} {M′} (.M —→⟨ ξξ F refl refl M→M₁ ⟩ M₁—↠M′)
--     with frame—↠ M₁—↠M′
-- ... | inj₁ (F , N , N′ , eq , N→N′ , refl) = {!!}
-- ... | inj₂ yy = {!!}
-- frame—↠ {M} {M′} (.M —→⟨ ξξ-blame F refl ⟩ M₁—↠M′) = {!!}
-- frame—↠ {.(ƛ _ · _)} {M′} (.(ƛ _ · _) —→⟨ β x ⟩ M₁—↠M′) = {!!}
-- frame—↠ {.(_ ⟨ h ?⟩)} {M′} (.(_ ⟨ h ?⟩) —→⟨ collapse x g h x₁ ⟩ M₁—↠M′) = {!!}
-- frame—↠ {.(_ ⟨ h ?⟩)} {M′} (.(_ ⟨ h ?⟩) —→⟨ collide x g h x₁ x₂ ⟩ M₁—↠M′) = {!!}


-- frame—↠ : ∀{FM F M N}
--   → FM —↠ N
--   → FM ≡ (F ⟦ M ⟧)
--   → (∃[ M′ ] ((M —↠ M′) × N ≡ F ⟦ M′ ⟧)) ⊎ (∃[ V ] (Value V × (M —↠ V) × (F ⟦ V ⟧ —↠ N)))
-- frame—↠ {FM} {F} {M} {N} (.FM END) eq = inj₁ (M , (_ END) , eq)
-- frame—↠ {FM} {F} {M} {N} (.FM —→⟨ ξξ F₁ refl refl FM→M₁ ⟩ M₁—↠N) eq rewrite eq
--     with frame—↠ M₁—↠N refl
-- ... | inj₁ (M′ , M→M′ , refl) = inj₁ ({!!} , {!!} , {!!})
-- ... | inj₂ (V , v , M→V , FV→N) = {!!}
-- frame—↠ {FM} {F} {M} {N} (.FM —→⟨ ξξ-blame F₁ x ⟩ M₁—↠N) eq = {!!}
-- frame—↠ {.(ƛ _ · _)} {F} {M} {N} (.(ƛ _ · _) —→⟨ β x ⟩ M₁—↠N) eq = {!!}
-- frame—↠ {.(_ ⟨ h ?⟩)} {F} {M} {N} (.(_ ⟨ h ?⟩) —→⟨ collapse x g h x₁ ⟩ M₁—↠N) eq = {!!}
-- frame—↠ {.(_ ⟨ h ?⟩)} {F} {M} {N} (.(_ ⟨ h ?⟩) —→⟨ collide x g h x₁ x₂ ⟩ M₁—↠N) eq = {!!}



bind-value : ∀ {A}{F}{M}{k}
   → (∀ V → (r : M —↠ V) → 𝓔⟦ A ⟧ (F ⟦ V ⟧) (k + len r))
   → 𝓔⟦ A ⟧ (F ⟦ M ⟧) k
bind-value {A}{F}{M} 𝓔FV N FM→N M→N<k = {!!}
