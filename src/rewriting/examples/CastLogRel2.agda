{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}
module rewriting.examples.CastLogRel2 where

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
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import Structures using (extensionality)
open import rewriting.examples.Cast

{- Lexicographic Recursion/Induction -}

_<₂_ : Rel (ℕ × ℕ) lzero
_<₂_ = ×-Lex _≡_ _<_ _<_

less-eq-less : ∀ {x y x′ y′} → x ≤ x′ → y < y′ → (x , y) <₂ (x′ , y′)
less-eq-less {x}{y}{x′}{y′} lt1 lt2
    with x ≟ x′
... | yes refl = inj₂ (refl , lt2)
... | no neq = inj₁ (≤∧≢⇒< lt1 neq)

<₂-Rec : ∀{ℓ} → RecStruct (ℕ × ℕ) ℓ ℓ
<₂-Rec = WfRec _<₂_

<₂-wellFounded : WellFounded _<₂_
<₂-wellFounded = ×-wellFounded <-wellFounded <-wellFounded

open WF.All <₂-wellFounded renaming (wfRec to <₂-rec)


{- Logical Relation for Type Safety -}

ValPred : ℕ × ℕ → Set₁
ValPred (k , s) = (A : Type) → (s ≡ size A) → Term → Set

{- This is already proved somewhere in the stdlib but I failed to figure out how to get to it. -}
<₂-trans : ∀{p q r} → p <₂ q → q <₂ r → p <₂ r
<₂-trans (inj₁ x) (inj₁ x₁) = inj₁ (<-trans x x₁)
<₂-trans (inj₁ x) (inj₂ (refl , snd)) = inj₁ x
<₂-trans (inj₂ (refl , snd)) (inj₁ x) = inj₁ x
<₂-trans (inj₂ (refl , x)) (inj₂ (refl , y)) = inj₂ (refl , <-trans x y)

<₂-Rec-down : ∀{P : ℕ × ℕ → Set₁}{p}{q}
   → p <₂ q
   → <₂-Rec P q
   → <₂-Rec P p
<₂-Rec-down p<q Pq y y<p = Pq y (<₂-trans y<p p<q)

<₂-Rec-subtract : ∀{P : ℕ × ℕ → Set₁}{k}{j}{s}
   → <₂-Rec P (k , s)
   → <₂-Rec P (k ∸ j , s)
<₂-Rec-subtract {P} {zero} {j} Pk rewrite 0∸n≡0 j = Pk
<₂-Rec-subtract {P} {suc k} {zero} Pk = Pk
<₂-Rec-subtract {P} {suc k} {suc j} Pk = <₂-Rec-down (inj₁ (s≤s (m∸n≤m k j))) Pk

V-step : (p : ℕ × ℕ) → (<₂-Rec ValPred p) → ValPred p
V-step (k , .(size ★)) rec ★ refl (ƛ N) = ⊥
V-step (k , .(size ★)) rec ★ refl ($ c) = ⊥
V-step (zero , .(size ★)) rec ★ refl (V ⟨ g !⟩) = Value V
V-step (suc k , .(size ★)) rec ★ refl ((op-inject {G} g) ⦅ cons (ast V) nil ⦆) =
  V-step (k , size G) (<₂-Rec-down (inj₁ (s≤s ≤-refl)) rec) G refl V
V-step (k , .(size ★)) rec ★ refl (L · M) = ⊥
V-step (k , .(size ★)) rec ★ refl (` x) = ⊥
V-step (k , .(size ★)) rec ★ refl (V ⟨ h ?⟩) = ⊥
V-step (k , .(size ★)) rec ★ refl blame = ⊥

V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl (ƛ N) = ⊥
V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl ((op-lit {ι′} c) ⦅ nil ⦆) = ι ≡ ι′
V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl (V ⟨ g !⟩) = ⊥
V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl (L · M) = ⊥
V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl (` x) = ⊥
V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl (V ⟨ h ?⟩) = ⊥
V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl blame = ⊥

V-step (k , .(size (A ⇒ B))) rec (A ⇒ B) refl (ƛ N) =
   ∀ W (j : ℕ) → (lt : j ≤ k)
         → rec (j , size A) (less-eq-less lt (s≤s (m≤m⊔n (size A) (size B)))) A refl W
         → ∀ N′ → (NW→N′ : N [ W ] —↠ N′) → (len NW→N′ < j)
         → (rec (j ∸ len NW→N′ , size B)
                (less-eq-less (≤-trans (m∸n≤m j (len NW→N′)) lt) (s≤s (m≤n⊔m (size A) (size B)))) B refl N′)
           ⊎ (∃[ N″ ] (N′ —→ N″))
           ⊎ N′ ≡ blame
V-step (k , .(size (A ⇒ B))) rec (A ⇒ B) refl (` x) = ⊥
V-step (k , .(size (A ⇒ B))) rec (A ⇒ B) refl ($ c) = ⊥
V-step (k , .(size (A ⇒ B))) rec (A ⇒ B) refl (V ⟨ g !⟩) = ⊥
V-step (k , .(size (A ⇒ B))) rec (A ⇒ B) refl (V ⟨ h ?⟩) = ⊥
V-step (k , .(size (A ⇒ B))) rec (A ⇒ B) refl blame = ⊥
V-step (k , .(size (A ⇒ B))) rec (A ⇒ B) refl (L · M) = ⊥


abstract
  SafeVal : (p : ℕ × ℕ) → ValPred p
  SafeVal = <₂-rec _ (λ i → ValPred i) V-step

𝓥⟦_⟧ : (A : Type) → Term → ℕ → Set
𝓥⟦ A ⟧ V k = SafeVal (k , size A) A refl V

𝓔⟦_⟧ : Type → Term → ℕ → Set
𝓔⟦ A ⟧ M k = ∀ N → (M→N : M —↠ N) → (len M→N < k)
              → 𝓥⟦ A ⟧ N (k ∸ len M→N)
                ⊎ (∃[ N′ ] (N —→ N′))
                ⊎ N ≡ blame               

postulate
  V-step-ext : (x : ℕ × ℕ) → ∀ {IH IH′}
      → (∀{y} (y<x : y <₂ x) → IH y y<x ≡ IH′ y y<x)
      → V-step x IH ≡ V-step x IH′

abstract
  unfold-SafeVal : ∀ i → SafeVal i ≡ V-step i (λ i′ _ → SafeVal i′)
  unfold-SafeVal i = FixPoint.unfold-wfRec <₂-wellFounded (λ i → ValPred i)
                     V-step V-step-ext {i}

{- Equations for the Logical Relation -}

V-base : ∀{n}{ι}{ι′}{c : rep ι′}
   → 𝓥⟦ $ₜ ι ⟧ ($ c) n ≡ (ι ≡ ι′)
V-base {n} rewrite unfold-SafeVal (n , 0) = refl

V-dyn-zero : ∀{G}{V}{g : Ground G}
   → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) 0 ≡ Value V
V-dyn-zero rewrite unfold-SafeVal (0 , size ★) = refl

V-dyn : ∀{n}{G}{V}{g : Ground G}
   → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) (suc n) ≡ 𝓥⟦ G ⟧ V n
V-dyn {n}{G} rewrite unfold-SafeVal (suc n , size ★)
                   | sym (unfold-SafeVal (n , size G))
    = refl

V-fun : ∀{n}{A B}{N}
   → 𝓥⟦ A ⇒ B ⟧ (ƛ N) n ≡ ∀ W (j : ℕ) → (lt : j ≤ n)
                           → 𝓥⟦ A ⟧ W j
                           → 𝓔⟦ B ⟧ (N [ W ]) j
V-fun {n}{A}{B} rewrite unfold-SafeVal (n , size (A ⇒ B)) = refl

{- Introduction and Elimination for the Logical Relation -}

V-intro : ∀{n}{G}{V}{g}
   → 𝓥⟦ G ⟧ V n
   → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) (suc n)
V-intro {n}{G}{V}{g} Vv rewrite V-dyn {n}{G}{V}{g} = Vv

V-dyn-inv2 : ∀ (V : Term) {n}
   → 𝓥⟦ ★ ⟧ V (suc n)
   → ∃[ V′ ] ∃[ G ] Σ[ g ∈ Ground G ] (V ≡ V′ ⟨ g !⟩) × 𝓥⟦ G ⟧ V′ n
V-dyn-inv2 (ƛ N) {n} Vv rewrite unfold-SafeVal (suc n , size ★) = ⊥-elim Vv
V-dyn-inv2 ($ c) {n} Vv rewrite unfold-SafeVal (suc n , size ★) = ⊥-elim Vv
V-dyn-inv2 ((op-inject {G} g) ⦅ cons (ast V′) nil ⦆) {n} Vv
    rewrite unfold-SafeVal (suc n , size ★) | sym (unfold-SafeVal (n , size G)) =
    V′ , _ , g , refl , Vv
V-dyn-inv2 (` x) {n} Vv rewrite unfold-SafeVal (suc n , 0) = ⊥-elim Vv
V-dyn-inv2 (L · M) {n} Vv rewrite unfold-SafeVal (suc n , 0) = ⊥-elim Vv
V-dyn-inv2 (V ⟨ h ?⟩) {n} Vv rewrite unfold-SafeVal (suc n , 0) = ⊥-elim Vv
V-dyn-inv2 blame {n} Vv rewrite unfold-SafeVal (suc n , 0) = ⊥-elim Vv

V-base-elim : ∀{ι}{V}{j}
   → 𝓥⟦ $ₜ ι ⟧ V j
   → Σ[ c ∈ rep ι ] V ≡ $ c
V-base-elim{ι}{` x}{j} Vv rewrite unfold-SafeVal (j , 0) = ⊥-elim Vv
V-base-elim{ι}{$ c}{j} Vv rewrite unfold-SafeVal (j , 0)
    with Vv
... | refl = c , refl
V-base-elim{ι}{L · M}{j} Vv rewrite unfold-SafeVal (j , 0) = ⊥-elim Vv
V-base-elim{ι}{ƛ N}{j} Vv rewrite unfold-SafeVal (j , 0) = ⊥-elim Vv
V-base-elim{ι}{M ⟨ g !⟩}{j} Vv rewrite unfold-SafeVal (j , 0) = ⊥-elim Vv
V-base-elim{ι}{M ⟨ g ?⟩}{j} Vv rewrite unfold-SafeVal (j , 0) = ⊥-elim Vv
V-base-elim{ι}{blame}{j} Vv rewrite unfold-SafeVal (j , 0) = ⊥-elim Vv

{- Logical Relation contains values -}

𝓥⇒Value : ∀ {A}{k} M → 𝓥⟦ A ⟧ M k → Value M
𝓥⇒Value {★} {k} (` x) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {★} {k} ($ c) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {★} {k} (L · M) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {★} {k} (ƛ N) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {★} {0} (V ⟨ g !⟩) Vv rewrite unfold-SafeVal (0 , 0) = Vv 〈 g 〉
𝓥⇒Value {★} {suc k} ((op-inject {G} g) ⦅ cons (ast V) nil ⦆) Vv rewrite unfold-SafeVal (suc k , 0)
  | sym (unfold-SafeVal (k , size G)) = 𝓥⇒Value V Vv 〈 g 〉
𝓥⇒Value {★} {k} (V ⟨ h ?⟩) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {★} {k} blame Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv

𝓥⇒Value {$ₜ ι} {k} (` x) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {$ₜ ι} {k} ($ c) Vv rewrite unfold-SafeVal (k , 0) = $̬ c
𝓥⇒Value {$ₜ ι} {k} (L · M) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {$ₜ ι} {k} (ƛ N) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {$ₜ ι} {k} (V ⟨ g !⟩) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {$ₜ ι} {k} (M ⟨ h ?⟩) Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv
𝓥⇒Value {$ₜ ι} {k} blame Vv rewrite unfold-SafeVal (k , 0) = ⊥-elim Vv

𝓥⇒Value {A ⇒ B} {k} (` x) Vv rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim Vv
𝓥⇒Value {A ⇒ B} {k} ($ c) Vv rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim Vv
𝓥⇒Value {A ⇒ B} {k} (L · M) Vv rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim Vv
𝓥⇒Value {A ⇒ B} {k} (ƛ N) Vv = ƛ̬ N
𝓥⇒Value {A ⇒ B} {k} (V ⟨ g !⟩) Vv rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim Vv
𝓥⇒Value {A ⇒ B} {k} (V ⟨ h ?⟩) Vv rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim Vv
𝓥⇒Value {A ⇒ B} {k} blame Vv rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim Vv


{- Type Safety -}

𝓖⟦_⟧ : (Γ : List Type) → Subst → ℕ → Set
𝓖⟦ [] ⟧ σ k = ⊤
𝓖⟦ A ∷ Γ ⟧ σ k = 𝓖⟦ Γ ⟧ (λ x → σ (suc x)) k × 𝓥⟦ A ⟧ (σ 0) k

lemma-𝓖 : (Γ : List Type) → (γ : Subst) → (k : ℕ) → 𝓖⟦ Γ ⟧ γ k
  → ∀ {A}{y} → (∋y : Γ ∋ y ⦂ A)
  → 𝓥⟦ A ⟧ (γ y) k
lemma-𝓖 [] γ k 𝓖γ ()
lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {zero} refl = 𝓥γ0
lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {suc y} ∋y =
    lemma-𝓖 Γ (λ x → γ (suc x)) k 𝓖γ ∋y

_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ k (γ : Subst) → 𝓖⟦ Γ ⟧ γ k → 𝓔⟦ A ⟧ (⟪ γ ⟫ M) k

mono-𝓥 : ∀ {j}{k}{A} {V}
   → j ≤′ k
   → 𝓥⟦ A ⟧ V k
   → 𝓥⟦ A ⟧ V j
mono-𝓥 {j} {k} {A} {V} ≤′-refl Vvk = Vvk

mono-𝓥 {j} {suc k} {★} {` x} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk 
mono-𝓥 {j} {suc k} {★} {$ c} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk 
mono-𝓥 {j} {suc k} {★} {L · M} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk 
mono-𝓥 {j} {suc k} {★} {ƛ N} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk
mono-𝓥 {0} {suc k} {★} {(op-inject {G} g) ⦅ cons (ast V) nil ⦆} (≤′-step j≤k) Vvk
    rewrite unfold-SafeVal (0 , 0) | unfold-SafeVal (suc k , 0)
          | sym (unfold-SafeVal (k , size G))
     = 𝓥⇒Value V Vvk
mono-𝓥 {suc j} {suc k} {★} {(op-inject {G} g) ⦅ cons (ast V) nil ⦆} (≤′-step j≤k) Vvk
    rewrite unfold-SafeVal (suc k , 0) | unfold-SafeVal (suc j , 0)
          | sym (unfold-SafeVal (k , size G)) | sym (unfold-SafeVal (j , size G)) =
    mono-𝓥{j}{k} (≤⇒≤′ (≤-trans (n≤1+n j) (≤′⇒≤ j≤k))) Vvk
mono-𝓥 {j} {suc k} {★} {V ⟨ h ?⟩} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {★} {blame} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk

mono-𝓥 {j} {suc k} {$ₜ ι} {` x} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {$ₜ ι} {$ c} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) | unfold-SafeVal (j , 0) = Vvk
mono-𝓥 {j} {suc k} {$ₜ ι} {ƛ N} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {$ₜ ι} {L · M} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {$ₜ ι} {M ⟨ g !⟩} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {$ₜ ι} {M ⟨ h ?⟩} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {$ₜ ι} {blame} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , 0) = ⊥-elim Vvk

mono-𝓥 {j} {suc k} {A ⇒ B} {` x} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , size (A ⇒ B)) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {A ⇒ B} {$ c} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , size (A ⇒ B)) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {A ⇒ B} {ƛ N} (≤′-step j≤k) Vvk
    rewrite unfold-SafeVal (suc k , size (A ⇒ B))
    | unfold-SafeVal (j , size (A ⇒ B))
    = λ W l l≤j VW N′ NW→N′ <l →
      Vvk W l (≤-trans l≤j (≤-trans (≤′⇒≤ j≤k)  (n≤1+n k))) VW N′ NW→N′ <l 
  
mono-𝓥 {j} {suc k} {A ⇒ B} {L · M} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , size (A ⇒ B)) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {A ⇒ B} {V ⟨ g !⟩} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , size (A ⇒ B)) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {A ⇒ B} {V ⟨ h ?⟩} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , size (A ⇒ B)) = ⊥-elim Vvk
mono-𝓥 {j} {suc k} {A ⇒ B} {blame} (≤′-step j≤k) Vvk rewrite unfold-SafeVal (suc k , size (A ⇒ B)) = ⊥-elim Vvk


Val⇒Exp : ∀{A}{V : Term} (k : ℕ)
   → 𝓥⟦ A ⟧ V k
   → 𝓔⟦ A ⟧ V k
Val⇒Exp {A}{V} k Vv N M→N <k
    with value—↠ (𝓥⇒Value V Vv) M→N
... | refl  = inj₁ (mono-𝓥 (≤⇒≤′ (m∸n≤m k (len M→N))) Vv)

dyn? : (A : Type) → A ≡ ★ ⊎ A ≢ ★
dyn? ★ = inj₁ refl
dyn? ($ₜ ι) = inj₂ (λ ())
dyn? (A ⇒ B) = inj₂ (λ ())

ground-or-★ : (A : Type) → A ≡ ★ ⊎ Ground A ⊎ (∃[ G ] GroundOf A G × ¬ Ground A)
ground-or-★ ★ = inj₁ refl
ground-or-★ ($ₜ ι) = inj₂ (inj₁ ($ᵍ ι))
ground-or-★ (A ⇒ B)
    with dyn? A | dyn? B
... | inj₁ refl | inj₁ refl = inj₂ (inj₁ ★⇒★)
... | inj₁ refl | inj₂ neq = inj₂ (inj₂ ((★ ⇒ ★) , gnd-fun ,
                                         λ { ★⇒★ → neq refl}))
... | inj₂ neq | _ = inj₂ (inj₂ (★ ⇒ ★ , gnd-fun , λ { ★⇒★ → neq refl}))

ground-match? : ∀{G} (g : Ground G) (B : Type)
  → B ≢ ★
  → (GroundOf B G) ⊎ (∃[ H ] Ground H × GroundOf B H × G ≢ H)
ground-match? {.($ₜ ι)} ($ᵍ ι) ★ Bnd = ⊥-elim (Bnd refl)
ground-match? {.($ₜ ι)} ($ᵍ ι) ($ₜ ι′) Bnd
    with ι ≡$? ι′
... | yes refl = inj₁ gnd-base
... | no neq = inj₂ (($ₜ ι′) , ($ᵍ ι′) , gnd-base , (λ {refl → neq refl}))
ground-match? {.($ₜ ι)} ($ᵍ ι) (B ⇒ B′) Bnd = inj₂ (★ ⇒ ★ , ★⇒★ , gnd-fun , λ ())
ground-match? {.(★ ⇒ ★)} ★⇒★ ★ Bnd = ⊥-elim (Bnd refl)
ground-match? {.(★ ⇒ ★)} ★⇒★ ($ₜ ι) Bnd = inj₂ ($ₜ ι , $ᵍ ι , gnd-base , λ ())
ground-match? {.(★ ⇒ ★)} ★⇒★ (B ⇒ B′) Bnd = inj₁ gnd-fun

mono-SafeEnv : ∀ j k {Γ} (γ : Subst)
   → j ≤′ k
   → 𝓖⟦ Γ ⟧ γ k
     -----------
   → 𝓖⟦ Γ ⟧ γ j
mono-SafeEnv j k {[]} γ j≤k 𝓖γ = tt
mono-SafeEnv j k {A ∷ Γ} γ j≤k (𝓖γ , 𝓥γ0) = (mono-SafeEnv j k (λ z → γ (suc z)) j≤k 𝓖γ) , (mono-𝓥 j≤k 𝓥γ0)



