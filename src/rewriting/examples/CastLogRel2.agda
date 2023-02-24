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
ValPred (k , s) = (A : Type) → (s ≡ size A) → {V : Term} → Value V → Set

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
V-step (k , .(size ★)) rec ★ refl {.(ƛ N)} (ƛ̬ N) = ⊥
V-step (k , .(size ★)) rec ★ refl {.($ c)} ($̬ c) = ⊥
V-step (zero , .(size ★)) rec ★ refl {.(_ ⟨ g !⟩)} (v 〈 g 〉) = ⊤
V-step (suc k , .(size ★)) rec ★ refl {.(_ ⟨ g !⟩)} (_〈_〉 {V}{G} v g) =
  V-step (k , size G) (<₂-Rec-down (inj₁ (s≤s ≤-refl)) rec) G refl v 

V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl {.(ƛ N)} (ƛ̬ N) = ⊥
V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl {.($ c)} ($̬_ {ι′} c) = ι ≡ ι′
V-step (k , .(size ($ₜ ι))) rec ($ₜ ι) refl {.(_ ⟨ g !⟩)} (v 〈 g 〉) = ⊥

V-step (k , .(size (A ⇒ B))) rec (A ⇒ B) refl {V} v =
   ∀ {W} (w : Value W) (j : ℕ) → (lt : j ≤ k)
         → rec (j , size A) (less-eq-less lt (s≤s (m≤m⊔n (size A) (size B)))) A refl w
         → ∀ N → (VW→N : V · W —↠ N) → (len VW→N < j)
         → (Σ[ v ∈ Value N ]
              rec (j ∸ len VW→N , size B) (less-eq-less (≤-trans (m∸n≤m j (len VW→N)) lt) (s≤s (m≤n⊔m (size A) (size B)))) B refl v)
           ⊎ (∃[ N′ ] (N —→ N′))
           ⊎ N ≡ blame

abstract
  SafeVal : (p : ℕ × ℕ) → ValPred p
  SafeVal = <₂-rec _ (λ i → ValPred i) V-step

𝓥⟦_⟧ : (A : Type) → {V : Term} → Value V → ℕ → Set
𝓥⟦ A ⟧ v k = SafeVal (k , size A) A refl v

𝓔⟦_⟧ : Type → Term → ℕ → Set
𝓔⟦ A ⟧ M k = ∀ N → (M→N : M —↠ N) → (len M→N < k)
              → (Σ[ v ∈ Value N ] 𝓥⟦ A ⟧ v (k ∸ len M→N))
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

{- Equations for the Logical Relattion -}

V-base : ∀{n}{ι}{ι′}{c : rep ι′} → 𝓥⟦ $ₜ ι ⟧ ($̬ c) n ≡ (ι ≡ ι′)
V-base {n} rewrite unfold-SafeVal (n , 0) = refl

V-dyn-zero : ∀{G}{V}{v : Value V}{g : Ground G}
   → 𝓥⟦ ★ ⟧ {V ⟨ g !⟩} (v 〈 g 〉) 0 ≡ ⊤
V-dyn-zero rewrite unfold-SafeVal (0 , size ★) = refl

V-dyn : ∀{n}{G}{V}{v : Value V}{g : Ground G}
     → 𝓥⟦ ★ ⟧ {V ⟨ g !⟩} (v 〈 g 〉) (suc n) ≡ 𝓥⟦ G ⟧ v n
V-dyn {n}{G} rewrite unfold-SafeVal (suc n , size ★)
                   | sym (unfold-SafeVal (n , size G))
    = refl

V-intro : ∀{n}{G}{V}{v : Value V}{g}
     → 𝓥⟦ G ⟧ v n
     → 𝓥⟦ ★ ⟧ {V ⟨ g !⟩} (v 〈 g 〉) (suc n)
V-intro {n}{G}{V}{v}{g} Vv rewrite V-dyn {n}{G}{V}{v}{g} = Vv

V-dyn-inv2 : ∀{V}{v : Value V}{n}
     → 𝓥⟦ ★ ⟧ {V} v (suc n)
     → ∃[ V′ ] ∃[ G ] Σ[ g ∈ Ground G ] (V ≡ V′ ⟨ g !⟩) × Σ[ v′ ∈ Value V′ ] 𝓥⟦ G ⟧ {V′} v′ n
V-dyn-inv2 {.(ƛ N)} {ƛ̬ N} {n} Vv rewrite unfold-SafeVal (suc n , size ★) = ⊥-elim Vv
V-dyn-inv2 {.($ k)} {$̬ k} {n} Vv rewrite unfold-SafeVal (suc n , size ★) = ⊥-elim Vv
V-dyn-inv2 {(V′ ⟨ g !⟩)} {_〈_〉 {G = G} v g } {n} Vv
    rewrite unfold-SafeVal (suc n , size ★) | sym (unfold-SafeVal (n , size G)) =
    V′ , _ , g , refl , v , Vv

V-fun : ∀{n}{A B}{N₁}
  → 𝓥⟦ A ⇒ B ⟧ (ƛ̬ N₁) n ≡ ∀ {W} (w : Value W) (j : ℕ) → (lt : j ≤ n)
                          → 𝓥⟦ A ⟧ w j
                          → 𝓔⟦ B ⟧ ((ƛ N₁) · W) j
V-fun {n}{A}{B} rewrite unfold-SafeVal (n , size (A ⇒ B)) = refl

{- Type Safety -}

{- A substitution whose terms are all values. -}
ValSubst : Set
ValSubst = Σ[ σ ∈ Subst ] (∀ x → Value (σ x))

inc : ValSubst → ValSubst
inc σ = (λ x → proj₁ σ (suc x)) , (λ x → proj₂ σ (suc x))

𝓖⟦_⟧ : (Γ : List Type) → ValSubst → ℕ → Set
𝓖⟦ [] ⟧ σ k = ⊤
𝓖⟦ A ∷ Γ ⟧ σ k = 𝓖⟦ Γ ⟧ (inc σ) k × 𝓥⟦ A ⟧ (proj₂ σ 0) k

lemma-𝓖 : (Γ : List Type) → (γ : ValSubst) → (k : ℕ) → 𝓖⟦ Γ ⟧ γ k
  → ∀ {A}{y} → (∋y : Γ ∋ y ⦂ A)
  → 𝓥⟦ A ⟧ (proj₂ γ y) k
lemma-𝓖 [] γ k 𝓖γ ()
lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {zero} refl = 𝓥γ0
lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {suc y} ∋y =
  lemma-𝓖 Γ (inc γ) k 𝓖γ ∋y

_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ k (γ : ValSubst) → 𝓖⟦ Γ ⟧ γ k → 𝓔⟦ A ⟧ (⟪ proj₁ γ ⟫ M) k

_⊨ⱽ_⦂_ : List Type → {V : Term} → Value V → Type → Set
Γ ⊨ⱽ v ⦂ A = ∀ k (γ : ValSubst) → 𝓖⟦ Γ ⟧ γ k → 𝓥⟦ A ⟧ (sub-val (proj₁ γ) v) k

mono-𝓥 : ∀ {j}{k}{A} {V}{v : Value V}
   → j ≤′ k
   → 𝓥⟦ A ⟧ v k
   → 𝓥⟦ A ⟧ v j
mono-𝓥 j≤k Vvk = {!!}

Val⇒Exp : ∀{A}{V : Term}{v : Value V} (k : ℕ)
   → 𝓥⟦ A ⟧ v k
   → 𝓔⟦ A ⟧ V k
Val⇒Exp {v = v} k Vv N M→N <k
    with value—↠ v M→N
... | refl  = inj₁ (v , mono-𝓥 (≤⇒≤′ (m∸n≤m k (len M→N))) Vv)

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

mono-SafeEnv : ∀ j k {Γ} (γ : ValSubst)
   → j ≤′ k
   → 𝓖⟦ Γ ⟧ γ k
     -----------
   → 𝓖⟦ Γ ⟧ γ j
mono-SafeEnv = {!!}



