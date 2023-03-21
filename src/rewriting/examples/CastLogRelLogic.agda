{-# OPTIONS --without-K --rewriting #-}
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
open import rewriting.examples.StepIndexedLogic

pre-𝓔 : (Type × Term) → Fun (Type × Term) ⊤ Wellfounded DownClosed
pre-𝓔 (A , M) = ∀ᵍ λ N → (index (λ k → Σ[ r ∈ M —↠ N ] len r < k))
                        →ᶠ (irred N)ᶠ
                        →ᶠ ((▷ᶠ (recur (A , N))) ⊎ᶠ (N ≡ blame)ᶠ)

pre-𝓥 : (Type × Term) → Fun (Type × Term) ⊤ Wellfounded DownClosed
pre-𝓥 (★ , op-inject {G} g ⦅ cons (ast V) nil ⦆) =
    (Value V)ᶠ ×ᶠ (▷ᶠ (recur (G , V)))
pre-𝓥 ($ₜ ι , op-lit {ι′} c ⦅ nil ⦆) = (ι ≡ ι′)ᶠ
pre-𝓥 (A ⇒ B , ƛ N) = ∀ᵍ λ W → (▷ᶠ (recur (A , W)) →ᶠ pre-𝓔 (B , N [ W ]))

-- bogus cases for ★
pre-𝓥 (★ , ` x) = (⊥)ᶠ
pre-𝓥 (★ , $ c) = (⊥)ᶠ
pre-𝓥 (★ , ƛ N) = (⊥)ᶠ
pre-𝓥 (★ , L · M) = (⊥)ᶠ
pre-𝓥 (★ , M ⟨ h ?⟩) = (⊥)ᶠ
pre-𝓥 (★ , blame) = (⊥)ᶠ
-- bogus cases for ι
pre-𝓥 ($ₜ ι , ` x) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , ƛ N) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , L · M) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , M ⟨ g !⟩) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , M ⟨ h ?⟩) = (⊥)ᶠ
pre-𝓥 ($ₜ ι , blame) = (⊥)ᶠ
-- bogus cases for A ⇒ B
pre-𝓥 (A ⇒ B , ` x) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , $ c) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , L · M) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , M ⟨ g !⟩) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , M ⟨ h ?⟩) = (⊥)ᶠ
pre-𝓥 (A ⇒ B , blame) = (⊥)ᶠ

𝓥⟦_⟧ : (A : Type) → Term → Setᵒ
𝓥⟦ A ⟧ V = μᶠ (flip pre-𝓥) (A , V)

𝓔⟦_⟧ : (A : Type) → Term → Setᵒ
𝓔⟦ A ⟧ V = fun (pre-𝓔 (A , V)) (μᶠ (flip pre-𝓥)) tt

ee-𝓥 : ∀{A}{V} → ee (𝓥⟦ A ⟧ V)
ee-𝓥 {A}{V} = ee-μᶠ{F = flip pre-𝓥} (A , V)

dc-𝓥 : ∀{A}{V} → dc (𝓥⟦ A ⟧ V)
dc-𝓥 {A}{V} n = dc-μᶠ{F = flip pre-𝓥} n (A , V) 

{- Equations for the Logical Relation -}

V-base : ∀{n}{ι}{ι′}{c : rep ι′}
   → 𝓥⟦ $ₜ ι ⟧ ($ c) (suc n) ≡ (ι ≡ ι′)
V-base {n} = refl

V-dyn : ∀{G}{V}{g : Ground G}
   → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) ≡ᵒ ((Value V)ᵒ ×ᵒ ▷ᵒ (𝓥⟦ G ⟧ V))
V-dyn {G}{V}{g} =
    𝓥⟦ ★ ⟧ (V ⟨ g !⟩)             ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
    μᶠ (flip pre-𝓥) (★ , V ⟨ g !⟩)
                              ≡ᵒ⟨ fixpointᵒ{v = (★ , V ⟨ g !⟩)} (flip pre-𝓥) ⟩
    fun (flip pre-𝓥) (μᶠ (flip pre-𝓥)) (★ , V ⟨ g !⟩) ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
    (Value V)ᵒ ×ᵒ (▷ᵒ 𝓥⟦ G ⟧ V)
    QEDᵒ 

V-fun : ∀{A B}{N}
   → 𝓥⟦ A ⇒ B ⟧ (ƛ N) ≡ᵒ ∀ᵒ λ W → (▷ᵒ 𝓥⟦ A ⟧ W) →ᵒ (𝓔⟦ B ⟧ (N [ W ]))
V-fun {A}{B}{N} = 
    𝓥⟦ A ⇒ B ⟧ (ƛ N)                     ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
    μᶠ (flip pre-𝓥) (A ⇒ B , ƛ N)
                                ≡ᵒ⟨ fixpointᵒ{v = (A ⇒ B , ƛ N)} (flip pre-𝓥) ⟩
    fun (flip pre-𝓥) (μᶠ (flip pre-𝓥)) (A ⇒ B , ƛ N) ≡ᵒ⟨ ≡ᵒ-refl refl ⟩
    (∀ᵒ λ W → (▷ᵒ 𝓥⟦ A ⟧ W) →ᵒ (𝓔⟦ B ⟧ (N [ W ])))
    QEDᵒ

{- Logical Relation (above zero) contains values -}

𝓥⇒Value : ∀ {A}{k} M → 𝓥⟦ A ⟧ M (suc k) → Value M
𝓥⇒Value {★} {k} (op-inject {G} g ⦅ cons (ast M) nil ⦆) 𝓥Mg =
   let vM = proj₁ (proj₁ (V-dyn {G}{M}{g} (suc k)) 𝓥Mg) in
     -- proj₁ ((proj₁ (V-dyn {G}{M}{g} (suc k)) 𝓥Mg) (suc k) ≤-refl) in
   vM 〈 g 〉
𝓥⇒Value {$ₜ ι} {k} (op-lit {ι′} c ⦅ nil ⦆) 𝓥M = $̬ c
𝓥⇒Value {A ⇒ B} {k} (ƛ N) 𝓥ƛN = ƛ̬ N
-- bogus cases
𝓥⇒Value {★} {k} (` x) 𝓥x = ⊥-elim 𝓥x
𝓥⇒Value {★} {k} ($ c) 𝓥c = ⊥-elim 𝓥c
𝓥⇒Value {★} {k} (ƛ N) 𝓥ƛN = ⊥-elim 𝓥ƛN
𝓥⇒Value {★} {k} (L · M) 𝓥L·M = ⊥-elim 𝓥L·M
𝓥⇒Value {★} {k} (M ⟨ h ?⟩) 𝓥Mh = ⊥-elim 𝓥Mh
𝓥⇒Value {★} {k} blame 𝓥blame = ⊥-elim 𝓥blame
𝓥⇒Value {$ₜ ι} {k} (` x) 𝓥x = ⊥-elim 𝓥x
𝓥⇒Value {$ₜ ι} {k} (ƛ N) 𝓥ƛN = ⊥-elim 𝓥ƛN
𝓥⇒Value {$ₜ ι} {k} (L · M) 𝓥L·M = ⊥-elim 𝓥L·M
𝓥⇒Value {$ₜ ι} {k} (M ⟨ g !⟩) 𝓥Mg = ⊥-elim 𝓥Mg
𝓥⇒Value {$ₜ ι} {k} (M ⟨ h ?⟩) 𝓥Mh = ⊥-elim 𝓥Mh
𝓥⇒Value {$ₜ ι} {k} blame 𝓥blame = ⊥-elim 𝓥blame
𝓥⇒Value {A ⇒ B} {k} (` x) 𝓥x = ⊥-elim 𝓥x
𝓥⇒Value {A ⇒ B} {k} ($ c) 𝓥c = ⊥-elim 𝓥c
𝓥⇒Value {A ⇒ B} {k} (L · M) 𝓥L·M = ⊥-elim 𝓥L·M
𝓥⇒Value {A ⇒ B} {k} (M ⟨ g !⟩) 𝓥Mg = ⊥-elim 𝓥Mg
𝓥⇒Value {A ⇒ B} {k} (M ⟨ h ?⟩) 𝓥Mh = ⊥-elim 𝓥Mh
𝓥⇒Value {A ⇒ B} {k} blame 𝓥blame = ⊥-elim 𝓥blame

{- Semantic Type Safety -}

𝓖⟦_⟧ : (Γ : List Type) → Subst → Setᵒ
𝓖⟦ [] ⟧ σ = ⊤ᵒ
𝓖⟦ A ∷ Γ ⟧ σ = 𝓖⟦ Γ ⟧ (λ x → σ (suc x)) ×ᵒ (𝓥⟦ A ⟧ (σ 0))

lemma-𝓖 : (Γ : List Type) → (γ : Subst) → (k : ℕ) → 𝓖⟦ Γ ⟧ γ k
  → ∀ {A}{y} → (∋y : Γ ∋ y ⦂ A)
  → 𝓥⟦ A ⟧ (γ y) k
lemma-𝓖 [] γ k 𝓖γ ()
lemma-𝓖 (A ∷ Γ) γ zero 𝓖⟦A∷Γ⟧γk {.A} {zero} refl = ee-𝓥 {A}{γ 0}
lemma-𝓖 (A ∷ Γ) γ (suc k) (𝓖γ , 𝓥γ0) {.A} {zero} refl = 𝓥γ0
lemma-𝓖 (A ∷ Γ) γ zero 𝓖γ {B} {suc y} ∋y = ee-𝓥 {B}{γ (suc y)}
lemma-𝓖 (A ∷ Γ) γ (suc k) (𝓖γ , 𝓥γ0) {B} {suc y} ∋y =
    lemma-𝓖 Γ (λ x → γ (suc x)) (suc k) 𝓖γ ∋y

_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ k (γ : Subst) → 𝓖⟦ Γ ⟧ γ k → 𝓔⟦ A ⟧ (⟪ γ ⟫ M) k

Val⇒Exp : ∀{A}{V : Term} (k : ℕ)
   → 𝓥⟦ A ⟧ V k
   → 𝓔⟦ A ⟧ V k
Val⇒Exp {A} {V} k Vv N zero j≤k x .zero z≤n x₂ .zero z≤n = inj₂ tt
Val⇒Exp {A} {V} (suc k) Vv N (suc j) (s≤s j≤k) (V—↠N , VN<1+j) i i≤1+j irN zero l≤i = inj₂ tt
Val⇒Exp {A} {V} (suc k) Vv N (suc j) (s≤s j≤k) (V—↠N , VN<1+j) (suc i)
    (s≤s i≤j) irN (suc l) (s≤s l≤i) 
    with value—↠ (𝓥⇒Value{A} V Vv) V—↠N
... | refl =
    inj₁ λ {m (s≤s m≤l) → dc-𝓥{A}{V} (suc k) Vv m
             (≤-trans m≤l (≤-trans l≤i (≤-trans i≤j (≤-trans j≤k (n≤1+n k)))))}

dc-SafeEnv : ∀ j k {Γ} (γ : Subst)
   → j ≤ k
   → 𝓖⟦ Γ ⟧ γ k
     -----------
   → 𝓖⟦ Γ ⟧ γ j
dc-SafeEnv j k {[]} γ j≤k 𝓖γ = tt
dc-SafeEnv j k {A ∷ Γ} γ j≤k (𝓖γ , 𝓥γ0) =
  (dc-SafeEnv j k {Γ} (λ z → γ (suc z)) j≤k 𝓖γ)
  , dc-𝓥{A}{γ 0} k 𝓥γ0 j j≤k
