{-# OPTIONS --without-K --rewriting #-}

{-
 Based on the development of Logical step-indexed logical relation
 by Philip Wadler (June 1, 2022)

 Also based on "An Indexed Model of Recursive Types"
 by Appel and McAllester.
-}
module rewriting.examples.StepIndexedLogic where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; s≤s-injective; ≤⇒≤′; ≤′⇒≤; n≤1+n)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)

Setᵒ : Set₁
Setᵒ = ℕ → Set

⊥ᵒ : Setᵒ
⊥ᵒ zero     =  ⊤
⊥ᵒ (suc n)  =  ⊥

⊤ᵒ : Setᵒ
⊤ᵒ n  =  ⊤

infixr 7 _×ᵒ_
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
(P ×ᵒ Q) n  = ∀ k → k ≤ n → (P k) × (Q k)

infixr 7 _⊎ᵒ_
_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
(P ⊎ᵒ Q) n  = ∀ k → k < n → (P k) ⊎ (Q k)

infixr 6 _→ᵒ_
_→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
(P →ᵒ Q) n  = ∀ k → k ≤ n → P k → Q k

∀ᵒ : ∀{A} → (A → Setᵒ) → Setᵒ
∀ᵒ {A} F n = ∀ (v : A) → F v n

infixr 8 _ᵒ
_ᵒ  : Set → Setᵒ
(p ᵒ) zero = ⊤
(p ᵒ) (suc n) = p

▷ᵒ_ : Setᵒ → Setᵒ
(▷ᵒ P) n =  ∀ k → k < n → P k

iter : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → (A → A)
iter zero    F  =  id
iter (suc n) F  =  F ∘ iter n F

iter-subtract : ∀{ℓ}{A : Set ℓ}{P : A}
  → (F : A → A)
  → (j k : ℕ)
  → j ≤ k
  → iter j F (iter (k ∸ j) F P) ≡ iter k F P
iter-subtract {A = A} {P} F .zero k z≤n = refl
iter-subtract {A = A} {P} F (suc j) (suc k) (s≤s j≤k)
  rewrite iter-subtract{A = A}{P} F j k j≤k = refl

Predᵒ : Set → Set₁
Predᵒ A = A → Setᵒ

⊤ᵖ : ∀{A} → Predᵒ A
⊤ᵖ x = ⊤ᵒ

⊥ᵖ : ∀{A} → Predᵒ A
⊥ᵖ x = ⊥ᵒ

μᵖ : ∀ {A} → (Predᵒ A → Predᵒ A) → Predᵒ A
(μᵖ F) x k  = iter (suc k) F ⊤ᵖ x k

-- Lobᵒ : ∀{P : Setᵒ}
--    → (∀ k → (▷ᵒ P) k → P k)
--      ----------------------
--    → ∀ k → P k
-- Lobᵒ {P} ▷P→P zero = ▷P→P zero tt
-- Lobᵒ {P} ▷P→P (suc k) = ▷P→P (suc k) (Lobᵒ ▷P→P k)

{------------------- Eventually true at 0 --------------------}

ee : Setᵒ → Set
ee P  =  P zero

ee-⊥ : ee ⊥ᵒ
ee-⊥ = tt

ee-⊤ : ee ⊤ᵒ
ee-⊤ = tt

ee-× : ∀ {P Q} → ee P → ee Q → ee (P ×ᵒ Q)
ee-× P0 Q0 .zero z≤n = P0 , Q0

ee-⊎ : ∀ {P Q} → ee P → ee Q → ee (P ⊎ᵒ Q)
ee-⊎ P0 Q0 k ()

ee-→ : ∀ {P Q} → ee Q → ee (P →ᵒ Q)
ee-→ eeQ .zero z≤n Pz = eeQ

ee-∀ : ∀{A F}
   → (∀ v → ee (F v))
   → ee (∀ᵒ {A} F)
ee-∀ {F} eeF v = eeF v

ee-Pᵒ : (P : Set)
   → ee (P ᵒ)
ee-Pᵒ P = tt

eeᵖ : ∀{A} → Predᵒ A → Set
eeᵖ P = ∀ x → P x 0

{- the following lemma is currently unused -}
ee-iter : ∀{A}
    (i : ℕ)
  → (F : Predᵒ A → Predᵒ A)
  → (∀ p → eeᵖ p → eeᵖ (F p)) 
  → eeᵖ (iter i F ⊤ᵖ)
ee-iter zero F eeF x = tt
ee-iter (suc i) F eeF =
  eeF (iter i F (λ x x₁ → ⊤)) (ee-iter i F eeF)

ee-μ : ∀{A}{F : Predᵒ A → Predᵒ A}
   → (∀ p → eeᵖ p → eeᵖ (F p)) 
   → eeᵖ (μᵖ F)
ee-μ {A}{F} eeF x = eeF (λ _ _ → ⊤) (λ x → tt) x  

{------------------- Downward Closed --------------------}

dc : Setᵒ → Set
dc P  =  ∀ n → P n → ∀ k → k ≤ n → P k

dc-⊥ : dc ⊥ᵒ
dc-⊥ zero tt k z≤n  =   tt
dc-⊥ (suc n) ()

dc-⊤ : dc ⊤ᵒ
dc-⊤  =  λ n ⊤ᵒn k k≤n → tt

dc-× : ∀ {P Q} → dc P → dc Q → dc (P ×ᵒ Q)
dc-× dcP dcQ n P×Q k x₁ j x₂ = P×Q j (≤-trans x₂ x₁) 

dc-⊎ : ∀ {P Q} → dc P → dc Q → dc (P ⊎ᵒ Q)
dc-⊎ dcP dcQ n P⊎Q k x j y = P⊎Q j (≤-trans y x)

dc-→ᵒ : ∀ {P Q} → dc (P →ᵒ Q)
dc-→ᵒ n [P→ᵒQ]n k k≤n i i≤k Pi = [P→ᵒQ]n i (≤-trans i≤k k≤n) Pi

dc-∀ : ∀{A F}
  → (∀ v → dc (F v))
  → dc (∀ᵒ {A} F)
dc-∀ {A}{F} dcF n ∀Fn k k≤n v = dcF v n (∀Fn v) k k≤n

dc-Pᵒ : (P : Set)
   → dc (P ᵒ)
dc-Pᵒ P n Pn zero k≤n = tt
dc-Pᵒ P (suc n) Pn (suc k) (s≤s k≤n) = Pn

_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) × (Q → P)

⇔-trans : ∀{P Q R : Set}
  → P ⇔ Q
  → Q ⇔ R
    ------
  → P ⇔ R
⇔-trans PQ QR =
    (λ z → proj₁ QR (proj₁ PQ z)) , (λ z → proj₂ PQ (proj₂ QR z))  

infixr 2 _⇔⟨_⟩_
infix  3 _QED
  
_⇔⟨_⟩_ : 
    (P : Set)
  → ∀{Q} → P ⇔ Q
  → ∀{R} → Q ⇔ R
    -------------
  → P ⇔ R
P ⇔⟨ PQ ⟩ QR = ⇔-trans PQ QR

_QED :
    (P : Set)
    ---------
  → P ⇔ P
P QED = (λ x → x) , (λ x → x)

×-cong-⇔ : ∀{S S′ T T′}
   → S ⇔ S′
   → T ⇔ T′
     -------------------
   → (S × T) ⇔ (S′ × T′)
×-cong-⇔ SS′ TT′ = (λ x → (proj₁ SS′ (proj₁ x)) , (proj₁ TT′ (proj₂ x)))
                  , (λ x → (proj₂ SS′ (proj₁ x)) , (proj₂ TT′ (proj₂ x)))

monotonic : ∀{A} (F : Predᵒ A → Predᵒ A) → Set₁
monotonic F = ∀ {P}{Q} → (∀ x i → (P x) i → (Q x) i)
                       → (∀ x i → (F P x) i → (F Q x) i)

dcᵖ : ∀{A} → Predᵒ A → Set
dcᵖ P = ∀ n x → P x n → ∀ k → k ≤ n → P x k

dc-iter-aux : ∀(i : ℕ){A}
   → (F : Predᵒ A → Predᵒ A)
   → (∀ p → dcᵖ p → dcᵖ (F p))
   → dcᵖ (iter i F ⊤ᵖ)
dc-iter-aux zero F dcF = λ n x _ k _ → tt
dc-iter-aux (suc i) F dcF =
  let IH = dc-iter-aux i F dcF in
  dcF (iter i F ⊤ᵖ) IH

dc-iter : ∀(i : ℕ){A}{F : Predᵒ A → Predᵒ A}{x}
   → monotonic F
   → dc (λ k → iter k F ⊤ᵖ x i)
dc-iter i {A}{F}{x} mf k Fki j j≤k = lemma′ i j k mf (≤⇒≤′ j≤k) Fki
   where
   lemma′ : ∀(i j k : ℕ){A}{F : Predᵒ A → Predᵒ A}{x}
       → monotonic F
       → j ≤′ k → iter k F ⊤ᵖ x i → iter j F ⊤ᵖ x i
   lemma′ i j .j mF _≤′_.≤′-refl iter-k = iter-k
   lemma′ i zero (suc k) mF (≤′-step j≤k) iter-k = tt
   lemma′ i (suc j) (suc k) {A}{F}{x} mF (≤′-step j≤k) iter-k =
        mF IH x i iter-k
        where
        IH : (x₂ : A) (i₂ : ℕ) → iter k F ⊤ᵖ x₂ i₂ → iter j F ⊤ᵖ x₂ i₂
        IH x′ i′ iterki′ = lemma′ i′ j k mF
                              (≤⇒≤′ (≤-trans (n≤1+n j) (≤′⇒≤ j≤k))) iterki′

{-
  It seems that monotonic is too strong a requirement.
  Having trouble with some contravariance in trying to
  prove that pre-𝓥 is monotonic.
-}

-- dc-μ : ∀{A}{F : Predᵒ A → Predᵒ A}
--    → monotonic F
--    → (∀ p → dcᵖ p → dcᵖ (F p))
--    → dcᵖ (μᵖ F) 
-- dc-μ {A}{F} mF dcF n x μFxn k k≤n = {!!}
  -- let iternk = dc-iter-aux n F dcF n x μFxn k k≤n in
  -- dc-iter k mF n iternk k k≤n

{------------------- well founded and nonexpansive --------------------}

↓ᵒ : ℕ → Setᵒ → Setᵒ
↓ᵒ k S j = j < k  ×  S j

_≡ᵒ_ : Setᵒ → Setᵒ → Set
S ≡ᵒ T = ∀ i → S i ⇔ T i

≡ᵒ-refl : ∀{S T : Setᵒ}
  → S ≡ T
  → S ≡ᵒ T
≡ᵒ-refl refl i = (λ x → x) , (λ x → x)

≡ᵒ-sym : ∀{S T : Setᵒ}
  → S ≡ᵒ T
  → T ≡ᵒ S
≡ᵒ-sym ST i = (proj₂ (ST i)) , (proj₁ (ST i))

≡ᵒ-trans : ∀{S T R : Setᵒ}
  → S ≡ᵒ T
  → T ≡ᵒ R
  → S ≡ᵒ R
≡ᵒ-trans ST TR i = (λ z → proj₁ (TR i) (proj₁ (ST i) z))
                 , (λ z → proj₂ (ST i) (proj₂ (TR i) z))

↓ᵖ : ℕ → ∀{A} → Predᵒ A → Predᵒ A
↓ᵖ k P x = ↓ᵒ k (P x)

infixr 7 _×ᵖ_
_×ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
(P ×ᵖ Q) v  =  (P v) ×ᵒ (Q v)

infixr 7 _⊎ᵖ_
_⊎ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
(P ⊎ᵖ Q) v  =  (P v) ⊎ᵒ (Q v)

infixr 6 _→ᵖ_
_→ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
(P →ᵖ Q) v = P v →ᵒ Q v

▷ᵖ : ∀{A} → Predᵒ A → Predᵒ A
▷ᵖ P v = ▷ᵒ (P v)

∀ᵖ : ∀{A : Set}{B} → (A → Predᵒ B) → Predᵒ B
∀ᵖ {A} F x = ∀ᵒ(λ v → F v x)

infix 2 _≡ᵖ_
_≡ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Set
P ≡ᵖ Q = ∀ x → P x ≡ᵒ Q x

≡ᵖ-refl : ∀{A}{P Q : Predᵒ A}
  → P ≡ Q
  → P ≡ᵖ Q
≡ᵖ-refl refl x = (≡ᵒ-refl refl)

≡ᵖ-sym : ∀{A}{P Q : Predᵒ A}
  → P ≡ᵖ Q
  → Q ≡ᵖ P
≡ᵖ-sym PQ x = (≡ᵒ-sym (PQ x))
  
≡ᵖ-trans : ∀{A}{P Q R : Predᵒ A}
  → P ≡ᵖ Q
  → Q ≡ᵖ R
  → P ≡ᵖ R
≡ᵖ-trans{A}{P}{Q}{R} PQ QP x = ≡ᵒ-trans{T = Q x} (PQ x) (QP x)

infixr 2 _≡ᵖ⟨_⟩_
infix  3 _QEDᵖ
  
_≡ᵖ⟨_⟩_ : ∀{A}
  → (P : Predᵒ A)
  → ∀{Q} → P ≡ᵖ Q
  → ∀{R} → Q ≡ᵖ R
  → P ≡ᵖ R
P ≡ᵖ⟨ P≡Q ⟩ Q≡R = ≡ᵖ-trans P≡Q Q≡R

_QEDᵖ : ∀{A}
  → (P : Predᵒ A)
  → P ≡ᵖ P
P QEDᵖ = ≡ᵖ-refl refl

extensionalᵖ : ∀{A} (F : Predᵒ A → Predᵒ A) → Set₁
extensionalᵖ F = ∀{P}{Q} → P ≡ᵖ Q → F P ≡ᵖ F Q

-- ≡ᵖ-cong : ∀{A}{P Q : Predᵒ A}
--   → (F : Predᵒ A → Predᵒ A)
--   → P ≡ᵖ Q
--   → F P ≡ᵖ F Q
-- ≡ᵖ-cong F PQ x i = (λ FP → {!!}) , λ FQ → {!!}

ext-↓ : ∀{A}
    (k : ℕ)
  → extensionalᵖ{A} (↓ᵖ k)
ext-↓ k PQ x i = (λ { (fst , snd) → fst , proj₁ (PQ x i) snd})
                , λ { (fst , snd) → fst , proj₂ (PQ x i) snd}

{-

Nonexpansive means that you only need k steps of the input to get k
steps of the output. This is related to continuity.

-}
nonexpansive : ∀{A} → (Predᵒ A → Predᵒ A) → Set₁
nonexpansive F = ∀ P k → (↓ᵖ k (F P)) ≡ᵖ (↓ᵖ k (F (↓ᵖ k P)))

wellfounded : ∀{A} → (Predᵒ A → Predᵒ A) → Set₁
wellfounded F = ∀ P k → (↓ᵖ (suc k) (F P)) ≡ᵖ (↓ᵖ (suc k) (F (↓ᵖ k P)))

down-eq : ∀{A}{P : Predᵒ A}{x}
   → (i : ℕ)
   → (↓ᵖ (suc i) P x i) ⇔ (P x i)
down-eq {A}{P}{x} zero = (λ x₁ → proj₂ x₁) , (λ x₁ → s≤s z≤n , x₁)
down-eq {A}{P}{x} (suc i) = (λ x₁ → proj₂ x₁) , (λ x₁ → s≤s (s≤s ≤-refl) , x₁)

equiv-down : ∀{A}{P Q : Predᵒ A}
   → (∀ k → ↓ᵖ k P ≡ᵖ ↓ᵖ k Q)
   → P ≡ᵖ Q
equiv-down{A}{P}{Q} dPQ x i =
    (λ Pxi → let dP→dQ = proj₁ (dPQ (suc i) x i) in
             let dQ = dP→dQ (proj₂ (down-eq{A}{P} i) Pxi) in
             let Qxi = proj₁ (down-eq{A}{Q} i) dQ in
             Qxi)
   , (λ Qxi → let dQ→dP = proj₂ (dPQ (suc i) x i) in
             let dP = dQ→dP (proj₂ (down-eq{A}{Q} i) Qxi) in
             let Pxi = proj₁ (down-eq{A}{P} i) dP in
             Pxi)

down-equiv : ∀{A}{P Q : Predᵒ A}
  → P ≡ᵖ Q
  → (∀ k → ↓ᵖ k P ≡ᵖ ↓ᵖ k Q)
down-equiv P≡Q k x i = (λ { (fst , snd) → fst , proj₁ (P≡Q x i) snd})
    , λ { (fst , snd) → fst , proj₂ (P≡Q x i) snd}

{-
  Does wellfounded imply extensional?
  I don't think so.
-}
-- wff⇒ext : ∀{A}
--    → (F : Predᵒ A → Predᵒ A)
--    → wellfounded F
--    → extensionalᵖ F
-- wff⇒ext{A} F wfF {P}{Q} P≡Q = equiv-down {!!}
--   where
--   Goal : (k : ℕ) → ↓ᵖ k (F P) ≡ᵖ ↓ᵖ k (F Q)
--   Goal zero x i = (λ { ()}) , λ { ()}
--   Goal (suc k) = {!!}
--     where
--     IH : ↓ᵖ k (F P) ≡ᵖ ↓ᵖ k (F Q)
--     IH = Goal k
--     X : ↓ᵖ (suc k) (F P) ≡ᵖ ↓ᵖ (suc k) (F (↓ᵖ k P))
--     X = wfF P k
--     Ya : (↓ᵖ k P) ≡ᵖ (↓ᵖ k Q)
--     Ya = down-equiv P≡Q k
--     Y : ↓ᵖ (suc k) (F (↓ᵖ k P)) ≡ᵖ ↓ᵖ (suc k) (F (↓ᵖ k Q))
--     Y = {!!}

  {- wellfounded F = ∀ P k → (↓ᵖ (suc k) (F P)) ≡ᵖ (↓ᵖ (suc k) (F (↓ᵖ k P)))
  
    ↓ᵖ (suc k) (F P)
    =  wfF
    (↓ᵖ (suc k) (F (↓ᵖ k P)))
    = doh, need extensionality for this step
    (↓ᵖ (suc k) (F (↓ᵖ k Q)))
    = wfF
    ↓ᵖ (suc k) (F Q)

   Goal: ↓ᵖ (suc k) (F P) ≡ᵖ ↓ᵖ (suc k) (F Q)
   -}


lemma15a : ∀{A}{P Q : Predᵒ A}{j}
  → (F : Predᵒ A → Predᵒ A)
  → wellfounded F
  → extensionalᵖ F
  → ↓ᵖ j (iter j F P) ≡ᵖ ↓ᵖ j (iter j F Q)
lemma15a {A} {P} {Q} {zero} F wfF extF x i = (λ { ()}) , λ { ()}
lemma15a {A} {P} {Q} {suc j} F wfF extF =
    ↓ᵖ (suc j) (F (iter j F P))
  ≡ᵖ⟨ wfF (iter j F P) j  ⟩ 
    ↓ᵖ (suc j) (F (↓ᵖ j (iter j F P)))
  ≡ᵖ⟨ ext-↓ {A} (suc j) (extF (lemma15a{A}{P}{Q} {j = j} F wfF extF)) ⟩
    ↓ᵖ (suc j) (F (↓ᵖ j (iter j F Q)))
  ≡ᵖ⟨ ≡ᵖ-sym (wfF (iter j F Q) j) ⟩
    ↓ᵖ (suc j) (F (iter j F Q))
  QEDᵖ

lemma15b : ∀{A}{P : Predᵒ A}{j k}
  → (F : Predᵒ A → Predᵒ A)
  → wellfounded F
  → extensionalᵖ F
  → j ≤ k
  → ↓ᵖ j (iter j F P) ≡ᵖ ↓ᵖ j (iter k F P)
lemma15b{A}{P}{j}{k} F wfF extF j≤k =
    let eq = lemma15a {A}{P}{iter (k ∸ j) F P}{j} F wfF extF in
    ≡ᵖ-trans eq (ext-↓ j (≡ᵖ-refl Goal))
    where
    Goal : (λ z z₁ → iter j F (iter (k ∸ j) F P) z z₁)
           ≡ (λ z z₁ → iter k F P z z₁)
    Goal rewrite iter-subtract{A = Predᵒ A}{P} F j k j≤k = refl

substᵖ : ∀{A}{P Q : Predᵒ A}{x}
  → P ≡ᵖ Q
  → (i : ℕ)
  → P x i
  → Q x i
substᵖ {x = x} PQ i P = proj₁ (PQ x i) P

dc-μ : ∀{A}{F : Predᵒ A → Predᵒ A}
   → wellfounded F
   → extensionalᵖ F
   → (∀ p → dcᵖ p → dcᵖ (F p))
   → dcᵖ (μᵖ F) 
dc-μ {A}{F} wfF extF dcF k v μFvk j j≤k = T
   where
   X : iter (suc k) F ⊤ᵖ v k
   X = μFvk
   Y : iter (suc k) F ⊤ᵖ v j
   Y = dc-iter-aux (suc k) F dcF k v X j j≤k
   Z : ↓ᵖ (suc j) (iter (suc k) F ⊤ᵖ) v j
   Z = ≤-refl , Y
   W : ↓ᵖ (suc j) (iter (suc j) F ⊤ᵖ) v j
   W = let eq = lemma15b{A}{⊤ᵖ}{suc j}{suc k} F wfF extF (s≤s j≤k)
       in substᵖ (≡ᵖ-sym eq) j Z
   T : (iter (suc j) F ⊤ᵖ) v j
   T = proj₂ W

{- ↓ᵖ is idempotent -}
lemma17 : ∀{A}{P : Predᵒ A}
   → (k : ℕ)
   → ↓ᵖ k (↓ᵖ (suc k) P) ≡ᵖ ↓ᵖ k P
lemma17{A}{P} k x i =
    (λ { (fst , snd) → fst , proj₂ snd})
    , λ { (fst , snd) → fst , ((≤-trans fst (n≤1+n k)) , snd)}

lemma18a : ∀{A}
   → (k : ℕ)
   → (F : Predᵒ A → Predᵒ A)
   → wellfounded F
   → extensionalᵖ F
   → ↓ᵖ k (μᵖ F) ≡ᵖ ↓ᵖ k (iter k F ⊤ᵖ)
lemma18a zero F wfF extF x i = (λ { (() , b)}) , (λ { (() , b)})
lemma18a (suc k′) F wfF extF v j =
      let k = suc k′ in
      ↓ᵖ k (μᵖ F) v j                                ⇔⟨ EQ1 ⟩ 
      (j < k  ×  μᵖ F v j)                           ⇔⟨ EQ2 ⟩ 
      (j < k  ×  iter (suc j) F ⊤ᵖ v j)              ⇔⟨ EQ3 ⟩ 
      (j < k  ×  ↓ᵖ (suc j) (iter (suc j) F ⊤ᵖ) v j) ⇔⟨ EQ4 ⟩
      (j < k  ×  ↓ᵖ (suc j) (iter k F ⊤ᵖ) v j)       ⇔⟨ EQ5 ⟩
      (j < k  ×  iter k F ⊤ᵖ v j)                    ⇔⟨ EQ6 ⟩ 
      ↓ᵖ k (iter k F ⊤ᵖ) v j
    QED
    where
      EQ1 = (λ {(a , b) → a , b}) , (λ {(a , b) → a , b})
      EQ2 = (λ {(a , b) → a , b}) , (λ {(a , b) → a , b})
      EQ3 = (λ {(a , b) → a , ≤-refl , b})
          , (λ {(s≤s a , (b , c)) → s≤s a , c})
      EQ4 = (λ{(a , b) → a ,
              proj₁ (lemma15b {j = suc j}{k = suc k′} F wfF extF a v j) b})
          , (λ{(a , b) → a ,
              proj₂ (lemma15b {j = suc j}{k = suc k′} F wfF extF a v j) b})
      EQ5 = (λ {(a , b) → a , (proj₂ b)}) , λ {(a , b) → a , (≤-refl , b)}
      EQ6 = (λ {(a , b) → a , b}) , λ z → z

lemma18b : ∀{A}
   → (k : ℕ)
   → (F : Predᵒ A → Predᵒ A)
   → wellfounded F
   → extensionalᵖ F
   → ↓ᵖ (suc k) (F (μᵖ F)) ≡ᵖ ↓ᵖ (suc k) (iter (suc k) F ⊤ᵖ)
lemma18b {A} k F wfF extF =
      ↓ᵖ (suc k) (F (μᵖ F))                ≡ᵖ⟨ wfF _ k ⟩
      ↓ᵖ (suc k) (F (↓ᵖ k (μᵖ F)))         ≡ᵖ⟨ ext-↓ (suc k)
                                               (extF (lemma18a k F wfF extF)) ⟩
      ↓ᵖ (suc k) (F (↓ᵖ k (iter k F ⊤ᵖ)))  ≡ᵖ⟨ ≡ᵖ-sym (wfF _ k) ⟩
      ↓ᵖ (suc k) (F (iter k F ⊤ᵖ))         ≡ᵖ⟨ ≡ᵖ-refl refl ⟩
      ↓ᵖ (suc k) (iter (suc k) F ⊤ᵖ)
    QEDᵖ

lemma19 : ∀{A}
   → (k : ℕ)
   → (F : Predᵒ A → Predᵒ A)
   → wellfounded F
   → extensionalᵖ F
   → ↓ᵖ k (μᵖ F) ≡ᵖ ↓ᵖ k (F (μᵖ F))
lemma19 {A} k F wfF extF =
      ↓ᵖ k (μᵖ F)                    ≡ᵖ⟨ lemma18a k F wfF extF ⟩
      ↓ᵖ k (iter k F ⊤ᵖ)             ≡ᵖ⟨ lemma15b{j = k}{suc k} F wfF extF
                                              (n≤1+n k) ⟩
      ↓ᵖ k (iter (suc k) F ⊤ᵖ)              ≡ᵖ⟨ ≡ᵖ-sym (lemma17 {P = iter (suc k) F ⊤ᵖ} k) ⟩
      ↓ᵖ k (↓ᵖ (suc k) (iter (suc k) F ⊤ᵖ)) ≡ᵖ⟨ ext-↓ k (≡ᵖ-sym (lemma18b k F wfF extF)) ⟩
      ↓ᵖ k (↓ᵖ (suc k) (F (μᵖ F)))          ≡ᵖ⟨ lemma17 k ⟩
      ↓ᵖ k (F (μᵖ F))
    QEDᵖ

theorem20 : ∀{A}
   → (F : Predᵒ A → Predᵒ A)
   → wellfounded F
   → extensionalᵖ F
   → μᵖ F ≡ᵖ F (μᵖ F)
theorem20 F wfF extF = equiv-down (λ k → lemma19 k F wfF extF)


nonexpansive-id : ∀{A}
   → nonexpansive{A} (λ P → P)
nonexpansive-id{A} Q k x i =
    (λ { (fst , snd) → fst , fst , snd})
    , (λ { (fst , snd) → fst , proj₂ snd})

nonexpansive-const : ∀{A}{P : Predᵒ A}
   → nonexpansive{A} (λ Q → P)
nonexpansive-const {A}{P} Q k = ≡ᵖ-refl refl

wellfounded⇒nonexpansive : ∀{A}
   → (F : Predᵒ A → Predᵒ A)
   → wellfounded F
   → extensionalᵖ F
   → nonexpansive F
wellfounded⇒nonexpansive F wfF extF P zero v i = (λ {()}) , λ { ()}
wellfounded⇒nonexpansive F wfF extF P (suc k) =
    ↓ᵖ (suc k) (F P)                       ≡ᵖ⟨ wfF _ k ⟩
    ↓ᵖ (suc k) (F (↓ᵖ k P))                ≡ᵖ⟨ ext-↓ (suc k) (extF (≡ᵖ-sym
                                                                 (lemma17 k))) ⟩
    ↓ᵖ (suc k) (F (↓ᵖ k (↓ᵖ (suc k) P)))   ≡ᵖ⟨ ≡ᵖ-sym (wfF _ k) ⟩
    ↓ᵖ (suc k) (F (↓ᵖ (suc k) P))
    QEDᵖ

cong-→ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
   → P ≡ᵖ P′
   → Q ≡ᵖ Q′
   → P →ᵖ Q  ≡ᵖ  P′ →ᵖ Q′
cong-→ᵖ PP′ QQ′ v k = (λ P→Q j j<k P′vj → let Pvj = proj₂ (PP′ v j) P′vj in
                                          let Qvj = P→Q j j<k Pvj in
                                          let Q′vj = proj₁ (QQ′ v j) Qvj in
                                          Q′vj)
                   , (λ P′→Q′ j j<k Pvj → let P′vj = proj₁ (PP′ v j) Pvj in
                                          let Q′vj = P′→Q′ j j<k P′vj in
                                          let Qvj = proj₂ (QQ′ v j) Q′vj in
                                          Qvj)

down-fun : ∀{A}{P Q : Predᵒ A}{k}
   → ↓ᵖ k (P →ᵖ Q) ≡ᵖ ↓ᵖ k ((↓ᵖ k P) →ᵖ (↓ᵖ k Q))
down-fun {A}{P}{Q}{k} x i =
        (λ { (i<k , PQxi) → i<k ,
                   (λ k₃ x₁ x₂ → (proj₁ x₂) , (PQxi k₃ x₁ (proj₂ x₂)))})
      , λ { (a , b) → a , (λ j x₁ Pxj →
                  let xx = b j x₁ (≤-trans (s≤s x₁) a , Pxj) in proj₂ xx)}

nonexpansive-→ : ∀{A}{F G : Predᵒ A → Predᵒ A}
   → nonexpansive F
   → nonexpansive G
   → nonexpansive (λ P → F P →ᵖ G P)
nonexpansive-→ {A}{F}{G} neF neG P k =
    ↓ᵖ k (F P →ᵖ G P)                              ≡ᵖ⟨ down-fun ⟩
    ↓ᵖ k (↓ᵖ k (F P) →ᵖ ↓ᵖ k (G P))  ≡ᵖ⟨ ext-↓ k (cong-→ᵖ (neF _ k) (neG _ k)) ⟩
    ↓ᵖ k (↓ᵖ k (F (↓ᵖ k P)) →ᵖ ↓ᵖ k (G (↓ᵖ k P)))  ≡ᵖ⟨ ≡ᵖ-sym down-fun ⟩
    ↓ᵖ k (F (↓ᵖ k P) →ᵖ G (↓ᵖ k P))
    QEDᵖ

wellfounded-→ : ∀{A}{F G : Predᵒ A → Predᵒ A}
   → wellfounded F
   → wellfounded G
   → wellfounded (λ P → F P →ᵖ G P)
wellfounded-→ {A}{F}{G} wfF wfG P k =
    ↓ᵖ (suc k) (F P →ᵖ G P)                              ≡ᵖ⟨ down-fun ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (F P) →ᵖ ↓ᵖ (suc k) (G P))
                               ≡ᵖ⟨ ext-↓ (suc k) (cong-→ᵖ (wfF _ k) (wfG _ k)) ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (F (↓ᵖ k P)) →ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P)))
                                                           ≡ᵖ⟨ ≡ᵖ-sym down-fun ⟩
    ↓ᵖ (suc k) (F (↓ᵖ k P) →ᵖ G (↓ᵖ k P))
    QEDᵖ


cong-×ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
   → P ≡ᵖ P′
   → Q ≡ᵖ Q′
   → P ×ᵖ Q  ≡ᵖ  P′ ×ᵖ Q′
cong-×ᵖ PP′ QQ′ v k = (λ {x k₁ x₁ → (proj₁ (PP′ v k₁) (proj₁ (x k₁ x₁)))
                                  , (proj₁ (QQ′ v k₁) (proj₂ (x k₁ x₁)))})
                    , (λ {x k₁ x₁ → (proj₂ (PP′ v k₁) (proj₁ (x k₁ x₁)))
                                  , (proj₂ (QQ′ v k₁) (proj₂ (x k₁ x₁)))})

down-× : ∀{A}{P Q : Predᵒ A}{k}
   → ↓ᵖ k (P ×ᵖ Q) ≡ᵖ ↓ᵖ k ((↓ᵖ k P) ×ᵖ (↓ᵖ k Q))
down-× {A}{P}{Q}{k} x i =
  (λ { (i<k , PQxi) → i<k , (λ j j≤i → ((≤-trans (s≤s j≤i) i<k) ,
             proj₁ (PQxi j j≤i)) , (≤-trans (s≤s j≤i) i<k)
                        , (proj₂ (PQxi j j≤i)))})
  ,
  λ {(i<k , PQxi) → i<k , (λ j j≤i → (proj₂ (proj₁ (PQxi j j≤i)))
                                   , (proj₂ (proj₂ (PQxi j j≤i))))}

wellfounded-× : ∀{A}{F G : Predᵒ A → Predᵒ A}
   → wellfounded F
   → wellfounded G
   → wellfounded (λ P → F P ×ᵖ G P)
wellfounded-× {A}{F}{G} wfF wfG P k =
    ↓ᵖ (suc k) (F P ×ᵖ G P)                              ≡ᵖ⟨ down-× ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (F P) ×ᵖ ↓ᵖ (suc k) (G P))
         ≡ᵖ⟨ ext-↓ (suc k) (cong-×ᵖ (wfF _ k) (wfG _ k)) ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (F (↓ᵖ k P)) ×ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P)))
         ≡ᵖ⟨ ≡ᵖ-sym down-× ⟩
    ↓ᵖ (suc k) (F (↓ᵖ k P) ×ᵖ G (↓ᵖ k P))
    QEDᵖ

nonexpansive-× : ∀{A}{F G : Predᵒ A → Predᵒ A}
   → nonexpansive F
   → nonexpansive G
   → nonexpansive (λ P → F P ×ᵖ G P)
nonexpansive-× {A}{F}{G} neF neG P k =
    ↓ᵖ k (F P ×ᵖ G P)                              ≡ᵖ⟨ down-× ⟩
    ↓ᵖ k (↓ᵖ k (F P) ×ᵖ ↓ᵖ k (G P))
         ≡ᵖ⟨ ext-↓ k (cong-×ᵖ (neF _ k) (neG _ k)) ⟩
    ↓ᵖ k (↓ᵖ k (F (↓ᵖ k P)) ×ᵖ ↓ᵖ k (G (↓ᵖ k P)))
         ≡ᵖ⟨ ≡ᵖ-sym down-× ⟩
    ↓ᵖ k (F (↓ᵖ k P) ×ᵖ G (↓ᵖ k P))
    QEDᵖ

cong-⊎ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
   → P ≡ᵖ P′
   → Q ≡ᵖ Q′
   → P ⊎ᵖ Q  ≡ᵖ  P′ ⊎ᵖ Q′
cong-⊎ᵖ {A}{P}{P′}{Q}{Q′} PP′ QQ′ v k = to , fro
  where
  to : (P ⊎ᵖ Q) v k → (P′ ⊎ᵖ Q′) v k
  to PQ j j<k
      with PQ j j<k
  ... | inj₁ Pvj = inj₁ (proj₁ (PP′ v j) Pvj)
  ... | inj₂ Qvj = inj₂ (proj₁ (QQ′ v j) Qvj)
  fro : (P′ ⊎ᵖ Q′) v k → (P ⊎ᵖ Q) v k
  fro PQ′ j j<k
      with PQ′ j j<k
  ... | inj₁ P′vj = inj₁ (proj₂ (PP′ v j) P′vj)
  ... | inj₂ Q′vj = inj₂ (proj₂ (QQ′ v j) Q′vj)
      
wellfounded-⊎ : ∀{A}{F G : Predᵒ A → Predᵒ A}
   → nonexpansive F
   → nonexpansive G
   → wellfounded (λ P → F P ⊎ᵖ G P)
wellfounded-⊎ {A}{F}{G} neF neG P k =
    ↓ᵖ (suc k) (F P ⊎ᵖ G P)                              ≡ᵖ⟨ EQ1 ⟩
    ↓ᵖ (suc k) (↓ᵖ k (F P) ⊎ᵖ ↓ᵖ k (G P))                ≡ᵖ⟨ ext-↓ (suc k) (cong-⊎ᵖ (neF _ k) (neG _ k)) ⟩
    ↓ᵖ (suc k) (↓ᵖ k (F (↓ᵖ k P)) ⊎ᵖ ↓ᵖ k (G (↓ᵖ k P)))  ≡ᵖ⟨ ≡ᵖ-sym EQ1 ⟩
    ↓ᵖ (suc k) (F (↓ᵖ k P) ⊎ᵖ G (↓ᵖ k P))
    QEDᵖ
    where
    to : ∀{P}{Q}{k} → (x : A) (i : ℕ) → ↓ᵖ (suc k) (P ⊎ᵖ Q) x i → ↓ᵖ (suc k) (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q) x i
    to {P} {Q} {k} x i (s≤s i≤k , P⊎Q) = s≤s i≤k , Goal
        where
        Goal : (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q) x i
        Goal j j<i
            with P⊎Q j j<i
        ... | inj₁ Pj = inj₁ ((≤-trans j<i i≤k) , Pj)
        ... | inj₂ Qj = inj₂ (≤-trans j<i i≤k , Qj)

    fro : ∀{P}{Q}{k} → (x : A) (i : ℕ) → ↓ᵖ (suc k) (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q) x i → ↓ᵖ (suc k) (P ⊎ᵖ Q) x i
    fro {P} {Q} {k} x i (s≤s i≤k , P⊎Q) = s≤s i≤k , Goal
        where
        Goal : (P ⊎ᵖ Q) x i
        Goal j j<i
            with P⊎Q j j<i
        ... | inj₁ Pj = inj₁ (proj₂ Pj)
        ... | inj₂ Qj = inj₂ (proj₂ Qj)

    EQ1 : ∀{P}{Q}{k} → ↓ᵖ (suc k) (P ⊎ᵖ Q) ≡ᵖ ↓ᵖ (suc k) ((↓ᵖ k P) ⊎ᵖ (↓ᵖ k Q))
    EQ1 {P}{Q}{k} x i = to{P}{Q} x i , fro{P}{Q} x i

extensional-id : ∀{A} → extensionalᵖ{A} (λ P → P)
extensional-id {A} PQ x i = proj₁ (PQ x i) , proj₂ (PQ x i)

extensional-→ : ∀{A}{F G : Predᵒ A → Predᵒ A}
   → extensionalᵖ{A} F
   → extensionalᵖ{A} G
   → extensionalᵖ{A} (λ P → F P →ᵖ G P)
extensional-→ {A} extF extG PQ x i =
  (λ FP→GP k x₂ x₃ → proj₁ (extG PQ x k) (FP→GP k x₂ (proj₂ (extF PQ x k) x₃)))
  , (λ z k z₁ z₂ → proj₂ (extG PQ x k) (z k z₁ (proj₁ (extF PQ x k) z₂)))

extensional-× : ∀{A}{F G : Predᵒ A → Predᵒ A}
   → extensionalᵖ{A} F
   → extensionalᵖ{A} G
   → extensionalᵖ{A} (λ P → F P ×ᵖ G P)
extensional-× {A} extF extG PQ x i =
  (λ x₁ k x₂ → (proj₁ (extF PQ x k) (proj₁ (x₁ k x₂)))
             , (proj₁ (extG PQ x k) (proj₂ (x₁ k x₂))))
  , (λ x₁ k x₂ → (proj₂ (extF PQ x k) (proj₁ (x₁ k x₂)))
               , (proj₂ (extG PQ x k) (proj₂ (x₁ k x₂))))

extensional-⊎ : ∀{A}{F G : Predᵒ A → Predᵒ A}
   → extensionalᵖ{A} F
   → extensionalᵖ{A} G
   → extensionalᵖ{A} (λ P → F P ⊎ᵖ G P)
extensional-⊎ {A}{F}{G} extF extG {P}{Q} PQ x i = to , fro
  where
  to : (F P ⊎ᵖ G P) x i → (F Q ⊎ᵖ G Q) x i
  to FP⊎GP k k<i
      with FP⊎GP k k<i
  ... | inj₁ FP = inj₁ (proj₁ (extF PQ x k) FP)
  ... | inj₂ GP = inj₂ (proj₁ (extG PQ x k) GP)

  fro : (F Q ⊎ᵖ G Q) x i → (F P ⊎ᵖ G P) x i
  fro FP⊎GP k k<i
      with FP⊎GP k k<i
  ... | inj₁ FP = inj₁ (proj₂ (extF PQ x k) FP)
  ... | inj₂ GP = inj₂ (proj₂ (extG PQ x k) GP)

cong-▷ᵖ : ∀{A}{P P′ : Predᵒ A}
   → P ≡ᵖ P′
   → ▷ᵖ P ≡ᵖ ▷ᵖ P′
cong-▷ᵖ PP′ v k = (λ {▷Pvk j j<k → proj₁ (PP′ v j) (▷Pvk j j<k)})
                , (λ ▷P′vk j j<k → proj₂ (PP′ v j) (▷P′vk j j<k))

wellfounded-▷ : ∀{A}{F : Predᵒ A → Predᵒ A}
   → nonexpansive F
   → wellfounded (λ P → ▷ᵖ (F P))
wellfounded-▷ {A}{F} neF P k =
    ↓ᵖ (suc k) (▷ᵖ (F P))                ≡ᵖ⟨ EQ1 ⟩
    ↓ᵖ (suc k) (▷ᵖ (↓ᵖ k (F P)))         ≡ᵖ⟨ ext-↓ (suc k) (cong-▷ᵖ (neF _ k)) ⟩
    ↓ᵖ (suc k) (▷ᵖ (↓ᵖ k (F (↓ᵖ k P))))  ≡ᵖ⟨ ≡ᵖ-sym EQ1 ⟩
    ↓ᵖ (suc k) (▷ᵖ (F (↓ᵖ k P)))
    QEDᵖ
  where
  EQ1 : ∀{P : Predᵒ A}{k} → ↓ᵖ (suc k) (▷ᵖ P) ≡ᵖ ↓ᵖ (suc k) (▷ᵖ (↓ᵖ k P))
  EQ1 {P}{k} x i = (λ {(s≤s i≤k , b) → s≤s i≤k ,
                      λ j j<i → (≤-trans j<i i≤k) , (b j j<i)})
                 , λ {(s≤s i≤k , b) → (s≤s i≤k) , (λ k z → proj₂ (b k z))}

extensional-▷ : ∀{A}{F : Predᵒ A → Predᵒ A}
   → extensionalᵖ{A} F
   → extensionalᵖ{A} (λ P → ▷ᵖ (F P))
extensional-▷ {A} extF PQ x i =
      (λ x₁ k x₂ → proj₁ (extF PQ x k) (x₁ k x₂))
    , (λ x₁ k x₂ → proj₂ (extF PQ x k) (x₁ k x₂))

{-------------------------------------------------------------------------------
     Step Indexed Logic
-------------------------------------------------------------------------------}

record NE (A : Set) : Set₁ where
  field
    fun : Predᵒ A → Predᵒ A
    ne : nonexpansive fun
    ext : extensionalᵖ fun
open NE

record WF (A : Set) : Set₁ where
  field
    fun : Predᵒ A → Predᵒ A
    wf : wellfounded fun
    ext : extensionalᵖ fun
open WF

idₖ : ∀{A} → NE A
idₖ = record { fun = λ P → P ; ne = nonexpansive-id ; ext = extensional-id }

infixr 6 _→ₖ_
_→ₖ_ : ∀{A} → NE A → NE A → NE A
F →ₖ G = record { fun = λ P → (fun F) P →ᵖ (fun G) P
                ; ne = nonexpansive-→ (ne F) (ne G)
                ; ext = extensional-→ (ext F) (ext G) }

infixr 6 _→ʷ_
_→ʷ_ : ∀{A} → WF A → WF A → WF A
F →ʷ G = record { fun = λ P → (fun F) P →ᵖ (fun G) P
                ; wf = wellfounded-→ (wf F) (wf G)
                ; ext = extensional-→ (ext F) (ext G) }

infixr 7 _×ₖ_
_×ₖ_ : ∀{A} → NE A → NE A → NE A
(F ×ₖ G) = record { fun = (λ P → (fun F) P ×ᵖ (fun G) P)
                  ; ne = nonexpansive-× (ne F) (ne G)
                  ; ext = extensional-× (ext F) (ext G) }

infixr 7 _×ʷ_
_×ʷ_ : ∀{A} → WF A → WF A → WF A
(F ×ʷ G) = record { fun = (λ P → (fun F) P ×ᵖ (fun G) P)
                  ; wf = wellfounded-× (wf F) (wf G)
                  ; ext = extensional-× (ext F) (ext G) }

infixr 7 _⊎ₖ_
_⊎ₖ_ : ∀{A} → NE A → NE A → WF A
(F ⊎ₖ G) = record { fun = (λ P → (fun F) P ⊎ᵖ (fun G) P)
                  ; wf = wellfounded-⊎ (ne F) (ne G)
                  ; ext = extensional-⊎ (ext F) (ext G) }

▷ₖ : ∀{A} → NE A → WF A
▷ₖ F = record { fun = (λ P → ▷ᵖ ((fun F) P))
              ; wf = wellfounded-▷ (ne F)
              ; ext = extensional-▷ (ext F) }

WF⇒NE : ∀{A} → WF A → NE A
WF⇒NE F = record { fun = fun F
                 ; ne = wellfounded⇒nonexpansive (fun F) (wf F) (ext F)
                 ; ext = ext F }

_ₖ : ∀{A} → Predᵒ A → NE A
(P)ₖ = record { fun = λ Q → P
              ; ne = nonexpansive-const{P = P}
              ; ext = λ _ x i → (λ x₁ → x₁) , (λ x₁ → x₁) }

μₖ : ∀{A} → WF A → Predᵒ A
μₖ F = μᵖ (fun F)

fixpoint  : ∀{A}
  → (F : WF A)
  → μₖ F ≡ᵖ fun F (μₖ F)
fixpoint F = theorem20 (fun F) (wf F) (ext F)



{------------------- Monotonic --------------------}

-- mono-→ᵒ : ∀{A}
--    → (F : Predᵒ A → Predᵒ A)
--    → monotonic F
--    → (G : Predᵒ A → Predᵒ A)
--    → monotonic G
--    → monotonic (λ P x → (F P x) →ᵒ (G P x))
-- mono-→ᵒ F mF G mG {P}{Q} P→Q x i FP→GP k k≤i FQk = {!!}

{-
have
FQk   : F Q x k
P→Q   : (x₁ : A) (i₁ : ℕ) → P x₁ i₁ → Q x₁ i₁
FP→GP : (F P x →ᵒ G P x) i

Goal: G Q x k

-}


{-------------------------------------------------------------------------------
  Experiment: attach all the good properties
 ------------------------------------------------------------------------------}

-- record Setₖ : Set₁ where
--   field
--     val : Setᵒ
--     dcl : dc val
--     ez : ee val
-- open Setₖ public

-- _ₖ : Set → Setₖ
-- P ₖ = record { val = (P ᵒ) ; dcl = dc-Pᵒ P ; ez = ee-Pᵒ P }

-- ⊥ₖ : Setₖ
-- ⊥ₖ = record { val = ⊥ᵒ ; dcl = dc-⊥ ; ez = ee-⊥ }

-- ⊤ₖ : Setₖ
-- ⊤ₖ  = record { val = ⊤ᵒ ; dcl = dc-⊤ ; ez = ee-⊤ }

-- _×ₖ_ : Setₖ → Setₖ → Setₖ
-- (P ×ₖ Q) = record { val = (val P ×ᵒ val Q)
--                   ; dcl = dc-× (dcl P) (dcl Q)
--                   ; ez = ee-× {val P}{val Q} (ez P) (ez Q) }

-- _⊎ₖ_ : Setₖ → Setₖ → Setₖ
-- (P ⊎ₖ Q) = record { val = (val P ⊎ᵒ val Q)
--                   ; dcl = dc-⊎ (dcl P) (dcl Q)
--                   ; ez = ee-⊎ {val P}{val Q} (ez P) (ez Q) }

-- _→ₖ_ : Setₖ → Setₖ → Setₖ
-- (P →ₖ Q) = record { val = (λ k → ∀ j → j < k → val P j → val Q j)
--                   ; dcl = dc-→ᵒ
--                   ; ez = ee-→
--                   }

-- ∀ₖ : ∀{A} → (A → Setₖ) → Setₖ
-- ∀ₖ {A} P = record { val = (λ k → ∀ (v : A) → val (P v) k)
--                   ; dcl = (λ n f k k≤n v → dcl (P v) n (f v) k k≤n)
--                   ; ez = ee-∀ {F = λ x → val (P x)} λ v → ez (P v) }

-- ▷_ : Setₖ → Setₖ
-- ▷ P = record { val = ▷ᵒ (val P) ; dcl = G ; ez = H }
--   where
--   G : dc (▷ᵒ (val P))
--   G n x zero k≤n = tt
--   G (suc n) Pn (suc k) (s≤s k≤n) = (dcl P) n Pn k k≤n

--   H : ee (▷ᵒ (val P))
--   H = tt

-- Predₖ : Set → Set₁
-- Predₖ A = A → Setₖ

-- ⊤ᴾ : ∀{A} → Predₖ A
-- ⊤ᴾ x = ⊤ₖ

-- ⊥ᴾ : ∀{A} → Predₖ A
-- ⊥ᴾ x = ⊥ₖ

-- monotonicₖ : ∀{A} (F : Predₖ A → Predₖ A) → Set₁
-- monotonicₖ F = ∀ P Q x i → (val (P x) i → val (Q x) i)
--                         → (val (F P x) i → val (F Q x) i)

-- record Functional (A : Set) : Set₁ where
--   field
--     fun : Predₖ A → Predₖ A
--     mono : monotonicₖ fun
-- open Functional    

-- -- dc-iter-index : ∀{i j k : ℕ}{A}{F : Functional A}{x : A}
-- --    → j ≤ k
-- --    → val (iter i (fun F) ⊤ᴾ x) k
-- --    → val (iter i (fun F) ⊤ᴾ x) j
-- -- dc-iter-index {zero} {j} {k} j≤k iterFk = tt
-- -- dc-iter-index {suc i} {j} {k}{A}{F}{x} j≤k iterFk =
-- --    let dcF = dcl (fun F (iter i (fun F) ⊤ᴾ) x) in
-- --    dcF k iterFk j j≤k

-- -- dc-iter-depth : ∀(i j k : ℕ){A}{F : Functional A}{x : A}
-- --    → j ≤′ k
-- --    → val (iter k (fun F) ⊤ᴾ x) i
-- --    → val (iter j (fun F) ⊤ᴾ x) i
-- -- dc-iter-depth i j .j _≤′_.≤′-refl iterkF = iterkF
-- -- dc-iter-depth i zero (suc k) (≤′-step j≤k) iterkF = tt
-- -- dc-iter-depth i (suc j) (suc k) {A}{F}{x} (≤′-step j≤k) FiterkFi =
-- --   mono F (iter k (fun F) ⊤ᴾ) (iter j (fun F) ⊤ᴾ) x i
-- --                   (λ iterkFi → dc-iter-depth i j k {A}{F}
-- --                       (≤⇒≤′ (≤-trans (n≤1+n _) (≤′⇒≤ j≤k))) iterkFi) FiterkFi

-- -- μᴾ : ∀{A} → (F : Functional A) → Predₖ A
-- -- (μᴾ {A} F) x = record
-- --   { val = (λ k → val (iter k (fun F) ⊤ᴾ x) k) 
-- --   ; dcl = (λ n Fnxn k k≤n →
-- --              let Fnxk = dc-iter-index{n}{k}{n}{A}{F}{x} k≤n Fnxn in
-- --              dc-iter-depth k k n {F = F}{x = x} (≤⇒≤′ k≤n) Fnxk)
-- --   ; ez = tt }


-- Lob : ∀{P : Setₖ}
--    → (∀ k → val (▷ P) k → val P k)
--      -----------------------------
--    → ∀ k → val P k
-- Lob ▷P→P zero = ▷P→P zero tt
-- Lob {P} ▷P→P (suc k) = ▷P→P (suc k) (Lob{P} ▷P→P k)

