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
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
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
(P ⊎ᵒ Q) n  = ∀ k → k ≤ n → (P k) ⊎ (Q k)

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

{------------------- Step Indexed Predicates --------------------}

Predᵒ : Set → Set₁
Predᵒ A = A → Setᵒ

⊤ᵖ : ∀{A} → Predᵒ A
⊤ᵖ x = ⊤ᵒ

⊥ᵖ : ∀{A} → Predᵒ A
⊥ᵖ x = ⊥ᵒ

fstᵖ : ∀{A}{B} (P : Predᵒ A) → Predᵒ (A × B)
fstᵖ P (a , b) = P a

sndᵖ : ∀{A}{B} (P : Predᵒ B) → Predᵒ (A × B)
sndᵖ P (a , b) = P b

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

μᵖ : ∀ {A} → (Predᵒ A → Predᵒ A) → Predᵒ A
(μᵖ F) x k  = iter (suc k) F ⊤ᵖ x k

{------------------- Eventually True at 0 --------------------}

ee : Setᵒ → Set
ee P  =  P zero

ee-⊥ : ee ⊥ᵒ
ee-⊥ = tt

ee-⊤ : ee ⊤ᵒ
ee-⊤ = tt

ee-× : ∀ {P Q} → ee P → ee Q → ee (P ×ᵒ Q)
ee-× P0 Q0 .zero z≤n = P0 , Q0

ee-⊎ : ∀ {P Q} → ee P → ee Q → ee (P ⊎ᵒ Q)
ee-⊎ P0 Q0 .zero z≤n = inj₁ P0

ee-→ : ∀ {P Q} → ee Q → ee (P →ᵒ Q)
ee-→ eeQ .zero z≤n Pz = eeQ

ee-▷ : ∀{P} → ee (▷ᵒ P)
ee-▷ {P} k ()

ee-∀ : ∀{A F}
   → (∀ v → ee (F v))
   → ee (∀ᵒ {A} F)
ee-∀ {F} eeF v = eeF v

ee-Pᵒ : (P : Set)
   → ee (P ᵒ)
ee-Pᵒ P = tt

eeᵖ : ∀{A} → Predᵒ A → Set
eeᵖ P = ∀ x → P x 0

ee-μ : ∀{A}{F : Predᵒ A → Predᵒ A}
   → (∀ p → eeᵖ p → eeᵖ (F p)) 
   → eeᵖ (μᵖ F)
ee-μ {A}{F} eeF x = eeF (λ _ _ → ⊤) (λ x → tt) x  

ee-fst : ∀{A}{B}{P : Predᵒ A}
   → eeᵖ P
   → eeᵖ (fstᵖ{A}{B} P)
ee-fst {A}{B}{P} eeP (a , b) = eeP a

ee-snd : ∀{A}{B}{P : Predᵒ B}
   → eeᵖ P
   → eeᵖ (sndᵖ{A}{B} P)
ee-snd {A}{B}{P} eeP (a , b) = eeP b

{------------------- Downward Closed --------------------}

dc : Setᵒ → Set
dc P  =  ∀ n → P n → ∀ k → k ≤ n → P k

dc-⊥ : dc ⊥ᵒ
dc-⊥ zero tt k z≤n  =   tt
dc-⊥ (suc n) ()

dc-⊤ : dc ⊤ᵒ
dc-⊤  =  λ n ⊤ᵒn k k≤n → tt

dc-× : ∀ {P Q} → dc (P ×ᵒ Q)
dc-× n P×Q k x₁ j x₂ = P×Q j (≤-trans x₂ x₁) 

dc-⊎ : ∀ {P Q} → dc (P ⊎ᵒ Q)
dc-⊎ n P⊎Q k x j y = P⊎Q j (≤-trans y x)

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

dc-▷ : ∀{P}
   → dc P
   → dc (▷ᵒ P)
dc-▷ dcP n ▷Pn k k≤n j j<k = ▷Pn j (≤-trans j<k k≤n)

dcᵖ : ∀{A} → Predᵒ A → Set
dcᵖ P = ∀ n x → P x n → ∀ k → k ≤ n → P x k

dc-Pᵖ : ∀{A}(S : Set)
   → dcᵖ{A} (λ v → (S)ᵒ)
dc-Pᵖ S n x Sᵒn = dc-Pᵒ S n Sᵒn

dc-∀ᵖ : ∀{A}{B}{F : A → Predᵒ B}
   → (∀ a → dcᵖ (F a))
   → dcᵖ (∀ᵖ F)
dc-∀ᵖ {A}{B}{F} dcF n b ∀F k kn v = dcF v n b (∀F v) k kn

dc-iter : ∀(i : ℕ){A}
   → (F : Predᵒ A → Predᵒ A)
   → (∀ p → dcᵖ p → dcᵖ (F p))
   → dcᵖ (iter i F ⊤ᵖ)
dc-iter zero F dcF = λ n x _ k _ → tt
dc-iter (suc i) F dcF =
  let IH = dc-iter i F dcF in
  dcF (iter i F ⊤ᵖ) IH

dc-fst : ∀{A}{B}{P : Predᵒ A}
  → dcᵖ P
  → dcᵖ (fstᵖ{A}{B} P)
dc-fst {A}{B}{P} dcP n (a , b) fstP k k≤n = dcP n a fstP k k≤n

dc-snd : ∀{A}{B}{P : Predᵒ B}
  → dcᵖ P
  → dcᵖ (sndᵖ{A}{B} P)
dc-snd {A}{B}{P} dcP n (a , b) sndP k k≤n = dcP n b sndP k k≤n

{-----------   Reasoning about if-and-only-if    -----------------}

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

{-----  Reasoning about Equality on Step Indexed Sets and Predicates  ---------}

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

{---------  Extensionality     ------------------------------------------------}

extensionalᵖ : ∀{A}{B} (F : Predᵒ A → Predᵒ B) → Set₁
extensionalᵖ F = ∀{P}{Q} → P ≡ᵖ Q → F P ≡ᵖ F Q

extensional-id : ∀{A} → extensionalᵖ{A} (λ P → P)
extensional-id {A} PQ x i = proj₁ (PQ x i) , proj₂ (PQ x i)

extensional-fst : ∀{A}{B}
  → extensionalᵖ{A}{A × B} fstᵖ
extensional-fst {A}{B} PQ (a , b) i =
    (λ x₁ → proj₁ (PQ a i) x₁) , proj₂ (PQ a i)

extensional-snd : ∀{A}{B}
  → extensionalᵖ{B}{A × B} sndᵖ
extensional-snd {A}{B} PQ (a , b) i =
    proj₁ (PQ b i) , proj₂ (PQ b i)

extensional-→ : ∀{A}{B}{F G : Predᵒ A → Predᵒ B}
   → extensionalᵖ F
   → extensionalᵖ G
   → extensionalᵖ (λ P → F P →ᵖ G P)
extensional-→ extF extG PQ x i =
  (λ FP→GP k x₂ x₃ → proj₁ (extG PQ x k) (FP→GP k x₂ (proj₂ (extF PQ x k) x₃)))
  , (λ z k z₁ z₂ → proj₂ (extG PQ x k) (z k z₁ (proj₁ (extF PQ x k) z₂)))

extensional-× : ∀{A}{B}{F G : Predᵒ A → Predᵒ B}
   → extensionalᵖ F
   → extensionalᵖ G
   → extensionalᵖ (λ P → F P ×ᵖ G P)
extensional-× extF extG PQ x i =
  (λ x₁ k x₂ → (proj₁ (extF PQ x k) (proj₁ (x₁ k x₂)))
             , (proj₁ (extG PQ x k) (proj₂ (x₁ k x₂))))
  , (λ x₁ k x₂ → (proj₂ (extF PQ x k) (proj₁ (x₁ k x₂)))
               , (proj₂ (extG PQ x k) (proj₂ (x₁ k x₂))))

extensional-⊎ : ∀{A}{B}{F G : Predᵒ A → Predᵒ B}
   → extensionalᵖ F
   → extensionalᵖ G
   → extensionalᵖ (λ P → F P ⊎ᵖ G P)
extensional-⊎ {A}{B}{F}{G} extF extG {P}{Q} PQ x i = to , fro
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

extensional-▷ : ∀{A}{B}{F : Predᵒ A → Predᵒ B}
   → extensionalᵖ F
   → extensionalᵖ (λ P → ▷ᵖ (F P))
extensional-▷ extF PQ x i =
      (λ x₁ k x₂ → proj₁ (extF PQ x k) (x₁ k x₂))
    , (λ x₁ k x₂ → proj₂ (extF PQ x k) (x₁ k x₂))

extensional-∀ : ∀{A B C}{F : Predᵒ B → Predᵒ (A × C)}
   → extensionalᵖ{B}{A × C} F
   → extensionalᵖ{B}{C} (λ P → ∀ᵖ λ a b → (F P) (a , b))
extensional-∀ {A}{B}{C} extF PQ x i =
    (λ ∀FPxi v → proj₁ (extF PQ (v , x) i) (∀FPxi v))
  , (λ ∀FQxi v → proj₂ (extF PQ (v , x) i) (∀FQxi v))

{------------ Continuous and Wellfounded Functions on Step Indexed Predicates -}

↓ᵒ : ℕ → Setᵒ → Setᵒ
↓ᵒ k S j = j < k  ×  S j

↓ᵖ : ℕ → ∀{A} → Predᵒ A → Predᵒ A
↓ᵖ k P x = ↓ᵒ k (P x)

ext-↓ : ∀{A}
    (k : ℕ)
  → extensionalᵖ{A}{A} (↓ᵖ k)
ext-↓ k PQ x i = (λ { (fst , snd) → fst , proj₁ (PQ x i) snd})
                , λ { (fst , snd) → fst , proj₂ (PQ x i) snd}

{-
  Continuous means that you only need k steps of the input to get k
  steps of the output.
  (This is called nonexpansive in Appel and McAllester.)
-}
continuous : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
continuous F = ∀ P k → (↓ᵖ k (F P)) ≡ᵖ (↓ᵖ k (F (↓ᵖ k P)))

wellfounded : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
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
   Y = dc-iter (suc k) F dcF k v X j j≤k
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
      ↓ᵖ k (μᵖ F)                                   ≡ᵖ⟨ lemma18a k F wfF extF ⟩
      ↓ᵖ k (iter k F ⊤ᵖ)
                               ≡ᵖ⟨ lemma15b{j = k}{suc k} F wfF extF (n≤1+n k) ⟩
      ↓ᵖ k (iter (suc k) F ⊤ᵖ)
                                ≡ᵖ⟨ ≡ᵖ-sym (lemma17 {P = iter (suc k) F ⊤ᵖ} k) ⟩
      ↓ᵖ k (↓ᵖ (suc k) (iter (suc k) F ⊤ᵖ))
                                  ≡ᵖ⟨ ext-↓ k (≡ᵖ-sym (lemma18b k F wfF extF)) ⟩
      ↓ᵖ k (↓ᵖ (suc k) (F (μᵖ F)))                              ≡ᵖ⟨ lemma17 k ⟩
      ↓ᵖ k (F (μᵖ F))
    QEDᵖ

theorem20 : ∀{A}
   → (F : Predᵒ A → Predᵒ A)
   → wellfounded F
   → extensionalᵖ F
   → μᵖ F ≡ᵖ F (μᵖ F)
theorem20 F wfF extF = equiv-down (λ k → lemma19 k F wfF extF)

continuous-const : ∀{A}{B}{P : Predᵒ B}
   → continuous{A}{B} (λ Q → P)
continuous-const {A}{P} Q k = ≡ᵖ-refl refl

wellfounded-const : ∀{A}{B}{P : Predᵒ B}
   → wellfounded{A}{B} (λ Q → P)
wellfounded-const {A}{P} Q k x i = (λ x → x) , (λ x → x)

extensional-const : ∀{A}{B}{P : Predᵒ B}
   → extensionalᵖ {A}{B} (λ Q → P)
extensional-const {A}{P} Q k = ≡ᵒ-refl refl

wellfounded⇒continuous : ∀{A}{B}
   → (F : Predᵒ A → Predᵒ B)
   → wellfounded F
   → extensionalᵖ F
   → continuous F
wellfounded⇒continuous F wfF extF P zero v i = (λ {()}) , λ { ()}
wellfounded⇒continuous F wfF extF P (suc k) =
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

continuous-→ : ∀{A}{B}{F G : Predᵒ A → Predᵒ B}
   → continuous F
   → continuous G
   → continuous (λ P → F P →ᵖ G P)
continuous-→ {A}{B}{F}{G} neF neG P k =
    ↓ᵖ k (F P →ᵖ G P)                              ≡ᵖ⟨ down-fun ⟩
    ↓ᵖ k (↓ᵖ k (F P) →ᵖ ↓ᵖ k (G P))  ≡ᵖ⟨ ext-↓ k (cong-→ᵖ (neF _ k) (neG _ k)) ⟩
    ↓ᵖ k (↓ᵖ k (F (↓ᵖ k P)) →ᵖ ↓ᵖ k (G (↓ᵖ k P)))  ≡ᵖ⟨ ≡ᵖ-sym down-fun ⟩
    ↓ᵖ k (F (↓ᵖ k P) →ᵖ G (↓ᵖ k P))
    QEDᵖ

wellfounded-→ : ∀{A}{B}{F G : Predᵒ A → Predᵒ B}
   → wellfounded F
   → wellfounded G
   → wellfounded (λ P → F P →ᵖ G P)
wellfounded-→ {A}{B}{F}{G} wfF wfG P k =
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

wellfounded-× : ∀{A}{B}{F G : Predᵒ A → Predᵒ B}
   → wellfounded F
   → wellfounded G
   → wellfounded (λ P → F P ×ᵖ G P)
wellfounded-× {A}{B}{F}{G} wfF wfG P k =
    ↓ᵖ (suc k) (F P ×ᵖ G P)                              ≡ᵖ⟨ down-× ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (F P) ×ᵖ ↓ᵖ (suc k) (G P))
         ≡ᵖ⟨ ext-↓ (suc k) (cong-×ᵖ (wfF _ k) (wfG _ k)) ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (F (↓ᵖ k P)) ×ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P)))
         ≡ᵖ⟨ ≡ᵖ-sym down-× ⟩
    ↓ᵖ (suc k) (F (↓ᵖ k P) ×ᵖ G (↓ᵖ k P))
    QEDᵖ

continuous-× : ∀{A}{B}{F G : Predᵒ A → Predᵒ B}
   → continuous F
   → continuous G
   → continuous (λ P → F P ×ᵖ G P)
continuous-× {A}{B}{F}{G} neF neG P k =
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
      
down-⊎ : ∀{A}{P Q : Predᵒ A}{k}
   → ↓ᵖ k (P ⊎ᵖ Q) ≡ᵖ ↓ᵖ k ((↓ᵖ k P) ⊎ᵖ (↓ᵖ k Q))
down-⊎ {A}{P}{Q}{k} x i = to , fro
  where
  to : ↓ᵖ k (P ⊎ᵖ Q) x i → ↓ᵖ k (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q) x i
  to (i<k , P⊎Qxi) = (i<k , Goal)
    where
    Goal : (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q) x i
    Goal j j<
        with P⊎Qxi j j<
    ... | inj₁ Pxj = inj₁ ((≤-trans (s≤s j<) i<k) , Pxj)
    ... | inj₂ Qxj = inj₂ ((≤-trans (s≤s j<) i<k) , Qxj)
  fro : ↓ᵖ k (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q) x i → ↓ᵖ k (P ⊎ᵖ Q) x i
  fro (i<k , P⊎Qxi) = (i<k , Goal)
    where
    Goal : (P ⊎ᵖ Q) x i
    Goal j j<
        with P⊎Qxi j j<
    ... | inj₁ Pxj = inj₁ (proj₂ Pxj)
    ... | inj₂ Qxj = inj₂ (proj₂ Qxj)

continuous-⊎ : ∀{A}{B}{F G : Predᵒ A → Predᵒ B}
   → continuous F
   → continuous G
   → continuous (λ P → F P ⊎ᵖ G P)
continuous-⊎ {A}{B}{F}{G} neF neG P k =
    ↓ᵖ k (F P ⊎ᵖ G P)                              ≡ᵖ⟨ down-⊎ ⟩
    ↓ᵖ k (↓ᵖ k (F P) ⊎ᵖ ↓ᵖ k (G P))
         ≡ᵖ⟨ ext-↓ k (cong-⊎ᵖ (neF _ k) (neG _ k)) ⟩
    ↓ᵖ k (↓ᵖ k (F (↓ᵖ k P)) ⊎ᵖ ↓ᵖ k (G (↓ᵖ k P)))
         ≡ᵖ⟨ ≡ᵖ-sym down-⊎ ⟩
    ↓ᵖ k (F (↓ᵖ k P) ⊎ᵖ G (↓ᵖ k P))
    QEDᵖ

wellfounded-⊎ : ∀{A}{B}{F G : Predᵒ A → Predᵒ B}
   → wellfounded F
   → wellfounded G
   → wellfounded (λ P → F P ⊎ᵖ G P)
wellfounded-⊎ {A}{B}{F}{G} wfF wfG P k =
    ↓ᵖ (suc k) (F P ⊎ᵖ G P)                              ≡ᵖ⟨ down-⊎ ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (F P) ⊎ᵖ ↓ᵖ (suc k) (G P))
         ≡ᵖ⟨ ext-↓ (suc k) (cong-⊎ᵖ (wfF _ k) (wfG _ k)) ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (F (↓ᵖ k P)) ⊎ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P)))
         ≡ᵖ⟨ ≡ᵖ-sym down-⊎ ⟩
    ↓ᵖ (suc k) (F (↓ᵖ k P) ⊎ᵖ G (↓ᵖ k P))
    QEDᵖ

cong-▷ᵖ : ∀{A}{P P′ : Predᵒ A}
   → P ≡ᵖ P′
   → ▷ᵖ P ≡ᵖ ▷ᵖ P′
cong-▷ᵖ PP′ v k = (λ {▷Pvk j j<k → proj₁ (PP′ v j) (▷Pvk j j<k)})
                , (λ ▷P′vk j j<k → proj₂ (PP′ v j) (▷P′vk j j<k))

wellfounded-▷ : ∀{A}{B}{F : Predᵒ A → Predᵒ B}
   → continuous F
   → wellfounded (λ P → ▷ᵖ (F P))
wellfounded-▷ {A}{B}{F} neF P k =
    ↓ᵖ (suc k) (▷ᵖ (F P))                ≡ᵖ⟨ EQ1 ⟩
    ↓ᵖ (suc k) (▷ᵖ (↓ᵖ k (F P)))         ≡ᵖ⟨ ext-↓ (suc k) (cong-▷ᵖ (neF _ k)) ⟩
    ↓ᵖ (suc k) (▷ᵖ (↓ᵖ k (F (↓ᵖ k P))))  ≡ᵖ⟨ ≡ᵖ-sym EQ1 ⟩
    ↓ᵖ (suc k) (▷ᵖ (F (↓ᵖ k P)))
    QEDᵖ
  where
  EQ1 : ∀{A}{P : Predᵒ A}{k} → ↓ᵖ (suc k) (▷ᵖ P) ≡ᵖ ↓ᵖ (suc k) (▷ᵖ (↓ᵖ k P))
  EQ1 {A}{P}{k} x i = (λ {(s≤s i≤k , b) → s≤s i≤k ,
                      λ j j<i → (≤-trans j<i i≤k) , (b j j<i)})
                 , λ {(s≤s i≤k , b) → (s≤s i≤k) , (λ k z → proj₂ (b k z))}

down-∀ : ∀{A B}{P : Predᵒ (A × B)}{k}
   → ↓ᵖ k (∀ᵖ λ a b → P (a , b)) ≡ᵖ ↓ᵖ k (∀ᵖ λ a b → ↓ᵖ k P (a , b))
down-∀ {A}{B}{F} x i = (λ {(i<k , ∀Fxi) → i<k , λ v → i<k , ∀Fxi v})
                     , (λ {(i<k , ∀Fxi) → i<k , (λ x → proj₂ (∀Fxi x))})

cong-∀ᵖ : ∀{A B}{P P′ : Predᵒ (A × B)}
   → P ≡ᵖ P′
   → ∀ᵖ (λ a b → P (a , b)) ≡ᵖ ∀ᵖ (λ a b → P′ (a , b))
cong-∀ᵖ PP′ v k =
    (λ z v′ → proj₁ (PP′ (v′ , v) k) (z v′))
    , (λ z v′ → proj₂ (PP′ (v′ , v) k) (z v′))

{-------------------------------------------------------------------------------
     Step Indexed Logic
-------------------------------------------------------------------------------}

data Kind : Set where
  Continuous : Kind
  Wellfounded : Kind

goodness : Kind → ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
goodness Continuous F = continuous F
goodness Wellfounded F = wellfounded F

data IsDownClosed : Set where
  DownClosed : IsDownClosed
  NotDownClosed : IsDownClosed

closed : IsDownClosed → ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
closed DownClosed F = ∀ P → dcᵖ P → dcᵖ (F P)
closed NotDownClosed F = topᵖ

record Fun (A B : Set) (κ : Kind) (DC : IsDownClosed) : Set₁ where
  field
    fun : Predᵒ A → Predᵒ B
    good : goodness κ fun
    ext : extensionalᵖ fun
    down : closed DC fun
    ez : ∀ P → eeᵖ P → eeᵖ (fun P)
    {- TODO: add eventually zero -}
open Fun public

choose : Kind → Kind → Kind
choose Continuous Continuous = Continuous
choose Continuous Wellfounded = Continuous
choose Wellfounded Continuous = Continuous
choose Wellfounded Wellfounded = Wellfounded

goodness-→ : ∀ (kf kg : Kind) {A}{B}{F G : Predᵒ A → Predᵒ B}
   → goodness kf F
   → extensionalᵖ F
   → goodness kg G
   → extensionalᵖ G
   → goodness (choose kf kg) (λ P → F P →ᵖ G P)
goodness-→ Continuous Continuous gf extF gg extG  = continuous-→ gf gg
goodness-→ Continuous Wellfounded {G = G} gf extF gg extG =
    continuous-→ gf (wellfounded⇒continuous G gg extG)
goodness-→ Wellfounded Continuous {F = F} gf extF gg extG =
    continuous-→ (wellfounded⇒continuous F gf extF) gg
goodness-→ Wellfounded Wellfounded gf extF gg extG = wellfounded-→ gf gg

kind : ∀{A}{B}{kF}{DC} → Fun A B kF DC → Kind
kind {A}{B}{kF} F = kF

infixr 6 _→ᶠ_
_→ᶠ_ : ∀{A B}{kF kG}{FDC}{GDC}
   → Fun A B kF FDC
   → Fun A B kG GDC
   → Fun A B (choose kF kG) DownClosed
F →ᶠ G = record { fun = λ P → (fun F) P →ᵖ (fun G) P
        ; good = goodness-→ (kind F) (kind G) (good F) (ext F) (good G) (ext G)
        ; ext = extensional-→ (ext F) (ext G)
        ; down = λ P dcP n x x₁ → dc-→ᵒ n x₁
        ; ez = λ P eeP x₁ → ee-→ (ez G P eeP x₁)
        }

goodness-× : ∀ (kf kg : Kind) {A}{B}{F G : Predᵒ A → Predᵒ B}
   → goodness kf F
   → extensionalᵖ F
   → goodness kg G
   → extensionalᵖ G
   → goodness (choose kf kg) (λ P → F P ×ᵖ G P)
goodness-× Continuous Continuous gf extF gg extG  = continuous-× gf gg
goodness-× Continuous Wellfounded {G = G} gf extF gg extG =
    continuous-× gf (wellfounded⇒continuous G gg extG)
goodness-× Wellfounded Continuous {F = F} gf extF gg extG =
    continuous-× (wellfounded⇒continuous F gf extF) gg
goodness-× Wellfounded Wellfounded gf extF gg extG = wellfounded-× gf gg

infixr 6 _×ᶠ_
_×ᶠ_ : ∀{A}{B}{kF kG}{FDC GDC}
   → Fun A B kF FDC
   → Fun A B kG GDC
   → Fun A B (choose kF kG) DownClosed
F ×ᶠ G = record { fun = λ P → (fun F) P ×ᵖ (fun G) P
        ; good = goodness-× (kind F) (kind G) (good F) (ext F) (good G) (ext G)
        ; ext = extensional-× (ext F) (ext G)
        ; down = λ P dcP n x x₁ → dc-× n x₁
        ; ez = λ P x x₁ → ee-× (ez F P x x₁) (ez G P x x₁)
        }

goodness-⊎ : ∀ (kf kg : Kind) {A}{B}{F G : Predᵒ A → Predᵒ B}
   → goodness kf F
   → extensionalᵖ F
   → goodness kg G
   → extensionalᵖ G
   → goodness (choose kf kg) (λ P → F P ⊎ᵖ G P)
goodness-⊎ Continuous Continuous gf extF gg extG  = continuous-⊎ gf gg
goodness-⊎ Continuous Wellfounded {G = G} gf extF gg extG =
    continuous-⊎ gf (wellfounded⇒continuous G gg extG)
goodness-⊎ Wellfounded Continuous {F = F} gf extF gg extG =
    continuous-⊎ (wellfounded⇒continuous F gf extF) gg
goodness-⊎ Wellfounded Wellfounded gf extF gg extG = wellfounded-⊎ gf gg

infixr 6 _⊎ᶠ_
_⊎ᶠ_ : ∀{A}{B}{kF kG}{FDC GDC}
   → Fun A B kF FDC
   → Fun A B kG GDC
   → Fun A B (choose kF kG) DownClosed
F ⊎ᶠ G = record { fun = λ P → (fun F) P ⊎ᵖ (fun G) P
        ; good = goodness-⊎ (kind F) (kind G) (good F) (ext F) (good G) (ext G)
        ; ext = extensional-⊎ (ext F) (ext G)
        ; down = λ P dcP n x x₁ → dc-⊎ n x₁
        ; ez = λ P x x₁ → ee-⊎ (ez F P x x₁) (ez G P x x₁)
        }

continuous-all : ∀{A B C}
   → (F : A → Fun B C Continuous DownClosed)
   → continuous (λ P → ∀ᵖ (λ a → fun (F a) P))
continuous-all F P k x i =
    (λ { (i<k , ∀FP) →
       i<k , (λ v → let xx = proj₁ (good (F v) P k x i) (i<k , (∀FP v)) in
                    proj₂ xx)})
  , (λ {(i<k , ∀F↓P) →
       i<k , (λ v → let xx = proj₂ (good (F v) P k x i) (i<k , (∀F↓P v)) in
                    proj₂ xx)})

wellfounded-all : ∀{A B C}
   → (F : A → Fun B C Wellfounded DownClosed)
   → wellfounded (λ P → ∀ᵖ (λ a → fun (F a) P))
wellfounded-all F P k x i =
    (λ{(s≤s i≤k , ∀FP) →
        (s≤s i≤k)
        , (λ v → let xx = proj₁ (good (F v) P k x i) ((s≤s i≤k) , (∀FP v)) in
                 proj₂ xx)})
    , λ {(s≤s i≤k , ∀F↓P) →
        (s≤s i≤k)
        , (λ v → let xx = proj₂ (good (F v) P k x i) ((s≤s i≤k) , (∀F↓P v)) in
                 proj₂ xx)}

goodness-all : ∀{A B C}{K}
   → (F : A → Fun B C K DownClosed)
   → goodness K (λ P → ∀ᵖ (λ a → fun (F a) P))
goodness-all {A} {B} {C} {Continuous} F = continuous-all F
goodness-all {A} {B} {C} {Wellfounded} F = wellfounded-all F

extensional-all : ∀{A B C}{K}
   → (F : A → Fun B C K DownClosed)
   → extensionalᵖ (λ P → ∀ᵖ (λ a → fun (F a) P))
extensional-all F {P}{Q} PQ c i =
  (λ ∀FP v → proj₁ (ext (F v) PQ c i) (∀FP v))
  , (λ ∀FQ v → proj₂ (ext (F v) PQ c i) (∀FQ v))

dc-all : ∀{A B C}{K}
   → (F : A → Fun B C K DownClosed)
   → (P : B → ℕ → Set)
   → dcᵖ P → dcᵖ (∀ᵖ (λ a → fun (F a) P))
dc-all F P dcP =
  let dcFP : ∀ a → dcᵖ (fun (F a) P)
      dcFP = λ a → down (F a) P dcP 
  in  
  dc-∀ᵖ dcFP

ee-all : ∀{A B C}{K}
   → (F : A → Fun B C K DownClosed)
   → (P : B → ℕ → Set)
   → eeᵖ P
   → eeᵖ (∀ᵖ (λ a → fun (F a) P))
ee-all F P eeP x v = ez (F v) P eeP x

∀ᵍ : ∀{A B C : Set}{K}
   → (A → Fun B C K DownClosed)
   → Fun B C K DownClosed
∀ᵍ {A}{B}{C} F = record { fun = λ P → ∀ᵖ {A} λ a → fun (F a) P
    ; good = goodness-all F
    ; ext = extensional-all F
    ; down = dc-all F
    ; ez = ee-all F }

goodness-▷ : ∀ (k : Kind) → ∀{A}{B}{F : Predᵒ A → Predᵒ B}
  → goodness k F
  → extensionalᵖ F
  → wellfounded (λ P → ▷ᵖ (F P))
goodness-▷ Continuous gf extF = wellfounded-▷ gf
goodness-▷ Wellfounded {A}{B}{F} gf extF =
    wellfounded-▷ (wellfounded⇒continuous F gf extF )

closed-▷ : ∀ (DC : IsDownClosed) → ∀{A}{B}{F : Predᵒ A → Predᵒ B}
   → closed DC F
   → closed DC (λ P → ▷ᵖ (F P))
closed-▷ DownClosed cF P x n x₁ x₂ = dc-▷ (λ n → cF P x n x₁) n x₂              
closed-▷ NotDownClosed cF = ttᵖ

▷ᶠ : ∀{A}{B}{kF}{DC} → Fun A B kF DC → Fun A B Wellfounded DC
▷ᶠ {DC = DC} F = record { fun = (λ P → ▷ᵖ ((fun F) P))
              ; good = goodness-▷ (kind F) (good F) (ext F)
              ; ext = extensional-▷ (ext F) 
              ; down = closed-▷ DC (down F)
              ; ez = λ P eeP v k → λ {()}
              }

μᶠ : ∀{A} → Fun A A Wellfounded DownClosed → Predᵒ A
μᶠ F = μᵖ (fun F)

dc-μᶠ : ∀{A}{F : Fun A A Wellfounded DownClosed}
   → dcᵖ (μᶠ F)
dc-μᶠ {A}{F} = dc-μ (good F) (ext F) (down F)

ee-μᶠ : ∀{A}{F : Fun A A Wellfounded DownClosed}
   → eeᵖ (μᶠ F)
ee-μᶠ {A}{F} = ee-μ{A}{fun F} (ez F)

fixpointᶠ  : ∀{A}
  → (F : Fun A A Wellfounded DownClosed)
  → μᶠ F ≡ᵖ fun F (μᶠ F)
fixpointᶠ F = theorem20 (fun F) (good F) (ext F)

goodness-flip : ∀{A}{B}{K}{DC}
  → (f : B → Fun A ⊤ K DC)
  → goodness K (λ P b k → fun (f b) P tt k)
goodness-flip {A} {B} {Continuous} f P k x = good (f x) P k tt
goodness-flip {A} {B} {Wellfounded} f P k x = good (f x) P k tt

extensional-flip : ∀{A}{B}{K}{DC}
   → (f : B → Fun A ⊤ K DC)
   → extensionalᵖ (λ P b k → fun (f b) P tt k)
extensional-flip {A}{B}{K} f z x = ext (f x) z tt

dc-flip : ∀{A}{B}{K}
   → (f : B → Fun A ⊤ K DownClosed)
   → (P : A → ℕ → Set)
   → dcᵖ P
   → dcᵖ (λ b k → fun (f b) P tt k)
dc-flip f P dcP n x = down (f x) P dcP n tt

ee-flip : ∀{A}{B}{K}{DC}
   → (f : B → Fun A ⊤ K DC)
   → (P : A → ℕ → Set)
   → eeᵖ P
   → eeᵖ (λ b k → fun (f b) P tt k)
ee-flip {A}{B}{K} f P eeP x = ez (f x) P eeP tt

closed-flip : ∀{A}{B}{K}{DC}
   → (f : B → Fun A ⊤ K DC)
   → closed DC (λ P b k → fun (f b) P tt k)
closed-flip {DC = DownClosed} f = dc-flip f
closed-flip {DC = NotDownClosed} f = ttᵖ 

flip : ∀{A}{B}{K}{DC}
   → (B → Fun A ⊤ K DC)
   → Fun A B K DC
flip f = record { fun = λ P b k → fun (f b) P tt k
                ; good = goodness-flip f
                ; ext = extensional-flip f
                ; down = closed-flip f
                ; ez = ee-flip f }

continuous-recur : ∀{A}{B}
   → (a : A)
   → continuous{A}{B} (λ P x → P a)
continuous-recur a P k x i =
    (λ { (i<k , Pa) → i<k , i<k , Pa})
  , λ { (i<k , ↓kPa) → i<k , proj₂ ↓kPa}

extensional-recur : ∀{A}{B}
   → (a : A)
   → extensionalᵖ{A}{B} (λ P x → P a)
extensional-recur {A}{B} a PQ x i = PQ a i   

dc-recur : ∀{A}{B}
   → (a : A)
   → (P : A → ℕ → Set)
   → dcᵖ P
   → dcᵖ{B} (λ x → P a)
dc-recur {A} a P dcP n x = dcP n a

ee-recur : ∀{A}{B}
   → (a : A)
   → (P : A → ℕ → Set) → eeᵖ P → eeᵖ{B} (λ x → P a)
ee-recur {A} a P eeP x = eeP a

closed-recur : ∀{A}{B}{DC}
   → (a : A)
   → closed DC {A}{B} (λ P x → P a)
closed-recur {DC = DownClosed} a = dc-recur a
closed-recur {DC = NotDownClosed} a = ttᵖ

recur : ∀{A}{B}
   → A
   → Fun A B Continuous DownClosed
recur a = record { fun = λ P → λ x → P a
    ; good = continuous-recur a
    ; ext = extensional-recur a
    ; down = dc-recur a
    ; ez = ee-recur a }

closed-set : ∀{A}{B}{DC}
   → (S : Set)
   → closed DC {A}{B} (λ P v → S ᵒ)
closed-set {DC = DownClosed} S P dcP = dc-Pᵖ S
closed-set {DC = NotDownClosed} S = ttᵖ

_ᶠ : ∀{A}{B}
   → Set
   → Fun A B Wellfounded DownClosed
(S)ᶠ = record { fun = λ P → (λ v → (S)ᵒ)
    ; good = wellfounded-const
    ; ext = extensional-const
    ; down = λ P dcP → dc-Pᵖ S
    ; ez = λ P eeP b → tt
    }

_₀ : Setᵒ → Setᵒ
(S ₀) zero = ⊤
(S ₀) (suc k) = S (suc k)

wellfounded-index : ∀{A}{B}{S : Setᵒ}
   → wellfounded{A}{B} (λ P b → (S)₀)
wellfounded-index P k b i =
    (λ {(s≤s i≤k , Si) → (s≤s i≤k) , Si})
    , λ {(s≤s i≤k , Si) → (s≤s i≤k) , Si}

extensional-index : ∀{A}{B}{S : Setᵒ}
   → extensionalᵖ{A}{B} (λ P b k → S k)
extensional-index {A}{B}{S} PQ b i = (λ z → z) , (λ z → z)

ee-zero :
    (S : Setᵒ)
  → ee ((S)₀)
ee-zero S = tt

index : ∀{A}{B}
   → (S : Setᵒ)
   → Fun A B Wellfounded NotDownClosed
index S = record { fun = λ P b → (S)₀
      ; good = wellfounded-index
      ; ext = extensional-index
      ; down = ttᵖ
      ; ez = λ P x x₁ → tt }
