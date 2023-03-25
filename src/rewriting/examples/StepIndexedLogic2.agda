{-# OPTIONS --without-K --rewriting #-}

{-
 Based on the development of Logical step-indexed logical relation
 by Philip Wadler (June 1, 2022)

 Also based on "An Indexed Model of Recursive Types"
 by Appel and McAllester.
-}
module rewriting.examples.StepIndexedLogic2 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; s≤s-injective; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import rewriting.examples.IfAndOnlyIf

{- Step Indexed Propositions and Predicates -}

Setₒ : Set₁
Setₒ = ℕ → Set

Predₒ : Set → Set₁
Predₒ A = A → ℕ → Set

⊥ₒ : Setₒ
⊥ₒ zero     =  ⊤
⊥ₒ (suc n)  =  ⊥

⊤ₒ : Setₒ
⊤ₒ n  =  ⊤

infixr 7 _×ₒ_
_×ₒ_ : Setₒ → Setₒ → Setₒ
(P ×ₒ Q) n  = (P n) × (Q n)

infixr 7 _⊎ₒ_
_⊎ₒ_ : Setₒ → Setₒ → Setₒ
(P ⊎ₒ Q) n  = (P n) ⊎ (Q n)

infixr 6 _→ₒ_
_→ₒ_ : Setₒ → Setₒ → Setₒ
(P →ₒ Q) n  = ∀ k → k ≤ n → P k → Q k

∀ₒ : ∀{A} → (A → Setₒ) → Setₒ
∀ₒ {A} F n = ∀ (a : A) → F a n

infixr 8 _ₒ
_ₒ  : Set → Setₒ
(p ₒ) zero = ⊤
(p ₒ) (suc n) = p

▷ₒ_ : Setₒ → Setₒ
(▷ₒ P) n =  ∀ k → k < n → P k

⊤ₚ : ∀{A} → Predₒ A
⊤ₚ x = ⊤ₒ

⊥ₚ : ∀{A} → Predₒ A
⊥ₚ x = ⊥ₒ

infixr 7 _×ₚ_
_×ₚ_ : ∀{A} → Predₒ A → Predₒ A → Predₒ A
(P ×ₚ Q) v  =  (P v) ×ₒ (Q v)

infixr 7 _⊎ₚ_
_⊎ₚ_ : ∀{A} → Predₒ A → Predₒ A → Predₒ A
(P ⊎ₚ Q) v  =  (P v) ⊎ₒ (Q v)

infixr 6 _→ₚ_
_→ₚ_ : ∀{A} → Predₒ A → Predₒ A → Predₒ A
(P →ₚ Q) v = P v →ₒ Q v

∀ₚ : ∀{A : Set}{B} → (A → Predₒ B) → Predₒ B
∀ₚ {A} F x = ∀ₒ(λ v → F v x)

▷ₚ : ∀{A} → Predₒ A → Predₒ A
▷ₚ P v = ▷ₒ (P v)

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

-- μₚ : ∀ {A} → (Predₒ A → Predₒ A) → Predₒ A
-- (μₚ F) x k = iter (suc k) F ⊤ₚ x k

{- Step Indexed Propositions and Predicates
   packaged with down-closed and true-at-zero.
 -}

downClosed : (ℕ → Set) → Set
downClosed P = ∀ n → P n → ∀ k → k ≤ n → P k

record Setᵒ : Set₁ where
  field
    # : Setₒ
    down : downClosed #
    tz : # 0
open Setᵒ

downClosedᵖ : ∀{A : Set} → (A → ℕ → Set) → Set
downClosedᵖ P = ∀ v → downClosed (P v)

record Predᵒ (A : Set) : Set₁ where
  field
    # : A → ℕ → Set -- or Set → Setᵒ?
    down  : downClosedᵖ #
    tz : ∀ v → # v 0
open Predᵒ

⊥ᵒ : Setᵒ
⊥ᵒ = record { # = ⊥ₒ
            ; down = λ { zero ⊥n .zero z≤n → tt}
            ; tz = tt
            }

⊤ᵒ : Setᵒ
⊤ᵒ = record { # = ⊤ₒ
            ; down = λ n _ k _ → tt
            ; tz = tt
            }

infixr 7 _×ᵒ_
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ×ᵒ Q = record { # = # P ×ₒ # Q
                ; down = λ k (Pk , Qk) j j≤k →
                          (down P k Pk j j≤k) , (down Q k Qk j j≤k)
                ; tz = (tz P) , (tz Q)
                }

infixr 7 _⊎ᵒ_
_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ⊎ᵒ Q = record { # = # P ⊎ₒ # Q
                ; down = λ { k (inj₁ Pk) j j≤k → inj₁ (down P k Pk j j≤k)
                           ; k (inj₂ Qk) j j≤k → inj₂ (down Q k Qk j j≤k)}
                ; tz = inj₁ (tz P)
                }

infixr 6 _→ᵒ_
_→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P →ᵒ Q = record { # = λ k → ∀ j → j ≤ k → # P j → # Q j
                ; down = λ k P→Q j j≤k i i≤j Pi → P→Q i (≤-trans i≤j j≤k) Pi
                ; tz = λ { .zero z≤n _ → tz Q}
                }

∀ᵒ : ∀{A} → Predᵒ A → Setᵒ
∀ᵒ{A} P = record { # = λ k → ∀ a → # P a k
                 ; down = λ k ∀Pk j j≤k a → down P a k (∀Pk a) j j≤k
                 ; tz = tz P
                 }

infixr 8 _ᵒ
_ᵒ  : Set → Setᵒ
S ᵒ = record { # = S ₒ
             ; down = λ { k Sk zero j≤k → tt
                        ; (suc k) Sk (suc j) j≤k → Sk}
             ; tz = tt
             }

infixr 8 ▷ᵒ_
▷ᵒ_ : Setᵒ → Setᵒ
▷ᵒ P = record { # = ▷ₒ # P
              ; down = λ n ▷Pn k k≤n j j<k → ▷Pn j (≤-trans j<k k≤n)
              ; tz = λ k ()
              }

↓ₒ : ℕ → Setᵒ → Setₒ
↓ₒ k S zero = ⊤
↓ₒ k S (suc j) = suc j < k × (# S j)

↓ᵒ : ℕ → Setᵒ → Setᵒ
↓ᵒ k S = record { # = ↓ₒ k S 
                ; down = λ { zero x .zero z≤n → tt
                           ; (suc n) (sn<k , Sn) zero j≤n → tt
                           ; (suc n) (sn<k , Sn) (suc j) (s≤s j≤n) →
                           (≤-trans (s≤s (s≤s j≤n)) sn<k) , (down S n Sn j j≤n)}
                ; tz = tt
                }

apply : ∀{A} → Predᵒ A → A → Setᵒ
apply P v = record { # = λ j → # P v j
                   ; down = down P v
                   ; tz = tz P v
                   }

⊤ᵖ : ∀{A} → Predᵒ A
⊤ᵖ {A} = record { # = ⊤ₚ ; down = λ v n _ k _ → tt ; tz = λ v → tt }

⊥ᵖ : ∀{A} → Predᵒ A
⊥ᵖ {A} = record { # = ⊥ₚ
                ; down = λ { a zero ⊥n .zero z≤n → tt}
                ; tz = λ v → tt }

infixr 7 _×ᵖ_
_×ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
P ×ᵖ Q = let P×Q = λ v → apply P v ×ᵒ apply Q v in
         record { # = λ v → # (P×Q v)
                ; down = λ v → down (P×Q v)
                ; tz = λ v → tz (P×Q v) }

infixr 7 _⊎ᵖ_
_⊎ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
P ⊎ᵖ Q = let P⊎Q = λ v → apply P v ⊎ᵒ apply Q v in
         record { # = λ v → # (P⊎Q v)
                ; down = λ v → down (P⊎Q v)
                ; tz = λ v → tz (P⊎Q v) }


infixr 6 _→ᵖ_
_→ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
P →ᵖ Q = let P→Q = λ a → (apply P a →ᵒ apply Q a) in
         record { # = λ a → # (P→Q a)
                ; down = λ a → down (apply P a →ᵒ apply Q a)
                ; tz = λ a → tz (apply P a →ᵒ apply Q a)
                }

-- TODO: find a better name for the following
cvt : ∀{A}{B}
   → (A → Predᵒ B)
     -------------
   → (B → Predᵒ A)
cvt F b = record { # = λ a → # (F a) b
                 ; down = λ a → down (F a) b
                 ; tz = λ a → tz (F a) b }   

∀ᵖ : ∀{A : Set}{B} → (A → Predᵒ B) → Predᵒ B
∀ᵖ {A}{B} F = let ∀P = λ b → ∀ᵒ {A} (cvt F b) in
              record { # = λ b → # (∀P b)
                     ; down = λ b → down (∀P b)
                     ; tz = λ b → tz (∀P b)
                     }

infixr 8 _ᵖ
_ᵖ  : Set → ∀{A} → Predᵒ A
(S ᵖ) {A} = let Sᵖ = λ a → (S ᵒ) in
            record { # = λ a → # (Sᵖ a)
                   ; down = λ a → down (Sᵖ a)
                   ; tz = λ a → tz (Sᵖ a) }

▷ᵖ : ∀{A} → Predᵒ A → Predᵒ A
▷ᵖ P = let ▷P = λ v → ▷ᵒ (apply P v) in
       record { # = λ v → # (▷P v)
              ; down = λ v → down (▷P v)
              ; tz = λ v → tz (▷P v) }

↓ᵖ : ℕ → ∀{A} → Predᵒ A → Predᵒ A
↓ᵖ k P = record { # = λ v → # (↓ᵒ k (apply P v))
                ; down = λ v → down (↓ᵒ k (apply P v))
                ; tz = λ v → tt
                }

{-----  Reasoning about Equality on Step Indexed Sets  ---------}

infix 4 _≡ₒ_
_≡ₒ_ : Setₒ → Setₒ → Set
S ≡ₒ T = ∀ i → S i ⇔ T i

≡ₒ-refl : ∀{S T : Setₒ}
  → S ≡ T
  → S ≡ₒ T
≡ₒ-refl refl i = (λ x → x) , (λ x → x)

≡ₒ-sym : ∀{S T : Setₒ}
  → S ≡ₒ T
  → T ≡ₒ S
≡ₒ-sym ST i = (proj₂ (ST i)) , (proj₁ (ST i))

≡ₒ-trans : ∀{S T R : Setₒ}
  → S ≡ₒ T
  → T ≡ₒ R
  → S ≡ₒ R
≡ₒ-trans ST TR i = (λ z → proj₁ (TR i) (proj₁ (ST i) z))
                 , (λ z → proj₂ (ST i) (proj₂ (TR i) z))

infixr 2 _≡ₒ⟨_⟩_
infix  3 _QEDₒ
  
_≡ₒ⟨_⟩_ : 
    (P : Setₒ)
   {Q : Setₒ}
  → P ≡ₒ Q
  → {R : Setₒ}
  → Q ≡ₒ R
  → P ≡ₒ R
P ≡ₒ⟨ P≡Q ⟩ Q≡R = ≡ₒ-trans P≡Q Q≡R

_QEDₒ :
    (P : Setₒ)
  → P ≡ₒ P
P QEDₒ = ≡ₒ-refl refl

example : ∀{P Q : Setᵒ} → # (P ×ᵒ Q) ≡ₒ # (Q ×ᵒ P)
example {P}{Q} = 
  # (P ×ᵒ Q)          ≡ₒ⟨ (λ i → (λ {(Pi , Qi) → Qi , Pi})
                               , (λ {(Qi , Pi) → Pi , Qi})) ⟩
  # (Q ×ᵒ P)
  QEDₒ


{-----  Reasoning about Equality on Step Indexed Predicates  ---------}

infix 2 _≡ₚ_
_≡ₚ_ : ∀{A} → Predₒ A → Predₒ A → Set
P ≡ₚ Q = ∀ v → P v ≡ₒ Q v

≡ₚ-refl : ∀{A}{P Q : Predₒ A}
  → P ≡ Q
  → P ≡ₚ Q
≡ₚ-refl refl x = ≡ₒ-refl refl

≡ₚ-sym : ∀{A}{P Q : Predₒ A}
  → P ≡ₚ Q
  → Q ≡ₚ P
≡ₚ-sym PQ x = ≡ₒ-sym (PQ x)
  
≡ₚ-trans : ∀{A : Set}{P Q R : Predₒ A}
  → P ≡ₚ Q
  → Q ≡ₚ R
  → P ≡ₚ R
≡ₚ-trans{R} PQ QR x = ≡ₒ-trans (PQ x) (QR x)

infixr 2 _≡ₚ⟨_⟩_
infix  3 _QEDₚ
  
_≡ₚ⟨_⟩_ : ∀{A}
  → (P : Predₒ A)
  → ∀{Q} → P ≡ₚ Q
  → ∀{R} → Q ≡ₚ R
  → P ≡ₚ R
P ≡ₚ⟨ P≡Q ⟩ Q≡R = ≡ₚ-trans P≡Q Q≡R

_QEDₚ : ∀{A}
  → (P : Predₒ A)
  → P ≡ₚ P
P QEDₚ = ≡ₚ-refl refl

cong-→ᵖ : ∀{A}{P P′ Q Q′ : Predₒ A}
   → P ≡ₚ P′
   → Q ≡ₚ Q′
   → (P →ₚ Q)  ≡ₚ  (P′ →ₚ Q′)
cong-→ᵖ PP′ QQ′ v k = (λ P→Q j j<k P′vj → let Pvj = proj₂ (PP′ v j) P′vj in
                                          let Qvj = P→Q j j<k Pvj in
                                          let Q′vj = proj₁ (QQ′ v j) Qvj in
                                          Q′vj)
                   , (λ P′→Q′ j j<k Pvj → let P′vj = proj₁ (PP′ v j) Pvj in
                                          let Q′vj = P′→Q′ j j<k P′vj in
                                          let Qvj = proj₂ (QQ′ v j) Q′vj in
                                          Qvj)

cong-×ᵖ : ∀{A}{P P′ Q Q′ : Predₒ A}
   → P ≡ₚ P′
   → Q ≡ₚ Q′
   → P ×ₚ Q  ≡ₚ  P′ ×ₚ Q′
cong-×ᵖ {A}{P}{P′}{Q}{Q′} PP′ QQ′ v k = to , fro
  where
  to : (P ×ₚ Q) v k → (P′ ×ₚ Q′) v k
  to (Pvk , Qvk) = (proj₁ (PP′ v k) Pvk) , (proj₁ (QQ′ v k) Qvk)
  fro  : (P′ ×ₚ Q′) v k → (P ×ₚ Q) v k
  fro (P′vk , Q′vk) = (proj₂ (PP′ v k) P′vk) , (proj₂ (QQ′ v k) Q′vk)

cong-⊎ᵖ : ∀{A}{P P′ Q Q′ : Predₒ A}
   → P ≡ₚ P′
   → Q ≡ₚ Q′
   → P ⊎ₚ Q  ≡ₚ  P′ ⊎ₚ Q′
cong-⊎ᵖ {A}{P}{P′}{Q}{Q′} PP′ QQ′ v k = to , fro
  where
  to : (P ⊎ₚ Q) v k → (P′ ⊎ₚ Q′) v k
  to (inj₁ Pvk) = inj₁ (proj₁ (PP′ v k) Pvk)
  to (inj₂ Qvk) = inj₂ (proj₁ (QQ′ v k) Qvk)
  fro : (P′ ⊎ₚ Q′) v k → (P ⊎ₚ Q) v k
  fro (inj₁ P′vk) = inj₁ (proj₂ (PP′ v k) P′vk)
  fro (inj₂ Q′vk) = inj₂ (proj₂ (QQ′ v k) Q′vk)

cong-▷ᵖ : ∀{A}{P P′ : Predₒ A}
   → P ≡ₚ P′
   → ▷ₚ P ≡ₚ ▷ₚ P′
cong-▷ᵖ PP′ v k = (λ {▷Pvk j j<k → proj₁ (PP′ v j) (▷Pvk j j<k)})
                , (λ ▷P′vk j j<k → proj₂ (PP′ v j) (▷P′vk j j<k))

{------------ Continuous and Wellfounded Functions on Step Indexed Predicates -}

congᵖ : ∀{A}{B} (F : Predᵒ A → Predᵒ B) → Set₁
congᵖ F = ∀ P Q → # P ≡ₚ # Q → #(F P) ≡ₚ #(F Q)

continuous : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
continuous F = ∀ P k → #(↓ᵖ k (F P)) ≡ₚ #(↓ᵖ k (F (↓ᵖ k P)))

wellfounded : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
wellfounded F = ∀ P k → #(↓ᵖ (suc k) (F P)) ≡ₚ #(↓ᵖ (suc k) (F (↓ᵖ k P)))

cong-↓ : ∀{A}
    (k : ℕ)
  → congᵖ{A}{A} (↓ᵖ k)
cong-↓ k P Q PQ x zero = (λ x → tt) , (λ x → tt)
cong-↓ k P Q PQ x (suc i) =
     (λ { (si<k , Pxi) → si<k , (proj₁ (PQ x i) Pxi)})
   , (λ {(si<k , Qxi) → si<k , proj₂ (PQ x i) Qxi})
                
{- ↓ᵖ is idempotent -}
lemma17 : ∀{A}
     (P : Predᵒ A)
   → (k : ℕ)
   → #(↓ᵖ k (↓ᵖ (suc k) P)) ≡ₚ #(↓ᵖ k P)
lemma17{A} P k x i = {!!}
    -- (λ { (fst , snd) → fst , proj₂ snd})
    -- , λ { (fst , snd) → fst , ((≤-trans fst (n≤1+n k)) , snd)}


↓-zero : ∀{A}
   → (P : Predᵒ A)
   → (Q : Predᵒ A)
   → #(↓ᵖ 0 P) ≡ₚ #(↓ᵖ 0 Q)
↓-zero P Q v i = {!!}
   --   (λ {(z≤n , Pvi) → z≤n , (tz Q v)})
   -- , λ {(z≤n , Qvi) → z≤n , (tz P v)}

wellfounded⇒continuous : ∀{A}{B}
   → (F : Predᵒ A → Predᵒ B)
   → wellfounded F
   → congᵖ F
   → continuous F
wellfounded⇒continuous F wfF congF P zero = ↓-zero (F P) (F (↓ᵖ zero P))
wellfounded⇒continuous F wfF congF P (suc k) =
    #(↓ᵖ (suc k) (F P))                       ≡ₚ⟨ wfF _ k ⟩
    #(↓ᵖ (suc k) (F (↓ᵖ k P)))
             ≡ₚ⟨ cong-↓ (suc k) (F (↓ᵖ k P)) (F (↓ᵖ k (↓ᵖ (suc k) P)))
                 (congF ((↓ᵖ k P)) ((↓ᵖ k (↓ᵖ (suc k) P))) (≡ₚ-sym (lemma17 P k))) ⟩
    #(↓ᵖ (suc k) (F (↓ᵖ k (↓ᵖ (suc k) P))))   ≡ₚ⟨ ≡ₚ-sym (wfF _ k) ⟩
    #(↓ᵖ (suc k) (F (↓ᵖ (suc k) P)))
    QEDₚ

data Kind : Set where
  Continuous : Kind
  Wellfounded : Kind

choose : Kind → Kind → Kind
choose Continuous Continuous = Continuous
choose Continuous Wellfounded = Continuous
choose Wellfounded Continuous = Continuous
choose Wellfounded Wellfounded = Wellfounded

goodness : Kind → ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
goodness Continuous F = continuous F
goodness Wellfounded F = wellfounded F

record Fun (A B : Set) (κ : Kind)
       : Set₁ where
  field
    fun : Predᵒ A → Predᵒ B
    good : goodness κ fun
    congr : congᵖ fun
open Fun public

{------- Implication --------}

infixr 6 _→ᶠ_
_→ᶠ_ : ∀{A B}{kF kG}
   → Fun A B kF
   → Fun A B kG
   → Fun A B (choose kF kG)
_→ᶠ_ {A}{B}{kF}{kG} F G =
  record { fun = λ P → fun F P →ᵖ fun G P
         ; good = goodness-→ kF kG (fun F) (fun G) (good F) (congr F)
                        (good G) (congr G)
         ; congr = cong-→ (fun F) (fun G) (congr F) (congr G) }
  where
  down-fun : ∀{A} (P Q : Predᵒ A){k}
     → #(↓ᵖ k (P →ᵖ Q)) ≡ₚ #(↓ᵖ k ((↓ᵖ k P) →ᵖ (↓ᵖ k Q)))
  down-fun {A} P Q {k} x i = {!!}
   --   (λ {(i≤k , PQxi) → i≤k , (λ {j j≤i (j≤k , Pxj) → j≤k , (PQxi j j≤i Pxj)})})
   -- , (λ {(i≤k , P→Q) →
   --      i≤k , (λ j j≤i Pxj →
   --                 let ↓kQ = P→Q j j≤i ((≤-trans j≤i i≤k) , Pxj) in
   --                 proj₂ ↓kQ)})

  continuous-→ : ∀{A}{B}(F G : Predᵒ A → Predᵒ B)
     → continuous F
     → continuous G
     → continuous (λ P → F P →ᵖ G P)
  continuous-→ {A}{B} F G neF neG P k =
     #(↓ᵖ k (F P →ᵖ G P))                             ≡ₚ⟨ down-fun (F P) (G P) ⟩
     #(↓ᵖ k (↓ᵖ k (F P) →ᵖ ↓ᵖ k (G P)))
                           ≡ₚ⟨ cong-↓ k (↓ᵖ k (F P) →ᵖ ↓ᵖ k (G P))
                                        (↓ᵖ k (F (↓ᵖ k P)) →ᵖ ↓ᵖ k (G (↓ᵖ k P)))
                                        (cong-→ᵖ (neF _ k) (neG _ k)) ⟩
     #(↓ᵖ k (↓ᵖ k (F (↓ᵖ k P)) →ᵖ ↓ᵖ k (G (↓ᵖ k P))))
                               ≡ₚ⟨ ≡ₚ-sym (down-fun (F (↓ᵖ k P)) (G (↓ᵖ k P))) ⟩
      #(↓ᵖ k (F (↓ᵖ k P) →ᵖ G (↓ᵖ k P)))
      QEDₚ

  wellfounded-→ : ∀{A}{B}(F G : Predᵒ A → Predᵒ B)
     → wellfounded F
     → wellfounded G
     → wellfounded (λ P → F P →ᵖ G P)
  wellfounded-→ {A}{B} F G wfF wfG P k =
      #(↓ᵖ (suc k) (F P →ᵖ G P))                      ≡ₚ⟨ down-fun (F P) (G P) ⟩
      #(↓ᵖ (suc k) (↓ᵖ (suc k) (F P) →ᵖ ↓ᵖ (suc k) (G P)))
               ≡ₚ⟨ cong-↓ (suc k)
                          (↓ᵖ (suc k) (F P) →ᵖ ↓ᵖ (suc k) (G P))
                          (↓ᵖ (suc k) (F (↓ᵖ k P)) →ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P)))
                          (cong-→ᵖ (wfF _ k) (wfG _ k)) ⟩
      #(↓ᵖ (suc k) (↓ᵖ (suc k) (F (↓ᵖ k P)) →ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P))))
                               ≡ₚ⟨ ≡ₚ-sym (down-fun (F (↓ᵖ k P)) (G (↓ᵖ k P))) ⟩
      #(↓ᵖ (suc k) (F (↓ᵖ k P) →ᵖ G (↓ᵖ k P)))
      QEDₚ

  goodness-→ : ∀ (kf kg : Kind) {A}{B}(F G : Predᵒ A → Predᵒ B)
     → goodness kf F
     → congᵖ F
     → goodness kg G
     → congᵖ G
     → goodness (choose kf kg) (λ P → F P →ᵖ G P)
  goodness-→ Continuous Continuous F G gf congF gg congG  =
      continuous-→ F G gf gg
  goodness-→ Continuous Wellfounded F G gf congF gg congG =
      continuous-→ F G gf (wellfounded⇒continuous G gg congG)
  goodness-→ Wellfounded Continuous F G gf congF gg congG =
      continuous-→ F G (wellfounded⇒continuous F gf congF) gg
  goodness-→ Wellfounded Wellfounded F G gf congF gg congG =
      wellfounded-→ F G gf gg

  cong-→ : ∀{A}{B}
       (F G : Predᵒ A → Predᵒ B)
     → congᵖ F
     → congᵖ G
     → congᵖ (λ P → F P →ᵖ G P)
  cong-→ F G congF congG P Q PQ b i =
      (λ FP→GP j j≤i FQbj →
         let FP≡FQ = congF P Q PQ b j in
         let GP≡GQ = congG P Q PQ b j in
         let GPbj = FP→GP j j≤i (proj₂ FP≡FQ FQbj) in
         let GQbj = proj₁ GP≡GQ GPbj in
         GQbj)
    , (λ FQ→GQ j j≤i FPbj →
        let FP≡FQ = congF P Q PQ b j in
        let GP≡GQ = congG P Q PQ b j in
        let GQbj = FQ→GQ j j≤i (proj₁ FP≡FQ FPbj) in
        let GPbj = proj₂ GP≡GQ GQbj in
        GPbj)

                
{- Conjunction -}

infixr 6 _×ᶠ_
_×ᶠ_ : ∀{A}{B}{kF kG}
   → Fun A B kF
   → Fun A B kG
   → Fun A B (choose kF kG)
_×ᶠ_ {A}{B}{kF}{kG} F G =
  record { fun = λ P → (fun F) P ×ᵖ (fun G) P
         ; good = goodness-× kF kG (fun F) (fun G) (good F) (congr F)
                       (good G) (congr G)
         ; congr = cong-× (fun F) (fun G) (congr F) (congr G)
         }
  where
  down-× : ∀{A}(P Q : Predᵒ A){k}
     → #(↓ᵖ k (P ×ᵖ Q)) ≡ₚ #(↓ᵖ k ((↓ᵖ k P) ×ᵖ (↓ᵖ k Q)))
  down-× {A} P Q {k} x i = {!!}
      -- (λ { (i≤k , (Pxi , Qxi)) → i≤k , (i≤k , Pxi) , i≤k , Qxi})
      -- , (λ {(i≤k , ((_ , Pxi) , (_ , Qxi))) → i≤k , Pxi , Qxi})
                           
  continuous-× : ∀{A}{B}(F G : Predᵒ A → Predᵒ B)
     → continuous F
     → continuous G
     → continuous (λ P → F P ×ᵖ G P)
  continuous-× {A}{B} F G neF neG P k =
      #(↓ᵖ k (F P ×ᵖ G P))                              ≡ₚ⟨ down-× (F P) (G P) ⟩
      #(↓ᵖ k (↓ᵖ k (F P) ×ᵖ ↓ᵖ k (G P)))
           ≡ₚ⟨ cong-↓ k (↓ᵖ k (F P) ×ᵖ ↓ᵖ k (G P))
                        (↓ᵖ k (F (↓ᵖ k P)) ×ᵖ ↓ᵖ k (G (↓ᵖ k P)))
                        (cong-×ᵖ (neF _ k) (neG _ k)) ⟩
      #(↓ᵖ k (↓ᵖ k (F (↓ᵖ k P)) ×ᵖ ↓ᵖ k (G (↓ᵖ k P))))
           ≡ₚ⟨ ≡ₚ-sym (down-× (F (↓ᵖ k P)) (G (↓ᵖ k P))) ⟩
      #(↓ᵖ k (F (↓ᵖ k P) ×ᵖ G (↓ᵖ k P)))
      QEDₚ

  wellfounded-× : ∀{A}{B}(F G : Predᵒ A → Predᵒ B)
     → wellfounded F
     → wellfounded G
     → wellfounded (λ P → F P ×ᵖ G P)
  wellfounded-× {A}{B} F G wfF wfG P k =
      #(↓ᵖ (suc k) (F P ×ᵖ G P))                       ≡ₚ⟨ down-× (F P) (G P) ⟩
      #(↓ᵖ (suc k) (↓ᵖ (suc k) (F P) ×ᵖ ↓ᵖ (suc k) (G P)))
           ≡ₚ⟨ cong-↓ (suc k)
                      (↓ᵖ (suc k) (F P) ×ᵖ ↓ᵖ (suc k) (G P))
                      (↓ᵖ (suc k) (F (↓ᵖ k P)) ×ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P)))
                      (cong-×ᵖ (wfF _ k) (wfG _ k)) ⟩
      #(↓ᵖ (suc k) (↓ᵖ (suc k) (F (↓ᵖ k P)) ×ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P))))
           ≡ₚ⟨ ≡ₚ-sym (down-× (F (↓ᵖ k P)) (G (↓ᵖ k P))) ⟩
      #(↓ᵖ (suc k) (F (↓ᵖ k P) ×ᵖ G (↓ᵖ k P)))
      QEDₚ

  goodness-× : ∀ (kf kg : Kind) {A}{B}(F G : Predᵒ A → Predᵒ B)
     → goodness kf F
     → congᵖ F
     → goodness kg G
     → congᵖ G
     → goodness (choose kf kg) (λ P → F P ×ᵖ G P)
  goodness-× Continuous Continuous F G gf congF gg congG  =
      continuous-× F G gf gg
  goodness-× Continuous Wellfounded F G gf congF gg congG =
      continuous-× F G gf (wellfounded⇒continuous G gg congG)
  goodness-× Wellfounded Continuous F G gf congF gg congG =
      continuous-× F G (wellfounded⇒continuous F gf congF) gg
  goodness-× Wellfounded Wellfounded F G gf congF gg congG =
      wellfounded-× F G gf gg

  cong-× : ∀{A}{B}
       (F G : Predᵒ A → Predᵒ B)
     → congᵖ F
     → congᵖ G
     → congᵖ (λ P → F P ×ᵖ G P)
  cong-× F G congF congG P Q PQ x i = 
    (λ {(FPxi , GPxi) →
          let FPxi⇔FQxi = congF P Q PQ x i in
          let GPxi⇔GQxi = congG P Q PQ x i in
          proj₁ FPxi⇔FQxi FPxi , proj₁ GPxi⇔GQxi GPxi})
    , (λ {(FQxi , GQxi) →
          let FPxi⇔FQxi = congF P Q PQ x i in
          let GPxi⇔GQxi = congG P Q PQ x i in
          proj₂ FPxi⇔FQxi FQxi  , proj₂ GPxi⇔GQxi GQxi})

{- Disjunction -}

infixr 6 _⊎ᶠ_
_⊎ᶠ_ : ∀{A}{B}{kF kG}
   → Fun A B kF
   → Fun A B kG
   → Fun A B (choose kF kG)
_⊎ᶠ_ {A}{B}{kF}{kG} F G =
  record { fun = λ P → (fun F) P ⊎ᵖ (fun G) P
         ; good = goodness-⊎ kF kG (fun F) (fun G) (good F) (congr F)
                      (good G) (congr G)
         ; congr = cong-⊎ (fun F) (fun G) (congr F) (congr G)
         }
  where
  down-⊎ : ∀{A}(P Q : Predᵒ A){k}
     → #(↓ᵖ k (P ⊎ᵖ Q)) ≡ₚ #(↓ᵖ k ((↓ᵖ k P) ⊎ᵖ (↓ᵖ k Q)))
  down-⊎ {A} P Q {k} x i = {!!}
    -- where
    -- to : #(↓ᵖ k (P ⊎ᵖ Q)) x i → #(↓ᵖ k (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q)) x i
    -- to (i<k , inj₁ Pi) = i<k , inj₁ (i<k , Pi)
    -- to (i<k , inj₂ Qi) = i<k , inj₂ (i<k , Qi)

    -- fro : #(↓ᵖ k (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q)) x i → #(↓ᵖ k (P ⊎ᵖ Q)) x i
    -- fro (i<k , inj₁ Pi) = i<k , inj₁ (proj₂ Pi)
    -- fro (i<k , inj₂ Qi) = i<k , inj₂ (proj₂ Qi)

  continuous-⊎ : ∀{A}{B}(F G : Predᵒ A → Predᵒ B)
     → continuous F
     → continuous G
     → continuous (λ P → F P ⊎ᵖ G P)
  continuous-⊎ {A}{B} F G neF neG P k =
      #(↓ᵖ k (F P ⊎ᵖ G P))                              ≡ₚ⟨ down-⊎ (F P) (G P)⟩
      #(↓ᵖ k (↓ᵖ k (F P) ⊎ᵖ ↓ᵖ k (G P)))
           ≡ₚ⟨ cong-↓ k
                      (↓ᵖ k (F P) ⊎ᵖ ↓ᵖ k (G P))
                      (↓ᵖ k (F (↓ᵖ k P)) ⊎ᵖ ↓ᵖ k (G (↓ᵖ k P)))
                      (cong-⊎ᵖ (neF _ k) (neG _ k)) ⟩
      #(↓ᵖ k (↓ᵖ k (F (↓ᵖ k P)) ⊎ᵖ ↓ᵖ k (G (↓ᵖ k P))))
           ≡ₚ⟨ ≡ₚ-sym (down-⊎ (F (↓ᵖ k P)) (G (↓ᵖ k P))) ⟩
      #(↓ᵖ k (F (↓ᵖ k P) ⊎ᵖ G (↓ᵖ k P)))
      QEDₚ

  wellfounded-⊎ : ∀{A}{B}(F G : Predᵒ A → Predᵒ B)
     → wellfounded F
     → wellfounded G
     → wellfounded (λ P → F P ⊎ᵖ G P)
  wellfounded-⊎ {A}{B} F G wfF wfG P k =
      #(↓ᵖ (suc k) (F P ⊎ᵖ G P))                        ≡ₚ⟨ down-⊎ (F P) (G P)⟩
      #(↓ᵖ (suc k) (↓ᵖ (suc k) (F P) ⊎ᵖ ↓ᵖ (suc k) (G P)))
           ≡ₚ⟨ cong-↓ (suc k)
                      (↓ᵖ (suc k) (F P) ⊎ᵖ ↓ᵖ (suc k) (G P))
                      (↓ᵖ (suc k) (F (↓ᵖ k P)) ⊎ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P)))
                      (cong-⊎ᵖ (wfF _ k) (wfG _ k)) ⟩
      #(↓ᵖ (suc k) (↓ᵖ (suc k) (F (↓ᵖ k P)) ⊎ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P))))
           ≡ₚ⟨ ≡ₚ-sym (down-⊎ (F (↓ᵖ k P)) (G (↓ᵖ k P))) ⟩
      #(↓ᵖ (suc k) (F (↓ᵖ k P) ⊎ᵖ G (↓ᵖ k P)))
      QEDₚ

  goodness-⊎ : ∀ (kf kg : Kind) {A}{B}(F G : Predᵒ A → Predᵒ B)
     → goodness kf F
     → congᵖ F
     → goodness kg G
     → congᵖ G
     → goodness (choose kf kg) (λ P → F P ⊎ᵖ G P)
  goodness-⊎ Continuous Continuous F G gf extF gg extG  =
      continuous-⊎ F G gf gg
  goodness-⊎ Continuous Wellfounded F G gf extF gg extG =
      continuous-⊎ F G gf (wellfounded⇒continuous G gg extG)
  goodness-⊎ Wellfounded Continuous F G gf extF gg extG =
      continuous-⊎ F G (wellfounded⇒continuous F gf extF) gg
  goodness-⊎ Wellfounded Wellfounded F G gf extF gg extG =
      wellfounded-⊎ F G gf gg

  cong-⊎ : ∀{A}{B}
       (F G : Predᵒ A → Predᵒ B)
     → congᵖ F
     → congᵖ G
     → congᵖ (λ P → F P ⊎ᵖ G P)
  cong-⊎ {A}{B} F G extF extG P Q PQ x i = to , fro
    where
    to : #(F P ⊎ᵖ G P) x i → #(F Q ⊎ᵖ G Q) x i
    to (inj₁ FPi) = inj₁ (proj₁ (extF P Q PQ x i) FPi)
    to (inj₂ GPi) = inj₂ (proj₁ (extG P Q PQ x i) GPi)

    fro : #(F Q ⊎ᵖ G Q) x i → #(F P ⊎ᵖ G P) x i
    fro (inj₁ FQi) = inj₁ (proj₂ (extF P Q PQ x i) FQi)
    fro (inj₂ GQi) = inj₂ (proj₂ (extG P Q PQ x i) GQi)

{- Forall -}

∀ᶠ : ∀{A B C : Set}{K}
   → (A → Fun B C K)
   → Fun B C K
∀ᶠ {A}{B}{C}{K} F =
  record { fun = λ P → ∀ᵖ {A} λ a → fun (F a) P
         ; good = goodness-all F
         ; congr = cong-all F
         }
  where
  continuous-all : ∀{A B C}
     → (F : A → Fun B C Continuous)
     → continuous (λ P → ∀ᵖ (λ a → fun (F a) P))
  continuous-all F P k x i = {!!}
    -- (λ { (i<k , ∀FP) →
    --    i<k , (λ v → let xx = proj₁ (good (F v) P k x i) (i<k , (∀FP v)) in
    --                 proj₂ xx)})
    -- , (λ {(i<k , ∀F↓P) →
    --    i<k , (λ v → let xx = proj₂ (good (F v) P k x i) (i<k , (∀F↓P v)) in
    --                 proj₂ xx)})
  
  wellfounded-all : ∀{A B C}
     → (F : A → Fun B C Wellfounded)
     → wellfounded (λ P → ∀ᵖ (λ a → fun (F a) P))
  wellfounded-all F P k x i = {!!}
      -- (λ{(i≤k , ∀FP) →
      --     i≤k
      --     , (λ v → let xx = proj₁ (good (F v) P k x i) (i≤k , (∀FP v)) in
      --              proj₂ xx)})
      -- , λ {(i≤k , ∀F↓P) →
      --     i≤k
      --     , (λ v → let xx = proj₂ (good (F v) P k x i) (i≤k , (∀F↓P v)) in
      --              proj₂ xx)}
  
  goodness-all : ∀{A B C}{K}
     → (F : A → Fun B C K)
     → goodness K (λ P → ∀ᵖ (λ a → fun (F a) P))
  goodness-all {A} {B} {C} {Continuous} F = continuous-all F
  goodness-all {A} {B} {C} {Wellfounded} F = wellfounded-all F

  cong-all : ∀{A B C}{K}
     → (F : A → Fun B C K)
     → congᵖ (λ P → ∀ᵖ (λ a → fun (F a) P))
  cong-all F P Q PQ c i =
    (λ ∀FP v → proj₁ (congr (F v) P Q PQ c i) (∀FP v))
    , (λ ∀FQ v → proj₂ (congr (F v) P Q PQ c i) (∀FQ v))

{- Constant -}

_ᶠ : ∀{A}{B}
   → Set
   → Fun A B Wellfounded
(S)ᶠ = record { fun = λ P → S ᵖ
    ; good = λ P k v i → (λ x → x) , (λ x → x)
    ; congr = λ P Q _ v i → (λ x → x) , (λ x → x)
    }

{- Later -}

≤-inv : ∀{i}{j}
   → suc i ≤ suc j
   → i ≤ j
≤-inv (s≤s i≤j) = i≤j


▷ᶠ : ∀{A}{B}{kF} → Fun A B kF → Fun A B Wellfounded
▷ᶠ {A}{B}{kF} F = record { fun = (λ P → ▷ᵖ ((fun F) P))
              ; good = goodness-▷ kF (fun F) (good F) (congr F) 
              ; congr = cong-▷ (fun F) (congr F)
              }
  where
  wellfounded-▷ : ∀{A}{B} (F : Predᵒ A → Predᵒ B)
     → continuous F
     → wellfounded (λ P → ▷ᵖ (F P))
  wellfounded-▷ {A}{B} F neF P k =
      #(↓ᵖ (suc k) (▷ᵖ (F P)))                ≡ₚ⟨ EQ1 (F P) ⟩
      #(↓ᵖ (suc k) (▷ᵖ (↓ᵖ k (F P))))
              ≡ₚ⟨ cong-↓ (suc k)
                         (▷ᵖ (↓ᵖ k (F P)))
                         (▷ᵖ (↓ᵖ k (F (↓ᵖ k P))))
                         EQ2 ⟩
      #(↓ᵖ (suc k) (▷ᵖ (↓ᵖ k (F (↓ᵖ k P)))))  ≡ₚ⟨ ≡ₚ-sym (EQ1 (F (↓ᵖ k P))) ⟩
      #(↓ᵖ (suc k) (▷ᵖ (F (↓ᵖ k P))))
      QEDₚ
    where
    EQ2 : # (▷ᵖ (↓ᵖ k (F P))) ≡ₚ # (▷ᵖ (↓ᵖ k (F (↓ᵖ k P))))
    EQ2 = cong-▷ᵖ (neF _ k)

    EQ1 : (P : Predᵒ B)
       → #(↓ᵖ (suc k) (▷ᵖ P)) ≡ₚ #(↓ᵖ (suc k) (▷ᵖ (↓ᵖ k P)))
    EQ1 P v i = {!!}
    -- (λ {(i≤1+k , ▷Pvi) →
    --              i≤1+k , (λ { j (s≤s j≤i) → (≤-trans j≤i (≤-inv i≤1+k))
    --                       , (▷Pvi j (s≤s j≤i))})})
    --           ,
    --           λ {(i≤1+k , ▷Pvi) → i≤1+k ,
    --               (λ { j (s≤s j≤n) → let xx = ▷Pvi j (s≤s j≤n) in proj₂ xx})}
  
  goodness-▷ : ∀ (k : Kind) → ∀{A}{B} (F : Predᵒ A → Predᵒ B)
    → goodness k F
    → congᵖ F
    → wellfounded (λ P → ▷ᵖ (F P))
  goodness-▷ Continuous F gf extF = wellfounded-▷ F gf
  goodness-▷ Wellfounded F gf extF =
      wellfounded-▷ F (wellfounded⇒continuous F gf extF )

  cong-▷ : ∀{A}{B}
       (F : Predᵒ A → Predᵒ B)
     → congᵖ F
     → congᵖ (λ P → ▷ᵖ (F P))
  cong-▷ F congF P Q PQ x i =
        (λ x₁ k x₂ → proj₁ (congF P Q PQ x k) (x₁ k x₂))
      , (λ x₁ k x₂ → proj₂ (congF P Q PQ x k) (x₁ k x₂))

{- Lemma for defining the recursive predicate -}

lemma15a : ∀{A} (P Q : Predᵒ A){j}
  → (F : Predᵒ A → Predᵒ A)
  → wellfounded F
  → congᵖ F
  → #(↓ᵖ j (iter j F P)) ≡ₚ #(↓ᵖ j (iter j F Q))
lemma15a {A} P Q {zero} F wfF congF x i = {!!}
    -- (λ { (z≤n , _) → z≤n , (tz Q x)})
    -- ,
    -- λ {(z≤n , _) → z≤n , (tz P x)}
lemma15a {A} P Q {suc j} F wfF congF =
    #(↓ᵖ (suc j) (F (iter j F P)))
  ≡ₚ⟨ wfF (iter j F P) j  ⟩ 
    #(↓ᵖ (suc j) (F (↓ᵖ j (iter j F P))))
  ≡ₚ⟨ cong-↓ {A} (suc j)
         (F (↓ᵖ j (iter j F P))) (F (↓ᵖ j (iter j F Q)))
         (congF (↓ᵖ j (iter j F P)) (↓ᵖ j (iter j F Q))
                (lemma15a{A} P Q {j = j} F wfF congF)) ⟩
    #(↓ᵖ (suc j) (F (↓ᵖ j (iter j F Q))))
  ≡ₚ⟨ ≡ₚ-sym (wfF (iter j F Q) j) ⟩
    #(↓ᵖ (suc j) (F (iter j F Q)))
  QEDₚ

lemma15b : ∀{A}(P : Predᵒ A){j k}
  → (F : Predᵒ A → Predᵒ A)
  → wellfounded F
  → congᵖ F
  → j ≤ k
  → #(↓ᵖ j (iter j F P)) ≡ₚ #(↓ᵖ j (iter k F P))
lemma15b{A} P {j}{k} F wfF congF j≤k =
    let eq = lemma15a {A} P (iter (k ∸ j) F P) {j} F wfF congF in
    ≡ₚ-trans eq (cong-↓ j (iter j F (iter (k ∸ j) F P)) (iter k F P)
                          (≡ₚ-refl Goal))
    where
    Goal : (λ z z₁ → #(iter j F (iter (k ∸ j) F P)) z z₁)
           ≡ (λ z z₁ → #(iter k F P) z z₁)
    Goal rewrite iter-subtract{A = Predᵒ A}{P} F j k j≤k = refl

{- Recursive Predicate -}

μₚ : ∀{A} → (Predᵒ A → Predᵒ A) → Predₒ A
μₚ F a k = #(iter (suc k) F ⊤ᵖ) a k

μᵖ : ∀{A} → Fun A A Wellfounded → Predᵒ A
μᵖ F = record { # = μₚ (fun F)
              ; down = dc-μ _ (good F) (congr F)
              ; tz = λ v → tz (fun F (id ⊤ᵖ)) v
              }

  where
  dc-iter : ∀(i : ℕ){A}
     → (F : Predᵒ A → Predᵒ A)
     → downClosedᵖ (#(iter i F ⊤ᵖ))
  dc-iter zero F = λ n x _ k _ → tt
  dc-iter (suc i) F = down (F (iter i F ⊤ᵖ))

  dc-μ : ∀{A}
       (F : Predᵒ A → Predᵒ A)
     → wellfounded F
     → congᵖ F
     → downClosedᵖ (μₚ F) 
  dc-μ {A} F wfF congF v k μFvk j j≤k = T
     where
     X : #(iter (suc k) F ⊤ᵖ) v k
     X = μFvk
     Y : #(iter (suc k) F ⊤ᵖ) v j
     Y = dc-iter (suc k) F v k X j j≤k
     Z : #(↓ᵖ (suc j) (iter (suc k) F ⊤ᵖ)) v j
     Z = {!!} -- n≤1+n j , Y
     W : #(↓ᵖ (suc j) (iter (suc j) F ⊤ᵖ)) v j
     W = let eq = lemma15b{A} ⊤ᵖ {suc j}{suc k} F wfF congF (s≤s j≤k)
         in proj₁ ((≡ₚ-sym eq) v j) Z
     T : #((iter (suc j) F ⊤ᵖ)) v j
     T = {!!} -- proj₂ W

{-
  Fixpoint Theorem
-}


lemma18a : ∀{A}
   → (k : ℕ)
   → (F : Fun A A Wellfounded)
   → #(↓ᵖ k (μᵖ F)) ≡ₚ #(↓ᵖ k (iter k (fun F) ⊤ᵖ))
lemma18a zero F x i = {!!}
    -- (λ { (z≤n , b) → z≤n , tt})
    -- ,
    -- λ { (z≤n , b) → z≤n , tz (fun F ⊤ᵖ) x}
lemma18a (suc k′) F v j = {!!}
    -- let k = suc k′ in
    -- #(↓ᵖ k (μᵖ F)) v j                                                ⇔⟨ EQ1 ⟩
    -- (j ≤ k  ×  (#(μᵖ F) v j))                                         ⇔⟨ EQ2 ⟩
    -- (j ≤ k  ×  #(iter (suc j) (fun F) ⊤ᵖ) v j)                        ⇔⟨ EQ3 ⟩
    -- (j ≤ k  ×  #(↓ᵖ (suc j) (iter (suc j) (fun F) ⊤ᵖ)) v j)           ⇔⟨ EQ4 ⟩
    -- (j ≤ k  ×  #(↓ᵖ (suc j) (iter k (fun F) ⊤ᵖ)) v j)                 ⇔⟨ EQ5 ⟩
    -- (j ≤ k  ×  #(iter k (fun F) ⊤ᵖ) v j)                              ⇔⟨ ? ⟩
    -- #(↓ᵖ k (iter k (fun F) ⊤ᵖ)) v j
    -- QED
      
{-
      #(↓ᵖ k (μᵖ F)) v j                                ⇔⟨ EQ1 ⟩ 
      (j ≤ k  ×  (#(μᵖ F) v j))                           ⇔⟨ EQ2 ⟩ 
      (j ≤ k  ×  #(iter (suc j) (fun F) ⊤ᵖ) v j)              ⇔⟨ EQ3 ⟩ 
      (j ≤ k  ×  #(↓ᵖ (suc j) (iter (suc j) (fun F) ⊤ᵖ)) v j) ⇔⟨ EQ4 ⟩
      (j ≤ k  ×  #(↓ᵖ (suc j) (iter k (fun F) ⊤ᵖ)) v j)       ⇔⟨ EQ5 ⟩
      (j ≤ k  ×  #(iter k (fun F) ⊤ᵖ) v j)                    ⇔⟨ EQ6 ⟩ 
      #(↓ᵖ k (iter k (fun F) ⊤ᵖ)) v j
    QED
-}    
    -- where
    --   EQ1 = {!!} -- (λ {(a , b) → a , b}) , (λ {(a , b) → a , b})
    --   EQ2 = (λ {(a , b) → a , b}) , (λ {(a , b) → a , b})
    --   EQ3 = (λ {(a , b) → a , ((n≤1+n j) , b)})
    --       , (λ {(a , (b , c)) → a , c})
    --   EQ4 = (λ{(a , b) → a ,
    --           let xx = (lemma15b ⊤ᵖ {j = suc j}{k = suc k′} (fun F) (good F) (congr F) {!!} v j) in
    --           proj₁ xx b -- proj₁ (lemma15b {j = suc j}{k = suc k′} F ? ? a v j) b
    --           })
    --       , (λ{(a , b) → a ,
    --           {!!} -- proj₂ (lemma15b {j = suc j}{k = suc k′} F ? ? a v j) b
    --           })
    --   EQ5 = (λ {(a , b) → a , {!!}}) , λ {(a , b) → a , {!!}}
    --   EQ6 = (λ {(a , b) → a , b}) , λ z → z
