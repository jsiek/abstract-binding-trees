{-# OPTIONS --without-K --rewriting #-}

{-
 Based on the development of Logical step-indexed logical relation
 by Philip Wadler (June 1, 2022)

 Also based on "An Indexed Model of Recursive Types"
 by Appel and McAllester.
-}
module rewriting.examples.Experiment1 where

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

{-
   Step Indexed Propositions and Predicates
   Continuous and Wellfounded Functions on Step Indexed Predicates
 -}

Setₒ : Set₁
Setₒ = ℕ → Set

Predₒ : Set → Set₁
Predₒ A = A → ℕ → Set

{- Step Indexed Propositions and Predicates
   packaged with down-closed and true-at-zero.
 -}

downClosed : Setₒ → Set
downClosed P = ∀ n → P n → ∀ k → k ≤ n → P k

downClosedᵖ : ∀{A : Set} → (A → ℕ → Set) → Set
downClosedᵖ P = ∀ v → downClosed (P v)

{- Making these abstract helps Agda's inference of implicits -Jeremy -}
abstract 
  record Setᵒ : Set₁ where
    field
      # : Setₒ
      down : downClosed #
      tz : # 0
  open Setᵒ

  {- workaround for "Cannot resolve overloaded projection" -}
  setof : Setᵒ → (ℕ → Set)
  setof S = # S

  record Predᵒ (A : Set) : Set₁ where
    field
      # : A → ℕ → Set -- or A → Setᵒ?
      down  : downClosedᵖ #
      tz : ∀ v → # v 0
  open Predᵒ

  {- workaround for "Cannot resolve overloaded projection" -}
  pred : ∀{A} → Predᵒ A → (A → ℕ → Set)
  pred P = # P

  {- workaround for "Cannot resolve overloaded projection" -}
  downᵖ : ∀{A} → (P : Predᵒ A) → (downClosedᵖ (pred P))
  downᵖ P = down P

  apply : ∀{A} → Predᵒ A → A → Setᵒ
  apply P v = record { # = λ j → # P v j
                     ; down = down P v
                     ; tz = tz P v
                     }
                   
{-----  Equality on Step Indexed Sets  ---------}

abstract
  infix 4 _≡ᵒ_
  _≡ᵒ_ : Setᵒ → Setᵒ → Set
  S ≡ᵒ T = ∀ i → # S i ⇔ # T i

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

infixr 2 _≡ᵒ⟨_⟩_
infix  3 _QEDᵒ
  
_≡ᵒ⟨_⟩_ : 
    (P : Setᵒ)
   {Q : Setᵒ}
  → P ≡ᵒ Q
  → {R : Setᵒ}
  → Q ≡ᵒ R
  → P ≡ᵒ R
P ≡ᵒ⟨ P≡Q ⟩ Q≡R = ≡ᵒ-trans P≡Q Q≡R

_QEDᵒ :
    (P : Setᵒ)
  → P ≡ᵒ P
P QEDᵒ = ≡ᵒ-refl refl

exampleᵒ : ∀{P Q} → P ≡ᵒ Q → Q ≡ᵒ P
exampleᵒ {P}{Q} P=Q =
  Q     ≡ᵒ⟨ ≡ᵒ-sym P=Q ⟩
  P
  QEDᵒ

{-----  Equality on Step Indexed Predicates  ---------}

abstract
  infix 2 _≡ᵖ_
  _≡ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Set
  P ≡ᵖ Q = ∀ v → apply P v ≡ᵒ apply Q v

  ≡ᵖ-refl : ∀{A}{P Q : Predᵒ A}
    → P ≡ Q
    → P ≡ᵖ Q
  ≡ᵖ-refl{A}{P}{Q} refl x = ≡ᵒ-refl{apply P x}{apply Q x} refl

  ≡ᵖ-sym : ∀{A}{P Q : Predᵒ A}
    → P ≡ᵖ Q
    → Q ≡ᵖ P
  ≡ᵖ-sym{A}{P}{Q} PQ x = ≡ᵒ-sym{apply P x}{apply Q x} (PQ x)

  ≡ᵖ-trans : ∀{A : Set}{P Q R : Predᵒ A}
    → P ≡ᵖ Q
    → Q ≡ᵖ R
    → P ≡ᵖ R
  ≡ᵖ-trans{A}{P}{Q}{R} PQ QR x =
      ≡ᵒ-trans{apply P x}{apply Q x}{apply R x} (PQ x) (QR x)

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

exampleᵖ : ∀{A}{P Q : Predᵒ A} → P ≡ᵖ Q → Q ≡ᵖ P
exampleᵖ {A}{P}{Q} P=Q =
  Q     ≡ᵖ⟨ ≡ᵖ-sym P=Q ⟩
  P
  QEDᵖ

{------------ Continuous and Wellfounded Functions on Step Indexed Predicates -}

abstract
  ↓ₒ : ℕ → Setᵒ → Setₒ
  ↓ₒ k S zero = ⊤
  ↓ₒ k S (suc j) = suc j < k × (# S (suc j))

  ↓ₒ-intro : ∀{i}{k}
       (S : Setᵒ)
     → i < k
     → (setof S i)
     → ↓ₒ k S i
  ↓ₒ-intro {zero} {k} S i<k Si = tt
  ↓ₒ-intro {suc i} {k} S i<k Si = i<k , Si

  ↓ᵒ : ℕ → Setᵒ → Setᵒ
  ↓ᵒ k S = record { # = ↓ₒ k S 
                  ; down = λ { zero x .zero z≤n → tt
                             ; (suc n) (sn<k , Sn) zero j≤n → tt
                             ; (suc n) (sn<k , Ssn) (suc j) (s≤s j≤n) →
                             (≤-trans (s≤s (s≤s j≤n)) sn<k)
                             , (down S (suc n) Ssn (suc j) (s≤s j≤n))}
                  ; tz = tt
                  }

  ↓ᵖ : ℕ → ∀{A} → Predᵒ A → Predᵒ A
  ↓ᵖ k P = record { # = λ v → # (↓ᵒ k (apply P v))
                  ; down = λ v → down (↓ᵒ k (apply P v))
                  ; tz = λ v → tt
                  }

congᵖ : ∀{A}{B} (F : Predᵒ A → Predᵒ B) → Set₁
congᵖ F = ∀ {P Q} → P ≡ᵖ Q → (F P) ≡ᵖ (F Q)

abstract
  cong-↓ : ∀{A}{k : ℕ}
    → congᵖ{A}{A} (↓ᵖ k)
  cong-↓ {k}{P}{Q} PQ x zero = (λ x → tt) , (λ x → tt)
  cong-↓ {k}{P}{Q} PQ x (suc i) =
       (λ { (si<k , Pxsi) → si<k , let P→Q = proj₁ (PQ x (suc i)) in P→Q Pxsi})
     , (λ {(si<k , Qxsi) → si<k , let Q→P = proj₂ (PQ x (suc i)) in Q→P Qxsi})
                
continuous : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
continuous F = ∀ P k → ↓ᵖ k (F P) ≡ᵖ ↓ᵖ k (F (↓ᵖ k P))

wellfounded : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
wellfounded F = ∀ {P k} → ↓ᵖ (suc k) (F P) ≡ᵖ ↓ᵖ (suc k) (F (↓ᵖ k P))

data Kind : Set where
  Continuous : Kind
  Wellfounded : Kind

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

{-- Step Index Propositions --}

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

∀ₒ-syntax = ∀ₒ
infix 1 ∀ₒ-syntax
syntax ∀ₒ-syntax (λ x → P) = ∀ₒ[ x ] P

infixr 8 _ₒ
_ₒ  : Set → Setₒ
(p ₒ) zero = ⊤
(p ₒ) (suc n) = p

▷ₒ_ : Setₒ → Setₒ
(▷ₒ P) zero =  ⊤
(▷ₒ P) (suc n) = P n

◁ₒ_ : Setₒ → Setₒ
(◁ₒ S) zero = ⊤
(◁ₒ S) (suc n) = S (suc (suc n))

{-- Step Index Predicates --}

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
∀ₚ {A} F x = ∀ₒ[ v ] F v x

∀ₚ-syntax = ∀ₚ
infix 1 ∀ₚ-syntax
syntax ∀ₚ-syntax (λ x → P) = ∀ₚ[ x ] P

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

{- Packaged Step Indexed Propositions -}

abstract
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

  ∀ᵒ : ∀{A : Set} → (A → Setᵒ) → Setᵒ
  ∀ᵒ{A} P = record { # = λ k → ∀ (a : A) → # (P a) k
                   ; down = λ n ∀Pn k k≤n a → down (P a) n (∀Pn a) k k≤n
                   ; tz = λ a → tz (P a) }

∀ᵒ-syntax = ∀ᵒ
infix 1 ∀ᵒ-syntax
syntax ∀ᵒ-syntax (λ x → P) = ∀ᵒ[ x ] P

abstract
  ∀ᵒₚ : ∀{A} → Predᵒ A → Setᵒ
  ∀ᵒₚ{A} P = record { # = λ k → ∀ a → # P a k
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
                ; down = λ { zero ▷Pn .zero z≤n → tt
                           ; (suc n) ▷Pn .zero z≤n → tt
                           ; (suc n) ▷Pn (suc k) (s≤s k≤n) → down P n ▷Pn k k≤n}
                ; tz = tt
                }

  infixr 8 ◁ᵒ_
  ◁ᵒ_ : Setᵒ → Setᵒ
  ◁ᵒ P = record { # = ◁ₒ # P
                ; down = λ { zero ◁Pk .zero z≤n → tt
                           ; (suc k) ◁Pk zero j≤k → tt
                           ; (suc k) ◁Pk (suc j) j≤k →
                              down P (suc (suc k)) ◁Pk (suc (suc j)) (s≤s j≤k)}
                ; tz = tt }

{- Packaged Step Indexed Predicates -}

abstract
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

  flipᵖ : ∀{A}{B}
     → (A → Predᵒ B)
       -------------
     → (B → Predᵒ A)
  flipᵖ F b = record { # = λ a → # (F a) b
                   ; down = λ a → down (F a) b
                   ; tz = λ a → tz (F a) b }   

  ∀ᵖ : ∀{A : Set}{B} → (A → Predᵒ B) → Predᵒ B
  ∀ᵖ {A}{B} F = let ∀P = λ b → ∀ᵒₚ {A} (flipᵖ F b) in
                record { # = λ b → # (∀P b)
                       ; down = λ b → down (∀P b)
                       ; tz = λ b → tz (∀P b)
                       }

∀ᵖ-syntax = ∀ᵖ
infix 1 ∀ᵖ-syntax
syntax ∀ᵖ-syntax (λ x → P) = ∀ᵖ[ x ] P

abstract
  infixr 8 _ᵖ
  _ᵖ  : Set → ∀{A} → Predᵒ A
  (S ᵖ) {A} = let Sᵖ = λ a → (S ᵒ) in
              record { # = λ a → # (Sᵖ a)
                     ; down = λ a → down (Sᵖ a)
                     ; tz = λ a → tz (Sᵖ a) }

  infixr 8 _ˢ
  _ˢ  : Setᵒ → ∀{A} → Predᵒ A
  (S ˢ) {A} = let Sˢ = λ a → S in
              record { # = λ a → # (Sˢ a)
                     ; down = λ a → down (Sˢ a)
                     ; tz = λ a → tz (Sˢ a)
                     }

  ▷ᵖ : ∀{A} → Predᵒ A → Predᵒ A
  ▷ᵖ P = let ▷P = λ v → ▷ᵒ (apply P v) in
         record { # = λ v → # (▷P v)
                ; down = λ v → down (▷P v)
                ; tz = λ v → tz (▷P v) }

abstract 
  ↓ᵖ-zero : ∀{A}{P Q : Predᵒ A} → ↓ᵖ zero P ≡ᵖ ↓ᵖ zero Q
  ↓ᵖ-zero v zero = (λ x → tt) , (λ x → tt)
  ↓ᵖ-zero v (suc i) = (λ{()}) , (λ{()})

lemma15a : ∀{A} {P Q : Predᵒ A}{j}
  → (F : Fun A A Wellfounded)
  → ↓ᵖ j (iter j (fun F) P) ≡ᵖ ↓ᵖ j (iter j (fun F) Q)
lemma15a {A} {P}{Q} {zero} F = ↓ᵖ-zero
lemma15a {A} {P}{Q} {suc j} F =
    let f = fun F in
    ↓ᵖ (suc j) (f (iter j f P))                                    ≡ᵖ⟨ good F ⟩ 
    ↓ᵖ (suc j) (f (↓ᵖ j (iter j f P)))      ≡ᵖ⟨ cong-↓ (congr F (lemma15a F)) ⟩
    ↓ᵖ (suc j) (f (↓ᵖ j (iter j f Q)))                    ≡ᵖ⟨ ≡ᵖ-sym (good F) ⟩
    ↓ᵖ (suc j) (f (iter j f Q))
  QEDᵖ

lemma15b : ∀{A}(P : Predᵒ A){j k}
  → (F : Fun A A Wellfounded)
  → j ≤ k
  → ↓ᵖ j (iter j (fun F) P) ≡ᵖ ↓ᵖ j (iter k (fun F) P)
lemma15b{A} P {j}{k} F j≤k =
  let f = fun F in
  ↓ᵖ j (iter j f P)                                           ≡ᵖ⟨ lemma15a F ⟩
  ↓ᵖ j (iter j f (iter (k ∸ j) f P))
                              ≡ᵖ⟨ cong-↓ (≡ᵖ-refl (iter-subtract f j k j≤k)) ⟩
  ↓ᵖ j (iter k f P)
  QEDᵖ

dc-iter : ∀(i : ℕ){A}
   → (F : Predᵒ A → Predᵒ A)
   → downClosedᵖ (pred (iter i F ⊤ᵖ))
dc-iter zero F = downᵖ ⊤ᵖ
dc-iter (suc i) F = downᵖ (F (iter i F ⊤ᵖ))

abstract
  μₚ : ∀{A} → (Predᵒ A → Predᵒ A) → Predₒ A
  μₚ F a k = #(iter (suc k) F ⊤ᵖ) a k

  μᵖ : ∀{A}
     → Fun A A Wellfounded
       -------------------
     → Predᵒ A
  μᵖ F = record { # = μₚ (fun F)
                ; down = dc-μ F
                ; tz = λ v → tz (fun F (id ⊤ᵖ)) v
                }
    where

    dc-μ : ∀{A}
         (F : Fun A A Wellfounded)
       → downClosedᵖ (μₚ (fun F)) 
    dc-μ {A} F v k μFvk zero j≤k = tz (fun F ⊤ᵖ) v
    dc-μ {A} F v (suc k′) μFvk (suc j′) (s≤s j′≤k) = T
      where
      j : ℕ
      j = suc j′
      k : ℕ
      k = suc k′
      j≤k : j ≤ k
      j≤k = s≤s j′≤k
      Y : pred (iter (suc k) (fun F) ⊤ᵖ) v j
      Y = dc-iter (suc k) (fun F) v k μFvk j j≤k
      Z : pred (↓ᵖ (suc j) (iter (suc k) (fun F) ⊤ᵖ)) v j
      Z = ↓ₒ-intro (apply (iter (suc k) (fun F) ⊤ᵖ) v) ≤-refl Y
      W : pred (↓ᵖ (suc j) (iter (suc j) (fun F) ⊤ᵖ)) v j
      W = let eq = lemma15b{A} ⊤ᵖ {suc j}{suc k} F (s≤s j≤k)
          in proj₁ ((≡ᵖ-sym{A}{↓ᵖ (suc j) (fun F (fun F (iter j′ (fun F) ⊤ᵖ)))}{↓ᵖ (suc j) (fun F (fun F (iter k′ (fun F) ⊤ᵖ)))} eq)
                      v j) Z
      T : pred((iter (suc j) (fun F) ⊤ᵖ)) v j
      T = proj₂ W
      
{------------ Auxiliary Lemmas ----------}

abstract
  cong-→ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
     → P ≡ᵖ P′
     → Q ≡ᵖ Q′
     → (P →ᵖ Q)  ≡ᵖ  (P′ →ᵖ Q′)
  cong-→ᵖ PP′ QQ′ v k = (λ P→Q j j<k P′vj → let Pvj = proj₂ (PP′ v j) P′vj in
                                            let Qvj = P→Q j j<k Pvj in
                                            let Q′vj = proj₁ (QQ′ v j) Qvj in
                                            Q′vj)
                     , (λ P′→Q′ j j<k Pvj → let P′vj = proj₁ (PP′ v j) Pvj in
                                            let Q′vj = P′→Q′ j j<k P′vj in
                                            let Qvj = proj₂ (QQ′ v j) Q′vj in
                                            Qvj)

  cong-×ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
     → P ≡ᵖ P′
     → Q ≡ᵖ Q′
     → P ×ᵖ Q  ≡ᵖ  P′ ×ᵖ Q′
  cong-×ᵖ {A}{P}{P′}{Q}{Q′} PP′ QQ′ v k = to , fro
    where
    to : pred (P ×ᵖ Q) v k → pred (P′ ×ᵖ Q′) v k
    to (Pvk , Qvk) = (proj₁ (PP′ v k) Pvk) , (proj₁ (QQ′ v k) Qvk)
    fro  : pred (P′ ×ᵖ Q′) v k → pred (P ×ᵖ Q) v k
    fro (P′vk , Q′vk) = (proj₂ (PP′ v k) P′vk) , (proj₂ (QQ′ v k) Q′vk)

  cong-⊎ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
     → P ≡ᵖ P′
     → Q ≡ᵖ Q′
     → P ⊎ᵖ Q  ≡ᵖ  P′ ⊎ᵖ Q′
  cong-⊎ᵖ {A}{P}{P′}{Q}{Q′} PP′ QQ′ v k = to , fro
    where
    to : pred (P ⊎ᵖ Q) v k → pred (P′ ⊎ᵖ Q′) v k
    to (inj₁ Pvk) = inj₁ (proj₁ (PP′ v k) Pvk)
    to (inj₂ Qvk) = inj₂ (proj₁ (QQ′ v k) Qvk)
    fro : pred (P′ ⊎ᵖ Q′) v k → pred (P ⊎ᵖ Q) v k
    fro (inj₁ P′vk) = inj₁ (proj₂ (PP′ v k) P′vk)
    fro (inj₂ Q′vk) = inj₂ (proj₂ (QQ′ v k) Q′vk)

  cong-▷ᵖ : ∀{A}{P P′ : Predᵒ A}
     → P ≡ᵖ P′
     → ▷ᵖ P ≡ᵖ ▷ᵖ P′
  cong-▷ᵖ PP′ v zero = (λ x → tt) , (λ x → tt)
  cong-▷ᵖ PP′ v (suc k) = (λ {x → proj₁ (PP′ v k) x}) , proj₂ (PP′ v k)

{- ↓ᵖ is idempotent -}
abstract
  lemma17 : ∀{A}{P : Predᵒ A}{k}
     → ↓ᵖ k (↓ᵖ (suc k) P) ≡ᵖ ↓ᵖ k P
  lemma17 {A} x zero = (λ x → tt) , (λ x → tt)
  lemma17 {A} x (suc i) =
    (λ { (fst , fst₁ , snd) → fst , snd})
    ,
    (λ { (fst , snd) → fst , (s≤s (<⇒≤ fst)) , snd})

  ↓-zero : ∀{A}{P Q : Predᵒ A}
     → ↓ᵖ 0 P ≡ᵖ ↓ᵖ 0 Q
  ↓-zero v zero = (λ x → tt) , (λ x → tt)
  ↓-zero v (suc i) = (λ { (() , _)}) , λ {(() , _)}

wellfounded⇒continuous : ∀{A}{B}
   → (F : Fun A B Wellfounded)
   → continuous (fun F)
wellfounded⇒continuous F P zero = ↓-zero 
wellfounded⇒continuous F P (suc k) =
    let f = fun F in
    ↓ᵖ (suc k) (f P)                      ≡ᵖ⟨ good F ⟩
    ↓ᵖ (suc k) (f (↓ᵖ k P))              ≡ᵖ⟨ cong-↓ (congr F (≡ᵖ-sym lemma17)) ⟩
    ↓ᵖ (suc k) (f (↓ᵖ k (↓ᵖ (suc k) P)))  ≡ᵖ⟨ ≡ᵖ-sym (good F) ⟩
    ↓ᵖ (suc k) (f (↓ᵖ (suc k) P))
    QEDᵖ

choose : Kind → Kind → Kind
choose Continuous Continuous = Continuous
choose Continuous Wellfounded = Continuous
choose Wellfounded Continuous = Continuous
choose Wellfounded Wellfounded = Wellfounded


