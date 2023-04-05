{-# OPTIONS --without-K --rewriting #-}

{-

 Based on "Logical Step-Indexed Logical Relations"
 by Dreyer, Ahmed, and Birkedal.

 Based on the Agda development of Logical Step-Indexed Logical Relations
 by Philip Wadler (June 1, 2022)

 The proof of the fixpoint theorem is based on "An Indexed Model of
 Recursive Types" by Appel and McAllester.

-}
module rewriting.examples.StepIndexedLogic where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤)
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

{- Step Indexed Propositions and Predicates
   packaged with down-closed and true-at-zero.
 -}

downClosed : (ℕ → Set) → Set
downClosed S = ∀ n → S n → ∀ k → k ≤ n → S k

downClosedᵖ : ∀{A : Set} → (A → ℕ → Set) → Set
downClosedᵖ P = ∀ v → downClosed (P v)

record Setᵒ : Set₁ where
  field
    # : ℕ → Set
    down : downClosed #
    tz : # 0                -- tz short for true at zero
open Setᵒ public

Predᵒ : Set → Set₁
Predᵒ A = A → Setᵒ

{-----  Equality on Step Indexed Sets  ---------}

{- Making these abstract helps Agda's inference of implicits -Jeremy -}
abstract
  infix 2 _≡ᵒ_
  _≡ᵒ_ : Setᵒ → Setᵒ → Set
  S ≡ᵒ T = ∀ i → # S i ⇔ # T i

  ≡ᵒ-intro : ∀{P Q : Setᵒ}
    → (∀ k → # P k → # Q k)
    → (∀ k → # Q k → # P k)
      ---------------------
    → P ≡ᵒ Q
  ≡ᵒ-intro P→Q Q→P k = ⇔-intro (P→Q k) (Q→P k)

  ≡ᵒ-to : ∀{P Q : Setᵒ}
    → P ≡ᵒ Q
    → (∀ k → # P k → # Q k)
  ≡ᵒ-to PQ k = ⇔-to (PQ k) 

  ≡ᵒ-fro : ∀{P Q : Setᵒ}
    → P ≡ᵒ Q
    → (∀ k → # Q k → # P k)
  ≡ᵒ-fro PQ k = ⇔-fro (PQ k)
  
  ≡ᵒ-refl : ∀{S T : Setᵒ}
    → S ≡ T
    → S ≡ᵒ T
  ≡ᵒ-refl refl i = ⇔-refl refl

  ≡ᵒ-sym : ∀{S T : Setᵒ}
    → S ≡ᵒ T
    → T ≡ᵒ S
  ≡ᵒ-sym ST i = ⇔-sym (ST i)

  ≡ᵒ-trans : ∀{S T R : Setᵒ}
    → S ≡ᵒ T
    → T ≡ᵒ R
    → S ≡ᵒ R
  ≡ᵒ-trans ST TR i = ⇔-trans (ST i) (TR i)

{-
  Phil:
    create a module for equational reasoning and
    then instantiate for iff and for the step-indexed sets.
-}

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
  P ≡ᵖ Q = ∀ v → P v ≡ᵒ Q v

  apply-≡ᵖ : ∀{A}{P Q : Predᵒ A}
     → P ≡ᵖ Q
     → (a : A)
     → P a ≡ᵒ Q a
  apply-≡ᵖ P=Q a = P=Q a

  ≡ᵖ-refl : ∀{A}{P Q : Predᵒ A}
    → P ≡ Q
    → P ≡ᵖ Q
  ≡ᵖ-refl{A}{P}{Q} refl x = ≡ᵒ-refl{P x}{Q x} refl

  ≡ᵖ-sym : ∀{A}{P Q : Predᵒ A}
    → P ≡ᵖ Q
    → Q ≡ᵖ P
  ≡ᵖ-sym{A}{P}{Q} PQ x = ≡ᵒ-sym{P x}{Q x} (PQ x)

  ≡ᵖ-trans : ∀{A : Set}{P Q R : Predᵒ A}
    → P ≡ᵖ Q
    → Q ≡ᵖ R
    → P ≡ᵖ R
  ≡ᵖ-trans{A}{P}{Q}{R} PQ QR x =
      ≡ᵒ-trans{P x}{Q x}{R x} (PQ x) (QR x)

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

{-
  The following is the same as the approx function in Appel and McAllester
  except for the case at 0.
  Here is their version:
  ↓ₒ k S j = j < k × (# S j)
-}
↓ₒ : ℕ → Setᵒ → (ℕ → Set)
↓ₒ k S zero = ⊤
↓ₒ k S (suc j) = suc j < k × (# S (suc j))

{-
Alternative that's simpler and true at zero,
but Jeremy had trouble with it later in the proofs.

↓′ₒ : ℕ → Setᵒ → Setₒ
↓′ₒ k S j = j ≤ k × # S j

The two definitions are related as follows:

↓′ₒ (suc k) S = ↓ₒ k S

so it should be possible to adapt to using ↓′ₒ.

-}

{-
Phil: idea, create a closure operator that
turns any Setₒ into Setᵒ.

close : Setₒ → Setᵒ
close S = record { # = λ k → ∀ j → j < k → S j
                 ; down = λ n ∀jSj k k≤n j j<k → ∀jSj j (≤-trans j<k k≤n)
                 ; tz = λ j () }

↓′ᵒ : ℕ → Setᵒ → Setᵒ
↓′ᵒ k S = close λ j → j < k × # S j
-}

↓ₒ-intro : ∀{i}{k}
     (S : Setᵒ)
   → i < k
   → (# S i)
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

{-
{- update stdlib to get this -}
n≮0 : ∀ {n} → (n < 0) → ⊥
n≮0 ()

equiv : ∀ k S → ↓′ᵒ k S ≡ᵒ ↓ᵒ k S
equiv zero S = ≡ᵒ-intro (λ { zero ↓0Sk → tt ;
                             (suc k) ↓0Sk → let x , y = ↓0Sk k ≤-refl in ⊥-elim (n≮0 {k} x)})
                        λ { zero ↓0Sk j () ;
                            (suc k) (() , _) j j<k}
equiv (suc k) S = ≡ᵒ-intro (λ { zero ↓′skSj → tt
                              ; (suc j) ↓′skSj →
                                let x , y = ↓′skSj j {!!} in
                                {!!} , {!!}})
                           {!!}
-}

↓ᵖ : ℕ → ∀{A} → Predᵒ A → Predᵒ A
↓ᵖ k P = λ a → ↓ᵒ k (P a)

congᵖ : ∀{A}{B} (F : Predᵒ A → Predᵒ B) → Set₁
congᵖ F = ∀ {P Q} → P ≡ᵖ Q → (F P) ≡ᵖ (F Q)

abstract
  cong-↓ : ∀{A}{k : ℕ}
    → congᵖ{A}{A} (↓ᵖ k)
  cong-↓ {k}{P}{Q} PQ x zero = ⇔-intro (λ x → tt) (λ x → tt)
  cong-↓ {k}{P}{Q} PQ x (suc i) =
      ⇔-intro
       (λ { (si<k , Pxsi) → si<k , let P→Q = ⇔-to (PQ x (suc i)) in P→Q Pxsi})
       (λ {(si<k , Qxsi) → si<k , let Q→P = ⇔-fro (PQ x (suc i)) in Q→P Qxsi})
                
continuous : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
continuous F = ∀ {P k} → ↓ᵖ k (F P) ≡ᵖ ↓ᵖ k (F (↓ᵖ k P))

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

{- Step Indexed Propositions -}

⊥ᵒ : Setᵒ
⊥ᵒ = record { # = λ { zero → ⊤ ; (suc k) → ⊥ }
            ; down = λ { zero ⊥n .zero z≤n → tt}
            ; tz = tt
            }

⊤ᵒ : Setᵒ
⊤ᵒ = record { # = λ k → ⊤
            ; down = λ n _ k _ → tt
            ; tz = tt
            }
              
infixr 7 _×ᵒ_
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ×ᵒ Q = record { # = λ k → # P k × # Q k
                ; down = λ k (Pk , Qk) j j≤k →
                          (down P k Pk j j≤k) , (down Q k Qk j j≤k)
                ; tz = (tz P) , (tz Q)
                }
                
infixr 7 _⊎ᵒ_
_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ⊎ᵒ Q = record { # = λ k → # P k ⊎ # Q k
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

∀ᵒ : ∀{A : Set} → (Predᵒ A) → Setᵒ
∀ᵒ{A} P = record { # = λ k → ∀ (a : A) → # (P a) k
                 ; down = λ n ∀Pn k k≤n a → down (P a) n (∀Pn a) k k≤n
                 ; tz = λ a → tz (P a) }

∀ᵒ-syntax = ∀ᵒ
infix 1 ∀ᵒ-syntax
syntax ∀ᵒ-syntax (λ x → P) = ∀ᵒ[ x ] P

infixr 8 _ᵒ
_ᵒ  : Set → Setᵒ
S ᵒ = record { # = λ { zero → ⊤ ; (suc k) → S }
             ; down = λ { k Sk zero j≤k → tt
                        ; (suc k) Sk (suc j) j≤k → Sk}
             ; tz = tt
             }

infixr 8 ▷ᵒ_
▷ᵒ_ : Setᵒ → Setᵒ
▷ᵒ P = record { # = λ { zero → ⊤ ; (suc k) → # P k }
              ; down = λ { zero ▷Pn .zero z≤n → tt
                         ; (suc n) ▷Pn .zero z≤n → tt
                         ; (suc n) ▷Pn (suc k) (s≤s k≤n) → down P n ▷Pn k k≤n}
              ; tz = tt
              }

infixr 8 ◁ᵒ_
◁ᵒ_ : Setᵒ → Setᵒ
◁ᵒ P = record { # = λ { zero → ⊤ ; (suc k) → # P (suc (suc k)) }
              ; down = λ { zero ◁Pk .zero z≤n → tt
                         ; (suc k) ◁Pk zero j≤k → tt
                         ; (suc k) ◁Pk (suc j) j≤k →
                            down P (suc (suc k)) ◁Pk (suc (suc j)) (s≤s j≤k)}
              ; tz = tt }

{- Step Indexed Predicates -}

⊤ᵖ : ∀{A} → Predᵒ A
⊤ᵖ {A} = λ a → ⊤ᵒ

⊥ᵖ : ∀{A} → Predᵒ A
⊥ᵖ {A} = λ a → ⊤ᵒ

infixr 7 _×ᵖ_
_×ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
P ×ᵖ Q = λ a → P a ×ᵒ Q a

infixr 7 _⊎ᵖ_
_⊎ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
P ⊎ᵖ Q = λ a → P a ⊎ᵒ Q a

infixr 6 _→ᵖ_
_→ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
P →ᵖ Q = λ a → (P a →ᵒ Q a)

flipᵖ : ∀{A}{B}
   → (A → Predᵒ B)
     -------------
   → (B → Predᵒ A)
flipᵖ F b = λ a → F a b

∀ᵖ : ∀{A : Set}{B} → (A → Predᵒ B) → Predᵒ B
∀ᵖ {A}{B} F = λ b → ∀ᵒ {A} (flipᵖ F b)

∀ᵖ-syntax = ∀ᵖ
infix 1 ∀ᵖ-syntax
syntax ∀ᵖ-syntax (λ x → P) = ∀ᵖ[ x ] P

infixr 8 _ᵖ
_ᵖ  : Set → ∀{A} → Predᵒ A
(S ᵖ) {A} = λ a → (S ᵒ)

infixr 8 _ˢ
_ˢ  : Setᵒ → ∀{A} → Predᵒ A
(S ˢ) {A} = λ a → S

▷ᵖ : ∀{A} → Predᵒ A → Predᵒ A
▷ᵖ P = λ a → ▷ᵒ (P a)

abstract 
  ↓ᵖ-zero : ∀{A}{P Q : Predᵒ A} → ↓ᵖ zero P ≡ᵖ ↓ᵖ zero Q
  ↓ᵖ-zero v zero = ⇔-intro (λ x → tt) (λ x → tt)
  ↓ᵖ-zero v (suc i) = ⇔-intro (λ{()}) (λ{()})

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
   → ∀ v → downClosed (#(iter i F ⊤ᵖ v))
dc-iter zero F = λ v n _ k _ → tt
dc-iter (suc i) F = λ v → down (F (iter i F ⊤ᵖ) v)

μₚ : ∀{A} → (Predᵒ A → Predᵒ A) → (A → ℕ → Set)
μₚ F a k = #(iter (suc k) F ⊤ᵖ a) k

μᵒ : ∀{A}
   → Fun A A Wellfounded
     -------------------
   → Predᵒ A
μᵒ F a =  record { # = μₚ (fun F) a
                 ; down = dc-μ F a
                 ; tz = tz ((fun F (id ⊤ᵖ)) a)
                 }
  where
  dc-μ : ∀{A}
       (F : Fun A A Wellfounded)
     → (a : A)
     → downClosed (μₚ (fun F) a)
  dc-μ {A} F a k μFak zero j≤k = tz (fun F ⊤ᵖ a)
  dc-μ {A} F a (suc k′) μFak (suc j′) (s≤s j′≤k) = T
   where
   Y : # (iter (suc (suc k′)) (fun F) ⊤ᵖ a) (suc j′)
   Y = dc-iter (suc (suc k′)) (fun F) a (suc k′) μFak (suc j′) (s≤s j′≤k)
   Z : # (↓ᵖ (suc (suc j′)) (iter (suc (suc k′)) (fun F) ⊤ᵖ) a) (suc j′)
   Z = ↓ₒ-intro ((iter (suc (suc k′)) (fun F) ⊤ᵖ) a) ≤-refl Y
   W : # (↓ᵖ (suc (suc j′)) (iter (suc (suc j′)) (fun F) ⊤ᵖ) a) (suc j′)
   W = let eq = lemma15b ⊤ᵖ F (s≤s (s≤s j′≤k)) in
       ≡ᵒ-to (apply-≡ᵖ (≡ᵖ-sym eq) a) (suc j′) Z 
   T : #(iter (suc (suc j′)) (fun F) ⊤ᵖ a) (suc j′)
   T = proj₂ W
   
{------------ Auxiliary Lemmas ----------}

abstract
  cong-→ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
     → P ≡ᵖ P′
     → Q ≡ᵖ Q′
     → (P →ᵖ Q)  ≡ᵖ  (P′ →ᵖ Q′)
  cong-→ᵖ PP′ QQ′ v k =
      ⇔-intro (λ P→Q j j<k P′vj → let Pvj = ⇔-fro (PP′ v j) P′vj in
                                  let Qvj = P→Q j j<k Pvj in
                                  let Q′vj = ⇔-to (QQ′ v j) Qvj in
                                  Q′vj)
               (λ P′→Q′ j j<k Pvj → let P′vj = ⇔-to (PP′ v j) Pvj in
                                    let Q′vj = P′→Q′ j j<k P′vj in
                                    let Qvj = ⇔-fro (QQ′ v j) Q′vj in
                                    Qvj)

  cong-×ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
     → P ≡ᵖ P′
     → Q ≡ᵖ Q′
     → P ×ᵖ Q  ≡ᵖ  P′ ×ᵖ Q′
  cong-×ᵖ {A}{P}{P′}{Q}{Q′} PP′ QQ′ v k = ⇔-intro to fro
    where
    to : # ((P ×ᵖ Q) v) k → # ((P′ ×ᵖ Q′) v) k
    to (Pvk , Qvk) = (⇔-to (PP′ v k) Pvk) , (⇔-to (QQ′ v k) Qvk)
    fro  : #((P′ ×ᵖ Q′) v) k → #((P ×ᵖ Q) v) k
    fro (P′vk , Q′vk) = (⇔-fro (PP′ v k) P′vk) , (⇔-fro (QQ′ v k) Q′vk)

  cong-⊎ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
     → P ≡ᵖ P′
     → Q ≡ᵖ Q′
     → P ⊎ᵖ Q  ≡ᵖ  P′ ⊎ᵖ Q′
  cong-⊎ᵖ {A}{P}{P′}{Q}{Q′} PP′ QQ′ v k = ⇔-intro to fro
    where
    to : #((P ⊎ᵖ Q) v) k → #((P′ ⊎ᵖ Q′) v) k
    to (inj₁ Pvk) = inj₁ (⇔-to (PP′ v k) Pvk)
    to (inj₂ Qvk) = inj₂ (⇔-to (QQ′ v k) Qvk)
    fro : #((P′ ⊎ᵖ Q′) v) k → #((P ⊎ᵖ Q) v) k
    fro (inj₁ P′vk) = inj₁ (⇔-fro (PP′ v k) P′vk)
    fro (inj₂ Q′vk) = inj₂ (⇔-fro (QQ′ v k) Q′vk)

  cong-▷ᵖ : ∀{A}{P P′ : Predᵒ A}
     → P ≡ᵖ P′
     → ▷ᵖ P ≡ᵖ ▷ᵖ P′
  cong-▷ᵖ PP′ v zero = ⇔-intro (λ x → tt) (λ x → tt)
  cong-▷ᵖ PP′ v (suc k) = ⇔-intro (λ x → ⇔-to (PP′ v k) x) (⇔-fro (PP′ v k))

{- ↓ᵖ is idempotent -}
abstract
  lemma17 : ∀{A}{P : Predᵒ A}{k}
     → ↓ᵖ k (↓ᵖ (suc k) P) ≡ᵖ ↓ᵖ k P
  lemma17 {A} x zero = ⇔-intro (λ x → tt) (λ x → tt)
  lemma17 {A} x (suc i) =
    ⇔-intro
      (λ { (fst , fst₁ , snd) → fst , snd})
      (λ { (fst , snd) → fst , (s≤s (<⇒≤ fst)) , snd})

  ↓-zero : ∀{A}{P Q : Predᵒ A}
     → ↓ᵖ 0 P ≡ᵖ ↓ᵖ 0 Q
  ↓-zero v zero = ⇔-intro (λ x → tt) (λ x → tt)
  ↓-zero v (suc i) = ⇔-intro (λ { (() , _)}) (λ {(() , _)})

wellfounded⇒continuous : ∀{A}{B}
   → (F : Fun A B Wellfounded)
   → continuous (fun F)
wellfounded⇒continuous F {P}{zero} = ↓-zero 
wellfounded⇒continuous F {P}{suc k} =
    let f = fun F in
    ↓ᵖ (suc k) (f P)                      ≡ᵖ⟨ good F ⟩
    ↓ᵖ (suc k) (f (↓ᵖ k P))              ≡ᵖ⟨ cong-↓ (congr F (≡ᵖ-sym lemma17)) ⟩
    ↓ᵖ (suc k) (f (↓ᵖ k (↓ᵖ (suc k) P)))  ≡ᵖ⟨ ≡ᵖ-sym (good F) ⟩
    ↓ᵖ (suc k) (f (↓ᵖ (suc k) P))
    QEDᵖ

WF⇒C : ∀{A}{B}
   → Fun A B Wellfounded
   → Fun A B Continuous
WF⇒C F = record { fun = fun F
                ; good = wellfounded⇒continuous F
                ; congr = congr F }   

choose : Kind → Kind → Kind
choose Continuous Continuous = Continuous
choose Continuous Wellfounded = Continuous
choose Wellfounded Continuous = Continuous
choose Wellfounded Wellfounded = Wellfounded

{-------------- Functions on Step Index Predicates  --------------}

{------- Implication --------}

abstract
  down-fun : ∀{A} {P Q : Predᵒ A}{k}
     → ↓ᵖ k (P →ᵖ Q) ≡ᵖ ↓ᵖ k ((↓ᵖ k P) →ᵖ (↓ᵖ k Q))
  down-fun x zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-fun {A}{P}{Q}{k} x (suc i) =
     ⇔-intro
     (λ {(si<k , P→Q) →
         si<k , (λ { zero j<si ↓kPxj → tt
                   ; (suc j) j<si (sj<k , Pxsj) →
                   sj<k , let Qsj = P→Q (suc j) j<si Pxsj in Qsj})})
     (λ {(si<k , P→Q) →
         si<k , λ { zero j<si Pxj → tz (Q x)
                  ; (suc j) j<si Pxj →
                     let ↓Qsj = P→Q (suc j) j<si
                                   ((≤-trans (s≤s j<si) si<k) , Pxj) in
                     proj₂ ↓Qsj}})

continuous-→ : ∀{A}{B}(F G : Fun A B Continuous)
   → continuous (λ P → (fun F) P →ᵖ (fun G) P)
continuous-→ {A}{B} F G {P}{k} =
   let f = fun F in let g = fun G in
   ↓ᵖ k (f P →ᵖ g P)                                             ≡ᵖ⟨ down-fun ⟩
   ↓ᵖ k (↓ᵖ k (f P) →ᵖ ↓ᵖ k (g P))   ≡ᵖ⟨ cong-↓ (cong-→ᵖ (good F) (good G)) ⟩
   ↓ᵖ k (↓ᵖ k (f (↓ᵖ k P)) →ᵖ ↓ᵖ k (g (↓ᵖ k P)))          ≡ᵖ⟨ ≡ᵖ-sym down-fun ⟩
   ↓ᵖ k (f (↓ᵖ k P) →ᵖ g (↓ᵖ k P))
   QEDᵖ

wellfounded-→ : ∀{A}{B}(F G : Fun A B Wellfounded)
   → wellfounded (λ P → (fun F) P →ᵖ (fun G) P)
wellfounded-→ {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵖ (suc k) (f P →ᵖ g P)                                      ≡ᵖ⟨ down-fun ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (f P) →ᵖ ↓ᵖ (suc k) (g P))
                                     ≡ᵖ⟨ cong-↓ (cong-→ᵖ (good F) (good G)) ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (f (↓ᵖ k P)) →ᵖ ↓ᵖ (suc k) (g (↓ᵖ k P)))
                                                          ≡ᵖ⟨ ≡ᵖ-sym down-fun ⟩
    ↓ᵖ (suc k) (f (↓ᵖ k P) →ᵖ g (↓ᵖ k P))
    QEDᵖ

goodness-→ : ∀ {kf kg : Kind} {A}{B}
     (F : Fun A B kf)
     (G : Fun A B kg)
   → goodness (choose kf kg) (λ P → (fun F) P →ᵖ (fun G) P)
goodness-→ {Continuous}{Continuous} F G  = continuous-→ F G
goodness-→ {Continuous}{Wellfounded} F G = continuous-→ F (WF⇒C G)
goodness-→ {Wellfounded}{Continuous} F G = continuous-→ (WF⇒C F) G
goodness-→ {Wellfounded}{Wellfounded} F G = wellfounded-→ F G 

abstract
  cong-→ : ∀{A}{B}{kf}{kg}
       (F : Fun A B kf)
       (G : Fun A B kg)
     → congᵖ (λ P → (fun F) P →ᵖ (fun G) P)
  cong-→ F G {P}{Q} PQ b i =
      ⇔-intro
      (λ FP→GP j j≤i FQbj →
         let FP≡FQ = congr F PQ b j in
         let GP≡GQ = congr G PQ b j in
         let GPbj = FP→GP j j≤i (⇔-fro FP≡FQ FQbj) in
         let GQbj = ⇔-to GP≡GQ GPbj in
         GQbj)
    (λ FQ→GQ j j≤i FPbj →
        let FP≡FQ = congr F PQ b j in
        let GP≡GQ = congr G PQ b j in
        let GQbj = FQ→GQ j j≤i (⇔-to FP≡FQ FPbj) in
        let GPbj = ⇔-fro GP≡GQ GQbj in
        GPbj)

infixr 6 _→ᶠ_
_→ᶠ_ : ∀{A B}{kF kG}
   → Fun A B kF
   → Fun A B kG
     ----------------------
   → Fun A B (choose kF kG)
_→ᶠ_ {A}{B}{kF}{kG} F G =
  record { fun = λ P → fun F P →ᵖ fun G P
         ; good = goodness-→ F G
         ; congr = cong-→ F G
         }

{------- Conjunction --------}

abstract
  down-× : ∀{A}{P Q : Predᵒ A}{k}
     → ↓ᵖ k (P ×ᵖ Q) ≡ᵖ ↓ᵖ k ((↓ᵖ k P) ×ᵖ (↓ᵖ k Q))
  down-× x zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-× x (suc i) =
      ⇔-intro
      (λ { (si<k , Pxsi , Qxsi) → si<k , ((si<k , Pxsi) , (si<k , Qxsi))})
      (λ { (si<k , (_ , Pxsi) , _ , Qxsi) → si<k , Pxsi , Qxsi})

continuous-× : ∀{A}{B}
    (F G : Fun A B Continuous)
   → continuous (λ P → (fun F) P ×ᵖ (fun G) P)
continuous-× {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵖ k (f P ×ᵖ g P)                                              ≡ᵖ⟨ down-× ⟩
    ↓ᵖ k (↓ᵖ k (f P) ×ᵖ ↓ᵖ k (g P))    ≡ᵖ⟨ cong-↓ (cong-×ᵖ (good F) (good G)) ⟩
    ↓ᵖ k (↓ᵖ k (f (↓ᵖ k P)) ×ᵖ ↓ᵖ k (g (↓ᵖ k P)))           ≡ᵖ⟨ ≡ᵖ-sym down-× ⟩
    ↓ᵖ k (f (↓ᵖ k P) ×ᵖ g (↓ᵖ k P))
    QEDᵖ

wellfounded-× : ∀{A}{B}
    (F G : Fun A B Wellfounded)
   → wellfounded (λ P → (fun F) P ×ᵖ (fun G) P)
wellfounded-× {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵖ (suc k) (f P ×ᵖ g P)                                       ≡ᵖ⟨ down-× ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (f P) ×ᵖ ↓ᵖ (suc k) (g P))
                                       ≡ᵖ⟨ cong-↓ (cong-×ᵖ (good F) (good G)) ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (f (↓ᵖ k P)) ×ᵖ ↓ᵖ (suc k) (g (↓ᵖ k P)))
                                                            ≡ᵖ⟨ ≡ᵖ-sym down-× ⟩
    ↓ᵖ (suc k) (f (↓ᵖ k P) ×ᵖ g (↓ᵖ k P))
    QEDᵖ

goodness-× : ∀ {kf kg : Kind} {A}{B}
    (F : Fun A B kf)
    (G : Fun A B kg)
   → goodness (choose kf kg) (λ P → (fun F) P ×ᵖ (fun G) P)
goodness-× {Continuous}{Continuous} F G = continuous-× F G 
goodness-× {Continuous}{Wellfounded} F G = continuous-× F (WF⇒C G)
goodness-× {Wellfounded}{Continuous} F G = continuous-× (WF⇒C F) G
goodness-× {Wellfounded}{Wellfounded} F G = wellfounded-× F G 

abstract
  cong-× : ∀{A}{B}{kf}{kg}
       (F : Fun A B kf)
       (G : Fun A B kg)
     → congᵖ (λ P → (fun F) P ×ᵖ (fun G) P)
  cong-× F G {P}{Q} PQ x i =
    ⇔-intro
    (λ {(FPxi , GPxi) →
          let FPxi⇔FQxi = congr F PQ x i in
          let GPxi⇔GQxi = congr G PQ x i in
          ⇔-to FPxi⇔FQxi FPxi , ⇔-to GPxi⇔GQxi GPxi})
    (λ {(FQxi , GQxi) →
          let FPxi⇔FQxi = congr F PQ x i in
          let GPxi⇔GQxi = congr G PQ x i in
          ⇔-fro FPxi⇔FQxi FQxi  , ⇔-fro GPxi⇔GQxi GQxi})

infixr 6 _×ᶠ_
_×ᶠ_ : ∀{A}{B}{kF kG}
   → Fun A B kF
   → Fun A B kG
     ----------------------
   → Fun A B (choose kF kG)
_×ᶠ_ {A}{B}{kF}{kG} F G =
  record { fun = λ P → (fun F) P ×ᵖ (fun G) P
         ; good = goodness-× F G
         ; congr = cong-× F G
         }

{------- Disjunction --------}

abstract
  down-⊎ : ∀{A}{P Q : Predᵒ A}{k}
     → ↓ᵖ k (P ⊎ᵖ Q) ≡ᵖ ↓ᵖ k ((↓ᵖ k P) ⊎ᵖ (↓ᵖ k Q))
  down-⊎ {A}{P}{Q} {k} x i = ⇔-intro (to i) (fro i)
    where
    to : ∀ i →  #(↓ᵖ k (P ⊎ᵖ Q) x) i → #(↓ᵖ k (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q) x) i
    to zero _ = tt
    to (suc i) (si<k , inj₁ Psi) = si<k , (inj₁ (si<k , Psi))
    to (suc i) (si<k , inj₂ Qsi) = si<k , (inj₂ (si<k , Qsi))

    fro : ∀ i → #(↓ᵖ k (↓ᵖ k P ⊎ᵖ ↓ᵖ k Q) x) i → #(↓ᵖ k (P ⊎ᵖ Q) x) i
    fro zero x = tt
    fro (suc i) (si<k , inj₁ (_ , Psi)) = si<k , inj₁ Psi
    fro (suc i) (si<k , inj₂ (_ , Qsi)) = si<k , (inj₂ Qsi)
  
continuous-⊎ : ∀{A}{B}(F G : Fun A B Continuous)
   → continuous (λ P → (fun F) P ⊎ᵖ (fun G) P)
continuous-⊎ {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵖ k (f P ⊎ᵖ g P)                              ≡ᵖ⟨ down-⊎ ⟩
    ↓ᵖ k (↓ᵖ k (f P) ⊎ᵖ ↓ᵖ k (g P))     ≡ᵖ⟨ cong-↓ (cong-⊎ᵖ (good F) (good G)) ⟩
    ↓ᵖ k (↓ᵖ k (f (↓ᵖ k P)) ⊎ᵖ ↓ᵖ k (g (↓ᵖ k P)))           ≡ᵖ⟨ ≡ᵖ-sym down-⊎ ⟩
    ↓ᵖ k (f (↓ᵖ k P) ⊎ᵖ g (↓ᵖ k P))
    QEDᵖ

wellfounded-⊎ : ∀{A}{B}(F G : Fun A B Wellfounded)
   → wellfounded (λ P → (fun F) P ⊎ᵖ (fun G) P)
wellfounded-⊎ {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵖ (suc k) (f P ⊎ᵖ g P)                                       ≡ᵖ⟨ down-⊎ ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (f P) ⊎ᵖ ↓ᵖ (suc k) (g P))
                                        ≡ᵖ⟨ cong-↓ (cong-⊎ᵖ (good F) (good G)) ⟩
    ↓ᵖ (suc k) (↓ᵖ (suc k) (f (↓ᵖ k P)) ⊎ᵖ ↓ᵖ (suc k) (g (↓ᵖ k P)))
                                                             ≡ᵖ⟨ ≡ᵖ-sym down-⊎ ⟩
    ↓ᵖ (suc k) (f (↓ᵖ k P) ⊎ᵖ g (↓ᵖ k P))
    QEDᵖ

goodness-⊎ : ∀ {kf kg : Kind} {A}{B}
     (F : Fun A B kf)
     (G : Fun A B kg)
   → goodness (choose kf kg) (λ P → (fun F) P ⊎ᵖ (fun G) P)
goodness-⊎ {Continuous}{Continuous} F G = continuous-⊎ F G 
goodness-⊎ {Continuous}{Wellfounded} F G = continuous-⊎ F (WF⇒C G)
goodness-⊎ {Wellfounded}{Continuous} F G = continuous-⊎ (WF⇒C F) G
goodness-⊎ {Wellfounded}{Wellfounded} F G = wellfounded-⊎ F G

abstract
  cong-⊎ : ∀{A}{B}{kf}{kg}
       (F : Fun A B kf)
       (G : Fun A B kg)
     → congᵖ (λ P → (fun F) P ⊎ᵖ (fun G) P)
  cong-⊎ {A}{B} F G {P}{Q} PQ x i = ⇔-intro to fro
    where
    to : #(((fun F) P ⊎ᵖ (fun G) P) x) i → #(((fun F) Q ⊎ᵖ (fun G) Q) x) i
    to (inj₁ FPi) = inj₁ (⇔-to (congr F {P}{Q} PQ x i) FPi)
    to (inj₂ GPi) = inj₂ (⇔-to (congr G {P}{Q} PQ x i) GPi)

    fro : #(((fun F) Q ⊎ᵖ (fun G) Q) x) i → #(((fun F) P ⊎ᵖ (fun G) P) x) i
    fro (inj₁ FQi) = inj₁ (⇔-fro (congr F {P}{Q} PQ x i) FQi)
    fro (inj₂ GQi) = inj₂ (⇔-fro (congr G PQ x i) GQi)

infixr 6 _⊎ᶠ_
_⊎ᶠ_ : ∀{A}{B}{kF kG}
   → Fun A B kF
   → Fun A B kG
     ----------------------
   → Fun A B (choose kF kG)
_⊎ᶠ_ {A}{B}{kF}{kG} F G =
  record { fun = λ P → (fun F) P ⊎ᵖ (fun G) P
         ; good = goodness-⊎ F G
         ; congr = cong-⊎ F G
         }

{------- Forall --------}

abstract
  continuous-all : ∀{A B C}
     → (F : A → Fun B C Continuous)
     → continuous (λ P → ∀ᵖ[ a ] fun (F a) P)
  continuous-all F {P}{k} x zero = ⇔-intro (λ x → tt) (λ x → tt)
  continuous-all F {P}{k} x (suc i) =
      ⇔-intro
      (λ {(si<k , ∀FP) → si<k ,
           (λ v →
               let ↓F↓P = ⇔-to (good (F v) x (suc i))
                            (↓ₒ-intro ((fun (F v) P) x) si<k (∀FP v) ) in
               proj₂ ↓F↓P)})
      (λ {(si<k , ∀FP) → si<k ,
         (λ v →
             let ↓FP = ⇔-fro (good (F v) x (suc i))
                  (↓ₒ-intro (((fun (F v) (↓ᵖ k P)) x)) si<k (∀FP v) ) in
             proj₂ ↓FP)})

  wellfounded-all : ∀{A B C}
     → (F : A → Fun B C Wellfounded)
     → wellfounded (λ P → ∀ᵖ (λ a → fun (F a) P))
  wellfounded-all F {P}{k} x zero = ⇔-intro (λ x → tt) (λ x → tt)
  wellfounded-all F {P}{k} x (suc i) =
      ⇔-intro
      (λ{(s≤s i≤k , ∀FP) →
          s≤s i≤k
          , (λ v → let ↓F↓P = ⇔-to (good (F v) x (suc i))
                            (↓ₒ-intro ((fun (F v) P) x)
                               (≤-trans (s≤s i≤k) ≤-refl) (∀FP v))
                   in proj₂ ↓F↓P)})
      (λ {(i≤k , ∀F↓P) →
          i≤k
          , (λ v → let ↓FP = ⇔-fro (good (F v) x (suc i))
                          (↓ₒ-intro ((fun (F v) (↓ᵖ k P)) x) i≤k (∀F↓P v))
                   in proj₂ ↓FP)})

goodness-all : ∀{A B C}{K}
   → (F : A → Fun B C K)
   → goodness K (λ P → ∀ᵖ (λ a → fun (F a) P))
goodness-all {A} {B} {C} {Continuous} F = continuous-all F
goodness-all {A} {B} {C} {Wellfounded} F = wellfounded-all F

abstract
  cong-all : ∀{A B C}{K}
     → (F : A → Fun B C K)
     → congᵖ (λ P → ∀ᵖ (λ a → fun (F a) P))
  cong-all F {P}{Q} PQ c i =
    ⇔-intro
    (λ ∀FP v → ⇔-to (congr (F v) PQ c i) (∀FP v))
    (λ ∀FQ v → ⇔-fro (congr (F v) PQ c i) (∀FQ v))

∀ᶠ : ∀{A B C : Set}{K}
   → (A → Fun B C K)
     ---------------
   → Fun B C K
∀ᶠ {A}{B}{C}{K} F =
  record { fun = λ P → ∀ᵖ[ a ] fun (F a) P
         ; good = goodness-all F
         ; congr = cong-all F
         }
  
∀ᶠ-syntax = ∀ᶠ
infix 1 ∀ᶠ-syntax
syntax ∀ᶠ-syntax (λ x → F) = ∀ᶠ[ x ] F

{------- Constant --------}

abstract
  wellfounded-const : ∀{A}{B} (S : Set) → wellfounded{A}{B} (λ P → S ᵖ)
  wellfounded-const S = λ v i → ⇔-intro (λ x → x) (λ x → x)

  cong-const : ∀{A}{B} (S : Set) → congᵖ{A}{B} (λ P → S ᵖ)
  cong-const S = λ _ v i → ⇔-intro (λ x → x) (λ x → x)

_ᶠ : ∀{A}{B}
   → Set
   → Fun A B Wellfounded
(S)ᶠ = record { fun = λ P → S ᵖ
              ; good = λ {P}{k} → wellfounded-const S {P}{k}
              ; congr = cong-const S
              }

{------- Later --------}

≤-inv : ∀{i}{j}
   → suc i ≤ suc j
   → i ≤ j
≤-inv (s≤s i≤j) = i≤j

abstract
  down-▷ : ∀{B}{k}(P : Predᵒ B) → ↓ᵖ (suc k) (▷ᵖ P) ≡ᵖ ↓ᵖ (suc k) (▷ᵖ (↓ᵖ k P))
  down-▷ P v zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-▷ P v (suc zero) =
      ⇔-intro (λ {(a , b) → a , tt}) (λ {(a , b) → a , (tz (P v))})
  down-▷ P v (suc (suc i)) =
    ⇔-intro
    (λ {(s≤s i≤1+k , ▷Pvi) →
                 s≤s i≤1+k , i≤1+k , ▷Pvi})
    (λ {(i≤1+k , (_ , ▷Pvi)) → i≤1+k , ▷Pvi})

wellfounded-▷ : ∀{A}{B} (F : Fun A B Continuous)
   → wellfounded (λ P → ▷ᵖ ((fun F) P))
wellfounded-▷ {A}{B} F {P}{k} =
    let f = fun F in
    ↓ᵖ (suc k) (▷ᵖ (f P))                ≡ᵖ⟨ down-▷ (f P) ⟩
    ↓ᵖ (suc k) (▷ᵖ (↓ᵖ k (f P)))         ≡ᵖ⟨ cong-↓ EQ2 ⟩
    ↓ᵖ (suc k) (▷ᵖ (↓ᵖ k (f (↓ᵖ k P))))  ≡ᵖ⟨ ≡ᵖ-sym (down-▷ (f (↓ᵖ k P))) ⟩
    ↓ᵖ (suc k) (▷ᵖ (f (↓ᵖ k P)))
    QEDᵖ
  where
  EQ2 : ▷ᵖ (↓ᵖ k ((fun F) P)) ≡ᵖ ▷ᵖ (↓ᵖ k ((fun F) (↓ᵖ k P)))
  EQ2 = cong-▷ᵖ (good F)

goodness-▷ : ∀ {k : Kind}{A}{B} (F : Fun A B k)
  → wellfounded (λ P → ▷ᵖ ((fun F) P))
goodness-▷ {Continuous} F = wellfounded-▷ F
goodness-▷ {Wellfounded} F = wellfounded-▷ (WF⇒C F)

abstract
  cong-▷ : ∀{A}{B}{kf}
       (F : Fun A B kf)
     → congᵖ (λ P → ▷ᵖ ((fun F) P))
  cong-▷ F PQ x 0 = ⇔-intro (λ x → tt) (λ x → tt)
  cong-▷ F PQ x (suc i) =
      ⇔-intro
        (λ FPxi → ⇔-to (congr F PQ x i) FPxi)
        (λ FQxi → ⇔-fro (congr F PQ x i) FQxi)

▷ᶠ : ∀{A}{B}{kF}
   → Fun A B kF
     -------------------
   → Fun A B Wellfounded
▷ᶠ {A}{B}{kF} F = record { fun = (λ P → ▷ᵖ ((fun F) P))
              ; good = goodness-▷ F
              ; congr = cong-▷ F
              }

{------- Flip --------}

flip : ∀{A}{B}{C}{K}
   → (A → Fun C B K)
   → (B → (Predᵒ C → Predᵒ A))
flip F b P = λ a → (fun (F a) P) b

abstract
  goodness-flip : ∀{A}{B}{C}{K}
    → (F : A → Fun C B K)
    → (b : B)
    → goodness K (flip F b)
  goodness-flip {A}{B}{C} {Continuous} F b {P}{k} x = good (F x) b
  goodness-flip {A}{B}{C} {Wellfounded} F b {P}{k} x = good (F x) b
    
  congᵖ-flip : ∀{A}{B}{C}{K}
    → (F : A → Fun C B K)
    → (b : B)
     → congᵖ (flip F b)
  congᵖ-flip {A}{B}{C}{K} F b P≡Q a = congr (F a) P≡Q b
    
flipᶠ : ∀{A}{B}{C}{K}
   → (A → Fun C B K)
     ----------------
   → (B → Fun C A K)
flipᶠ {A}{B}{C}{K} F b =
  record { fun = flip F b
         ; good = goodness-flip F b
         ; congr = congᵖ-flip F b
         }

{------- Recur --------}

abstract
  continuous-recur : ∀{A}{B}
     → (a : A)
     → continuous{A}{B} (λ P → P a ˢ)
  continuous-recur a {P}{k} v zero = ⇔-intro (λ x → tt) (λ x → tt)
  continuous-recur a {P}{k} v (suc i) =
      ⇔-intro
      (λ {(si<k , Psi) → si<k , (si<k , Psi)})
      (λ {(si<k , (_ , Psi)) → si<k , Psi})

  cong-recur : ∀ {A}{B}(a : A) → congᵖ{A}{B} (λ P → P a ˢ)
  cong-recur a PQ v i = PQ a i

recur : ∀{A}{B}
   → A
     ------------------
   → Fun A B Continuous
recur a =
  record { fun = λ P → (P a) ˢ 
         ; good = λ {P} {k} → continuous-recur a {P}{k}
         ; congr = cong-recur a
         }

{-------------------------------------------------------------------------------
  Fixpoint Theorem
-------------------------------------------------------------------------------}

abstract
  lemma18a : ∀{A}
     → (k : ℕ)
     → (F : Fun A A Wellfounded)
     → ↓ᵖ k (μᵒ F) ≡ᵖ ↓ᵖ k (iter k (fun F) ⊤ᵖ)
  lemma18a zero F x zero = ⇔-intro (λ x → tt) (λ x → tt)
  lemma18a zero F x (suc i) = ⇔-intro (λ { (() , b)}) (λ { (() , b)})
  lemma18a (suc k′) F v zero = ⇔-intro (λ x → tt) (λ x → tt)
  lemma18a (suc k′) F v (suc j′) =
      let k = suc k′ in
      let j = suc j′ in
      #((↓ᵖ k (μᵒ F)) v) j
                                  ⇔⟨ ⇔-intro (λ { (j<k , μFvj) → j<k , μFvj})
                                              (λ {(j<k , μFvj) → j<k , μFvj}) ⟩
      (j < k  ×  (#((μᵒ F) v) j))             ⇔⟨ ⇔-intro (λ {(a , b) → a , b})
                                                         (λ {(a , b) → a , b}) ⟩
      (j < k  ×  #((iter (suc j) (fun F) ⊤ᵖ) v) j)
                                     ⇔⟨ ⇔-intro (λ {(a , b) → a , ≤-refl , b})
                                          (λ {(s≤s a , (b , c)) → s≤s a , c}) ⟩
      (j < k  ×  #((↓ᵖ (suc j) (iter (suc j) (fun F) ⊤ᵖ)) v) j)        ⇔⟨ EQ4 ⟩
      (j < k  ×  #((↓ᵖ (suc j) (iter k (fun F) ⊤ᵖ)) v) j)
                                    ⇔⟨ ⇔-intro (λ {(a , b) → a , (proj₂ b)})
                                             (λ {(a , b) → a , (≤-refl , b)}) ⟩
      (j < k  ×  #((iter k (fun F) ⊤ᵖ) v) j)
                                  ⇔⟨ ⇔-intro (λ {(a , b) → a , b}) (λ z → z) ⟩
      #((↓ᵖ k (iter k (fun F) ⊤ᵖ)) v) j
      QED
      where
        k : ℕ
        k = suc k′
        j : ℕ
        j = suc j′
        EQ4 : (j < k  ×  #((↓ᵖ (suc j) (iter (suc j) (fun F) ⊤ᵖ)) v) j)
               ⇔ (j < k  ×  #((↓ᵖ (suc j) (iter k (fun F) ⊤ᵖ)) v) j)  
        EQ4 = ⇔-intro (λ{(s≤s j≤k′ , (j<1+j , FμF)) → s≤s j≤k′ ,
          let ↓FμF = ⇔-to (lemma15b ⊤ᵖ F (s≤s j≤k′) v (suc j′)) (j<1+j , FμF)
          in j<1+j , proj₂ ↓FμF})
         (λ{(s≤s j≤k′ , (j<1+j , FμF)) → s≤s j≤k′ ,
          let ↓FμF = ⇔-fro (lemma15b ⊤ᵖ F (s≤s j≤k′) v (suc j′)) (j<1+j , FμF)
          in  j<1+j , (proj₂ ↓FμF)
          })

lemma18b : ∀{A}
   → (k : ℕ)
   → (F : Fun A A Wellfounded)
   → ↓ᵖ (suc k) ((fun F) (μᵒ F)) ≡ᵖ ↓ᵖ (suc k) (iter (suc k) (fun F) ⊤ᵖ)
lemma18b {A} k F =
      ↓ᵖ (suc k) ((fun F) (μᵒ F))                         ≡ᵖ⟨ good F ⟩
      ↓ᵖ (suc k) ((fun F) (↓ᵖ k (μᵒ F)))
                                          ≡ᵖ⟨ cong-↓ (congr F (lemma18a k F)) ⟩
      ↓ᵖ (suc k) ((fun F) (↓ᵖ k (iter k (fun F) ⊤ᵖ)))     ≡ᵖ⟨ ≡ᵖ-sym (good F) ⟩
      ↓ᵖ (suc k) ((fun F) (iter k (fun F) ⊤ᵖ))            ≡ᵖ⟨ ≡ᵖ-refl refl ⟩
      ↓ᵖ (suc k) (iter (suc k) (fun F) ⊤ᵖ)
    QEDᵖ
    
lemma19 : ∀{A}
   → (k : ℕ)
   → (F : Fun A A Wellfounded)
   → ↓ᵖ k (μᵒ F) ≡ᵖ ↓ᵖ k ((fun F) (μᵒ F))
lemma19 {A} k F =
      ↓ᵖ k (μᵒ F)                                  ≡ᵖ⟨ lemma18a k F ⟩
      ↓ᵖ k (iter k (fun F) ⊤ᵖ)                     ≡ᵖ⟨ lemma15b _ F (n≤1+n k) ⟩
      ↓ᵖ k (iter (suc k) (fun F) ⊤ᵖ)               ≡ᵖ⟨ ≡ᵖ-sym lemma17 ⟩
      ↓ᵖ k (↓ᵖ (suc k) (iter (suc k) (fun F) ⊤ᵖ))
                                           ≡ᵖ⟨ cong-↓ (≡ᵖ-sym (lemma18b _ F)) ⟩
      ↓ᵖ k (↓ᵖ (suc k) ((fun F) (μᵒ F)))           ≡ᵖ⟨ lemma17 ⟩
      ↓ᵖ k ((fun F) (μᵒ F))
    QEDᵖ

abstract
  down-eq : ∀{A}{P : Predᵒ A}{x}
     → (i : ℕ)
     → (#((↓ᵖ (suc i) P) x) i) ⇔ (# (P x) i)
  down-eq {A}{P}{x} zero = ⇔-intro (λ _ → tz (P x)) (λ _ → tt)
  down-eq {A}{P}{x} (suc i′) =
      ⇔-intro (λ (i<1+i , Pxi) → Pxi) (λ Pxi → s≤s (s≤s ≤-refl) , Pxi)

abstract
  equiv-down : ∀{A}{P Q : Predᵒ A}
     → (∀ k → ↓ᵖ k P ≡ᵖ ↓ᵖ k Q)
     → P ≡ᵖ Q
  equiv-down {A} {P} {Q} ↓PQ x zero = ⇔-intro (λ _ → tz (Q x)) (λ _ → tz (P x))
  equiv-down {A} {P} {Q} ↓PQ x (suc i′) =
    ⇔-intro
    (λ Pxi →
        let ↓P→↓Q = ⇔-to (↓PQ (suc (suc i′)) x (suc i′)) in
        let ↓P = ⇔-fro (down-eq{A}{P}{x} (suc i′)) Pxi in
        let ↓Q = ↓P→↓Q ↓P in
        let Qxi = proj₂ ↓Q in
        Qxi)
    (λ Qxi →
        let ↓Q→↓P = ⇔-fro (↓PQ (suc (suc i′)) x (suc i′)) in
        let ↓Q = ⇔-fro (down-eq{A}{Q}{x} (suc i′)) Qxi in
        let ↓P = ↓Q→↓P ↓Q in
        let Pxi = proj₂ ↓P in
        Pxi)

{- Theorem 20 -}
fixpoint : ∀{A}
   → (F : Fun A A Wellfounded)
   → μᵒ F ≡ᵖ (fun F) (μᵒ F)
fixpoint F = equiv-down (λ k → lemma19 k F)

{--------------- Useful Lemmas -------------------}

abstract
  cong-×ᵒ : ∀{S S′ T T′}
    → S ≡ᵒ S′
    → T ≡ᵒ T′ 
    → (S ×ᵒ T) ≡ᵒ (S′ ×ᵒ T′)
  cong-×ᵒ S=S′ T=T′ i =
      ⇔-intro
      (λ { (Si , Ti) → (⇔-to (S=S′ i) Si) , (⇔-to (T=T′ i) Ti)})
      (λ {(S′i , T′i) → (⇔-fro (S=S′ i) S′i) , (⇔-fro (T=T′ i) T′i)})

  cong-⊎ᵒ : ∀{S S′ T T′}
    → S ≡ᵒ S′
    → T ≡ᵒ T′ 
    → (S ⊎ᵒ T) ≡ᵒ (S′ ⊎ᵒ T′)
  cong-⊎ᵒ S=S′ T=T′ i =
    ⇔-intro
    (λ { (inj₁ Si) → inj₁ (⇔-to (S=S′ i) Si)
       ; (inj₂ Ti) → inj₂ (⇔-to (T=T′ i) Ti)})
    (λ { (inj₁ S′i) → inj₁ (⇔-fro (S=S′ i) S′i)
       ; (inj₂ T′i) → inj₂ (⇔-fro (T=T′ i) T′i)})

  cong-→ᵒ : ∀{S S′ T T′}
    → S ≡ᵒ S′
    → T ≡ᵒ T′ 
    → (S →ᵒ T) ≡ᵒ (S′ →ᵒ T′)
  cong-→ᵒ S=S′ T=T′ i =
    ⇔-intro
    (λ S→Ti k k≤i S′k → ⇔-to (T=T′ k) (S→Ti k k≤i (⇔-fro (S=S′ k) S′k)))
    (λ z k z₁ z₂ → ⇔-fro (T=T′ k) (z k z₁ (⇔-to (S=S′ k) z₂)))

{---------------------- Proof Theory for Step Indexed Logic -------------------}

Πᵒ : List Setᵒ → Setᵒ
Πᵒ [] = ⊤ᵒ
Πᵒ (P ∷ 𝓟) = P ×ᵒ Πᵒ 𝓟 

abstract 
  infix 2 _⊢ᵒ_
  _⊢ᵒ_ : List Setᵒ → Setᵒ → Set
  𝓟 ⊢ᵒ P = ∀ n → # (Πᵒ 𝓟) n → # P n

  ⊢ᵒ-intro : ∀{𝓟}{P}
     → (∀ n → # (Πᵒ 𝓟) n → # P n)
     → 𝓟 ⊢ᵒ P
  ⊢ᵒ-intro 𝓟→P = 𝓟→P

  ⊢ᵒ-elim : ∀{𝓟}{P}
     → 𝓟 ⊢ᵒ P
     → (∀ n → # (Πᵒ 𝓟) n → # P n)
  ⊢ᵒ-elim 𝓟⊢P = 𝓟⊢P

downClosed-Πᵒ :
    (𝓟 : List Setᵒ)
  → downClosed (# (Πᵒ 𝓟))
downClosed-Πᵒ [] = λ n _ k _ → tt
downClosed-Πᵒ (P ∷ 𝓟) n (Pn , ⊨𝓟n) k k≤n =
    (down P n Pn k k≤n) , (downClosed-Πᵒ 𝓟 n ⊨𝓟n k k≤n)

▷-suc : ∀{S : Setᵒ}{n}
   → # (▷ᵒ S) (suc n)
   → # S n
▷-suc {S}{n} Ssn = Ssn

abstract
  ⊢ᵒ-mono : ∀ {𝓟}{P}
     → 𝓟 ⊢ᵒ P
       ------------
     → 𝓟 ⊢ᵒ (▷ᵒ P)
  ⊢ᵒ-mono {𝓟}{P} ⊢P zero ⊨𝓟n = tt
  ⊢ᵒ-mono {𝓟}{P} ⊢P (suc n) ⊨𝓟n =
    let ⊨𝓟n = downClosed-Πᵒ 𝓟 (suc n) ⊨𝓟n n (n≤1+n n) in
    ⊢P n ⊨𝓟n

  ⊢ᵒ-lob : ∀ {𝓟}{P}
     → (▷ᵒ P) ∷ 𝓟 ⊢ᵒ P
       -----------------------
     → 𝓟 ⊢ᵒ P
  ⊢ᵒ-lob {𝓟}{P} step zero ⊨𝓟n = tz P
  ⊢ᵒ-lob {𝓟}{P} step (suc n) ⊨𝓟sn =
    let ⊨𝓟n = downClosed-Πᵒ 𝓟 (suc n) ⊨𝓟sn n (n≤1+n n) in
    let Pn = ⊢ᵒ-lob {𝓟}{P} step n ⊨𝓟n in
    step (suc n) (Pn , ⊨𝓟sn)

  ▷× : ∀{𝓟 P Q}
     → 𝓟 ⊢ᵒ (▷ᵒ (P ×ᵒ Q))
       ----------------------
     → 𝓟 ⊢ᵒ (▷ᵒ P) ×ᵒ (▷ᵒ Q)
  ▷× ▷P×Q zero = λ _ → tt , tt
  ▷× ▷P×Q (suc n) = ▷P×Q (suc n)

  ▷⊎ : ∀{𝓟 P Q}
     → 𝓟 ⊢ᵒ (▷ᵒ (P ⊎ᵒ Q))
       ----------------------
     → 𝓟 ⊢ᵒ (▷ᵒ P) ⊎ᵒ (▷ᵒ Q)
  ▷⊎ ▷P⊎Q zero = λ _ → inj₁ tt
  ▷⊎ ▷P⊎Q (suc n) = ▷P⊎Q (suc n) 

  ▷→ : ∀{𝓟 P Q}
     → 𝓟 ⊢ᵒ (▷ᵒ (P →ᵒ Q))
       ----------------------
     → 𝓟 ⊢ᵒ (▷ᵒ P) →ᵒ (▷ᵒ Q)
  ▷→ ▷P→Q zero ⊨𝓟n .zero z≤n tt = tt
  ▷→ ▷P→Q (suc n) ⊨𝓟n .zero z≤n ▷Pj = tt
  ▷→ ▷P→Q (suc n) ⊨𝓟n (suc j) (s≤s j≤n) Pj = ▷P→Q (suc n) ⊨𝓟n j j≤n Pj

  ▷∀ : ∀{𝓟}{A}{P : A → Setᵒ}
     → 𝓟 ⊢ᵒ ▷ᵒ (∀ᵒ[ a ] P a)
       ------------------------
     → 𝓟 ⊢ᵒ (∀ᵒ[ a ] ▷ᵒ P a)
  ▷∀ 𝓟⊢▷∀P zero ⊨𝓟n a = tt
  ▷∀ 𝓟⊢▷∀P (suc n) ⊨𝓟sn a = 𝓟⊢▷∀P (suc n) ⊨𝓟sn a

abstract
  substᵒ : ∀{𝓟}{P Q : Setᵒ}
    → P ≡ᵒ Q
      -------------------
    → 𝓟 ⊢ᵒ P  →  𝓟 ⊢ᵒ Q
  substᵒ P=Q 𝓟⊢P n ⊨𝓟n = ⇔-to (P=Q n) (𝓟⊢P n ⊨𝓟n)

  ≡ᵖ⇒⊢ᵒ : ∀ 𝓟 {A} (P Q : Predᵒ A) {a : A}
    → 𝓟 ⊢ᵒ P a
    → P ≡ᵖ Q
      ---------------
    → 𝓟 ⊢ᵒ Q a
  ≡ᵖ⇒⊢ᵒ 𝓟 {A} P Q {a} 𝓟⊢P P=Q n ⊨𝓟n =
      let Pan = 𝓟⊢P n ⊨𝓟n in
      let Qan = ⇔-to (P=Q a n) Pan in
      Qan

⊢ᵒ-unfold : ∀ {A}{𝓟}{F : Fun A A Wellfounded}{a : A}
  → 𝓟 ⊢ᵒ (μᵒ F) a
    ------------------------------
  → 𝓟 ⊢ᵒ ((fun F) (μᵒ F)) a
⊢ᵒ-unfold {A}{𝓟}{F}{a} ⊢μa =
    ≡ᵖ⇒⊢ᵒ 𝓟 (μᵒ F) ((fun F) (μᵒ F)) ⊢μa (fixpoint F)

⊢ᵒ-fold : ∀ {A}{𝓟}{F : Fun A A Wellfounded}{a : A}
  → 𝓟 ⊢ᵒ ((fun F) (μᵒ F)) a
    ------------------------------
  → 𝓟 ⊢ᵒ (μᵒ F) a
⊢ᵒ-fold {A}{𝓟}{F}{a} ⊢μa =
    ≡ᵖ⇒⊢ᵒ 𝓟 ((fun F) (μᵒ F)) (μᵒ F) ⊢μa (≡ᵖ-sym (fixpoint F))

abstract
  ttᵒ : ∀{𝓟 : List Setᵒ}
    → 𝓟 ⊢ᵒ ⊤ᵒ
  ttᵒ n _ = tt  

  ⊥-elimᵒ : ∀{𝓟 : List Setᵒ}
    → 𝓟 ⊢ᵒ ⊥ᵒ
    → (P : Setᵒ)
    → 𝓟 ⊢ᵒ P
  ⊥-elimᵒ ⊢⊥ P zero ⊨𝓟n = tz P
  ⊥-elimᵒ ⊢⊥ P (suc n) ⊨𝓟sn = ⊥-elim (⊢⊥ (suc n) ⊨𝓟sn)

  _,ᵒ_ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
    → 𝓟 ⊢ᵒ P
    → 𝓟 ⊢ᵒ Q
      ------------
    → 𝓟 ⊢ᵒ P ×ᵒ Q
  (𝓟⊢P ,ᵒ 𝓟⊢Q) n ⊨𝓟n = 𝓟⊢P n ⊨𝓟n , 𝓟⊢Q n ⊨𝓟n

  proj₁ᵒ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
    → 𝓟 ⊢ᵒ P ×ᵒ Q
      ------------
    → 𝓟 ⊢ᵒ P
  proj₁ᵒ 𝓟⊢P×Q n ⊨𝓟n = proj₁ (𝓟⊢P×Q n ⊨𝓟n)

  proj₂ᵒ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
    → 𝓟 ⊢ᵒ P ×ᵒ Q
      ------------
    → 𝓟 ⊢ᵒ Q
  proj₂ᵒ 𝓟⊢P×Q n ⊨𝓟n = proj₂ (𝓟⊢P×Q n ⊨𝓟n)

  inj₁ᵒ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
    → 𝓟 ⊢ᵒ P
      ------------
    → 𝓟 ⊢ᵒ P ⊎ᵒ Q
  inj₁ᵒ 𝓟⊢P n ⊨𝓟n = inj₁ (𝓟⊢P n ⊨𝓟n)

  inj₂ᵒ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
    → 𝓟 ⊢ᵒ Q
      ------------
    → 𝓟 ⊢ᵒ P ⊎ᵒ Q
  inj₂ᵒ 𝓟⊢Q n ⊨𝓟n = inj₂ (𝓟⊢Q n ⊨𝓟n)

  caseᵒ : ∀{𝓟 : List Setᵒ }{P Q R : Setᵒ}
    → 𝓟 ⊢ᵒ P ⊎ᵒ Q
    → P ∷ 𝓟 ⊢ᵒ R
    → Q ∷ 𝓟 ⊢ᵒ R
      ------------
    → 𝓟 ⊢ᵒ R
  caseᵒ 𝓟⊢P⊎Q P∷𝓟⊢R Q∷𝓟⊢R n ⊨𝓟n
      with 𝓟⊢P⊎Q n ⊨𝓟n
  ... | inj₁ Pn = P∷𝓟⊢R n (Pn , ⊨𝓟n)
  ... | inj₂ Qn = Q∷𝓟⊢R n (Qn , ⊨𝓟n)

  case3ᵒ : ∀{𝓟 : List Setᵒ }{P Q R S : Setᵒ}
    → 𝓟 ⊢ᵒ P ⊎ᵒ Q ⊎ᵒ R
    → P ∷ 𝓟 ⊢ᵒ S
    → Q ∷ 𝓟 ⊢ᵒ S
    → R ∷ 𝓟 ⊢ᵒ S
      ------------
    → 𝓟 ⊢ᵒ S
  case3ᵒ 𝓟⊢P⊎Q⊎R P∷𝓟⊢S Q∷𝓟⊢S R∷𝓟⊢S n ⊨𝓟n
      with 𝓟⊢P⊎Q⊎R n ⊨𝓟n
  ... | inj₁ Pn = P∷𝓟⊢S n (Pn , ⊨𝓟n)
  ... | inj₂ (inj₁ Qn) = Q∷𝓟⊢S n (Qn , ⊨𝓟n)
  ... | inj₂ (inj₂ Rn) = R∷𝓟⊢S n (Rn , ⊨𝓟n)

  →ᵒI : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
    → P ∷ 𝓟 ⊢ᵒ Q
      ------------
    → 𝓟 ⊢ᵒ P →ᵒ Q
  →ᵒI {𝓟} P∷𝓟⊢Q n ⊨𝓟n j j≤n Pj =
      P∷𝓟⊢Q j (Pj , downClosed-Πᵒ 𝓟 n ⊨𝓟n j j≤n)

  appᵒ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
    → 𝓟 ⊢ᵒ P →ᵒ Q
    → 𝓟 ⊢ᵒ P
      ------------
    → 𝓟 ⊢ᵒ Q
  appᵒ {𝓟} 𝓟⊢P→Q 𝓟⊢P n ⊨𝓟n =
     let Pn = 𝓟⊢P n ⊨𝓟n in
     let Qn = 𝓟⊢P→Q n ⊨𝓟n n ≤-refl Pn in
     Qn

  {- TODO: remove the following -}
  ▷→▷ : ∀{𝓟 P Q}
     → 𝓟 ⊢ᵒ ▷ᵒ P
     → 𝓟 ⊢ᵒ P →ᵒ Q
       ------------
     → 𝓟 ⊢ᵒ ▷ᵒ Q
  ▷→▷ {𝓟}{P}{Q} ▷P P→Q n ⊨𝓟n =
    let ▷Q = appᵒ{𝓟}{▷ᵒ P}{▷ᵒ Q}
                (▷→{𝓟}{P}{Q}
                    (⊢ᵒ-mono{𝓟}{P →ᵒ Q} P→Q)) ▷P in
    ▷Q n ⊨𝓟n


  ⊢ᵒ-∀-intro : ∀{𝓟 : List Setᵒ }{A}{P : A → Setᵒ}
    → (∀ a → 𝓟 ⊢ᵒ P a)
      ----------------------
    → 𝓟 ⊢ᵒ ∀ᵒ P
  ⊢ᵒ-∀-intro ∀Pa n ⊨𝓟n a = ∀Pa a n ⊨𝓟n

  instᵒ : ∀{𝓟 : List Setᵒ }{A}{P : A → Setᵒ}
    → 𝓟 ⊢ᵒ ∀ᵒ P
    → (a : A)
      ---------
    → 𝓟 ⊢ᵒ P a
  instᵒ ⊢∀P a n ⊨𝓟n = ⊢∀P n ⊨𝓟n a

Λᵒ-syntax = ⊢ᵒ-∀-intro
infix 1 Λᵒ-syntax
syntax Λᵒ-syntax (λ a → ⊢Pa) = Λᵒ[ a ] ⊢Pa

abstract
  Zᵒ : ∀{𝓟 : List Setᵒ}{S : Setᵒ}
     → S ∷ 𝓟 ⊢ᵒ S
  Zᵒ n (Sn , ⊨𝓟n) = Sn

  Sᵒ : ∀{𝓟 : List Setᵒ}{T : Setᵒ}{S : Setᵒ}
     → 𝓟 ⊢ᵒ T
     → S ∷ 𝓟 ⊢ᵒ T
  Sᵒ 𝓟⊢T n (Sn , ⊨𝓟n) = 𝓟⊢T n ⊨𝓟n

  ⊢ᵒ-swap : ∀{𝓟 : List Setᵒ}{T : Setᵒ}{S S′ : Setᵒ}
     → S ∷ S′ ∷ 𝓟 ⊢ᵒ T
     → S′ ∷ S ∷ 𝓟 ⊢ᵒ T
  ⊢ᵒ-swap {𝓟}{T}{S}{S′} SS′𝓟⊢T n (S′n , Sn , ⊨𝓟n) =
      SS′𝓟⊢T n (Sn , S′n , ⊨𝓟n)

  →ᵒI′ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
    → (P ∷ 𝓟 ⊢ᵒ P → P ∷ 𝓟 ⊢ᵒ Q)
      -----------------------
    → 𝓟 ⊢ᵒ P →ᵒ Q
  →ᵒI′ {𝓟}{P}{Q} P→Q = →ᵒI{𝓟}{P}{Q} (P→Q (Zᵒ{𝓟}{P}))

λᵒ-syntax = →ᵒI′
infix 1 λᵒ-syntax
syntax λᵒ-syntax (λ ⊢P → ⊢Q) = λᵒ[ ⊢P ] ⊢Q

abstract
  ⊢ᵒ-Sᵒ-intro : ∀{𝓟}{S : Set}
     → S
     → 𝓟 ⊢ᵒ (S)ᵒ
  ⊢ᵒ-Sᵒ-intro s zero ⊨𝓟n = tt
  ⊢ᵒ-Sᵒ-intro s (suc n) ⊨𝓟n = s

  Sᵒ→Tᵒ⇒⊢ᵒ : ∀ {𝓟} {S T : Set}
    → 𝓟 ⊢ᵒ (S)ᵒ
    → (S → T)
      ----------
    → 𝓟 ⊢ᵒ (T)ᵒ
  Sᵒ→Tᵒ⇒⊢ᵒ 𝓟⊢S S→T zero ⊨𝓟n = tt
  Sᵒ→Tᵒ⇒⊢ᵒ 𝓟⊢S S→T (suc n) ⊨𝓟n = S→T (𝓟⊢S (suc n) ⊨𝓟n)

  Sᵒ⊢ᵒ : ∀ {𝓟}{S : Set}{R : Setᵒ}
     → (S → 𝓟 ⊢ᵒ R)
     → (S)ᵒ ∷ 𝓟 ⊢ᵒ R
  Sᵒ⊢ᵒ {𝓟} {S}{R} S→R zero (Sn , ⊨𝓟n) = tz R
  Sᵒ⊢ᵒ {𝓟} S→R (suc n) (Sn , ⊨𝓟n) = S→R Sn (suc n) ⊨𝓟n

  caseᵒ-L : ∀{𝓟 : List Setᵒ }{P Q R : Setᵒ}
    → P ∷ 𝓟 ⊢ᵒ R
    → Q ∷ 𝓟 ⊢ᵒ R
      ------------------
    → (P ⊎ᵒ Q) ∷ 𝓟 ⊢ᵒ R
  caseᵒ-L{𝓟}{P}{Q}{R} P∷𝓟⊢R Q∷𝓟⊢R =
      let 𝓟′ = P ∷ Q ∷ (P ⊎ᵒ Q) ∷ 𝓟 in
      let ⊢P⊎Q : (P ⊎ᵒ Q) ∷ 𝓟 ⊢ᵒ P ⊎ᵒ Q
          ⊢P⊎Q = Zᵒ{𝓟}{P ⊎ᵒ Q} in
      let P⊢R = ⊢ᵒ-swap{𝓟}{R}{P ⊎ᵒ Q}{P}
            (Sᵒ{P ∷ 𝓟}{R}{P ⊎ᵒ Q} P∷𝓟⊢R) in
      let Q⊢R = ⊢ᵒ-swap{𝓟}{R}{P ⊎ᵒ Q}{Q}
            (Sᵒ{Q ∷ 𝓟}{R}{P ⊎ᵒ Q} Q∷𝓟⊢R) in
      caseᵒ{(P ⊎ᵒ Q) ∷ 𝓟}{P}{Q}{R} ⊢P⊎Q P⊢R Q⊢R

abstract
  ◁▷ᵒ : ∀{S : Setᵒ} → ◁ᵒ (▷ᵒ S) ≡ᵒ S
  ◁▷ᵒ {S} zero = ⇔-intro (λ x → tz S) (λ x → tt)
  ◁▷ᵒ {S} (suc i) = ⇔-intro (λ z → z) (λ z → z)

◁̃ : List Setᵒ → List Setᵒ
◁̃ [] = []
◁̃ (P ∷ 𝓟) = ◁ᵒ P ∷ ◁̃ 𝓟

⊨◁𝓟 : ∀{𝓟}{n}
   → # (Πᵒ 𝓟) (suc n)
   → # (Πᵒ (◁̃ 𝓟)) n
⊨◁𝓟 {[]} {n} ⊨𝓟sn = tt
⊨◁𝓟 {P ∷ 𝓟} {zero} (Psn , ⊨𝓟sn) = tt , ⊨◁𝓟{𝓟} ⊨𝓟sn
⊨◁𝓟 {P ∷ 𝓟} {suc n} (Psn , ⊨𝓟sn) = Psn , ⊨◁𝓟{𝓟} ⊨𝓟sn

abstract
  weak-▷ : ∀{𝓟}{P}
     → ◁̃ 𝓟 ⊢ᵒ P
       ----------
     → 𝓟 ⊢ᵒ ▷ᵒ P
  weak-▷ {𝓟} {P} ◁𝓟⊢P zero ⊨𝓟n = tt
  weak-▷ {𝓟} {P} ◁𝓟⊢P (suc n) ⊨𝓟sn = ◁𝓟⊢P n (⊨◁𝓟{𝓟} ⊨𝓟sn)

  ◁Pᵒ : ∀{𝓟}{P : Set}
     → 𝓟 ⊢ᵒ ◁ᵒ (P ᵒ)
       -------------
     → 𝓟 ⊢ᵒ P ᵒ
  ◁Pᵒ ⊢◁P zero ⊨𝓟n = tt
  ◁Pᵒ ⊢◁P (suc n) ⊨𝓟n = ⊢◁P (suc n) ⊨𝓟n

sucP⊢ᵒQ : ∀{𝓟}{P Q : Setᵒ}
   → (∀{n} → # P (suc n) → P ∷ 𝓟 ⊢ᵒ Q)
   → P ∷ 𝓟 ⊢ᵒ Q
sucP⊢ᵒQ {𝓟}{P}{Q} Psn⊢Q =
    ⊢ᵒ-intro λ { zero (Pn , 𝓟n) → tz Q
               ; (suc n) (Psn , 𝓟sn) →
                  let ⊢Q = Psn⊢Q Psn in
                  let Qsn = ⊢ᵒ-elim ⊢Q (suc n) (Psn , 𝓟sn) in
                  Qsn}

⊢ᵒ-sucP : ∀{𝓟}{P Q : Setᵒ}
   → 𝓟 ⊢ᵒ P
   → (∀{n} → # P (suc n) → 𝓟 ⊢ᵒ Q)
   → 𝓟 ⊢ᵒ Q
⊢ᵒ-sucP {𝓟}{P}{Q} ⊢P Psn⊢Q =
    ⊢ᵒ-intro λ { zero x → tz Q
               ; (suc n) 𝓟sn →
                 let ⊢Q = Psn⊢Q (⊢ᵒ-elim ⊢P (suc n) 𝓟sn) in
                 let Qsn = ⊢ᵒ-elim ⊢Q (suc n) 𝓟sn in
                 Qsn}


{- This example shows that making ⊢ᵒ abstract solves the
   problem regarding inferece of implicit parameteters. -Jeremy -}
example-⊢ᵒ1 : ∀{P Q} → P ∷ Q ∷ [] ⊢ᵒ Q
example-⊢ᵒ1 = Sᵒ Zᵒ

example-⊢ᵒ2 : [] ⊢ᵒ ▷ᵒ (∀ᵒ[ n ] (0 ≤ n)ᵒ)
              → [] ⊢ᵒ (∀ᵒ[ n ] (▷ᵒ ((0 ≤ n)ᵒ)))
example-⊢ᵒ2 ⊢▷∀n = ▷∀{P = λ n → _} ⊢▷∀n

