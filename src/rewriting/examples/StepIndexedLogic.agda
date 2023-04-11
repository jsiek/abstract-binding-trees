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
--open import rewriting.examples.IfAndOnlyIf

open import rewriting.examples.EquivalenceRelation public

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
    → Eq._≡_ S T
    → S ≡ᵒ T
  ≡ᵒ-refl refl i = ⩦-refl refl

  ≡ᵒ-sym : ∀{S T : Setᵒ}
    → S ≡ᵒ T
    → T ≡ᵒ S
  ≡ᵒ-sym ST i = ⩦-sym (ST i)

  ≡ᵒ-trans : ∀{S T R : Setᵒ}
    → S ≡ᵒ T
    → T ≡ᵒ R
    → S ≡ᵒ R
  ≡ᵒ-trans ST TR i = ⩦-trans (ST i) (TR i)

instance
  SIL-Eqᵒ : EquivalenceRelation Setᵒ
  SIL-Eqᵒ = record { _⩦_ = _≡ᵒ_ ; ⩦-refl = ≡ᵒ-refl
                   ; ⩦-sym = ≡ᵒ-sym ; ⩦-trans = ≡ᵒ-trans }

exampleᵒ : ∀{P Q : Setᵒ} → P ≡ᵒ Q → Q ≡ᵒ P
exampleᵒ {P}{Q} P=Q =
  Q     ⩦⟨ ≡ᵒ-sym P=Q ⟩
  P     ∎

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
    → Eq._≡_ P Q
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

instance
  SIL-Eqᵖ : ∀{A} → EquivalenceRelation (Predᵒ A)
  SIL-Eqᵖ = record { _⩦_ = _≡ᵖ_ ; ⩦-refl = ≡ᵖ-refl
                   ; ⩦-sym = ≡ᵖ-sym ; ⩦-trans = ≡ᵖ-trans }

exampleᵖ : ∀{A}{P Q : Predᵒ A} → P ≡ᵖ Q → Q ≡ᵖ P
exampleᵖ {A}{P}{Q} P=Q =
  Q     ⩦⟨ ≡ᵖ-sym P=Q ⟩
  P
  ∎

record Inhabited (A : Set) : Set where
  field
    elt : A
open Inhabited {{...}} public

{- Signature of a Step-indexed Formula -}

record StepIndexedFormula : Set₂ where
  infixr 7 _×ᵒ_
  infixr 7 _⊎ᵒ_
  infixr 6 _→ᵒ_
  infixr 8 _ᵒ
  infixr 8 ▷ᵒ_
  infixr 8 ◁ᵒ_
  field
    Frmᵒ : Set₁
    ⊥ᵒ : Frmᵒ
    ⊤ᵒ : Frmᵒ
    _ᵒ : Set → Frmᵒ
    _×ᵒ_ : Frmᵒ → Frmᵒ → Frmᵒ
    _⊎ᵒ_ : Frmᵒ → Frmᵒ → Frmᵒ
    _→ᵒ_ : Frmᵒ → Frmᵒ → Frmᵒ
    ∀ᵒ : ∀{A : Set} → (A → Frmᵒ) → Frmᵒ
    ∃ᵒ : ∀{A : Set}{{_ : Inhabited A}} → (A → Frmᵒ) → Frmᵒ
    ▷ᵒ_ : Frmᵒ → Frmᵒ
    ◁ᵒ_ : Frmᵒ → Frmᵒ
    ↓ᵒ : ℕ → Frmᵒ → Frmᵒ
open StepIndexedFormula {{...}} public

{- Step Indexed Propositions -}

botᵒ : Setᵒ
botᵒ = record { # = λ { zero → ⊤ ; (suc k) → ⊥ }
            ; down = λ { zero ⊥n .zero z≤n → tt}
            ; tz = tt
            }

topᵒ : Setᵒ
topᵒ = record { # = λ k → ⊤
            ; down = λ n _ k _ → tt
            ; tz = tt
            }
              
andᵒ : Setᵒ → Setᵒ → Setᵒ
andᵒ P Q = record { # = λ k → # P k × # Q k
                ; down = λ k (Pk , Qk) j j≤k →
                          (down P k Pk j j≤k) , (down Q k Qk j j≤k)
                ; tz = (tz P) , (tz Q)
                }
                
orᵒ : Setᵒ → Setᵒ → Setᵒ
orᵒ P Q = record { # = λ k → # P k ⊎ # Q k
                ; down = λ { k (inj₁ Pk) j j≤k → inj₁ (down P k Pk j j≤k)
                           ; k (inj₂ Qk) j j≤k → inj₂ (down Q k Qk j j≤k)}
                ; tz = inj₁ (tz P)
                }

impliesᵒ : Setᵒ → Setᵒ → Setᵒ
impliesᵒ P Q = record { # = λ k → ∀ j → j ≤ k → # P j → # Q j
                ; down = λ k P→Q j j≤k i i≤j Pi → P→Q i (≤-trans i≤j j≤k) Pi
                ; tz = λ { .zero z≤n _ → tz Q}
                }

allᵒ : ∀{A : Set} → (Predᵒ A) → Setᵒ
allᵒ{A} P = record { # = λ k → ∀ (a : A) → # (P a) k
                   ; down = λ n ∀Pn k k≤n a → down (P a) n (∀Pn a) k k≤n
                   ; tz = λ a → tz (P a) }

∀ᵒ-syntax = ∀ᵒ
infix 1 ∀ᵒ-syntax
syntax ∀ᵒ-syntax (λ x → P) = ∀ᵒ[ x ] P

existᵒ : ∀{A : Set}{{_ : Inhabited A}} → (Predᵒ A) → Setᵒ
existᵒ{A} P = record { # = λ k → Σ[ a ∈ A ] # (P a) k
                     ; down = λ n (a , Pa) k k≤n → a , (down (P a) n Pa k k≤n)
                     ; tz = elt , tz (P elt)
                     }

∃ᵒ-syntax = ∃ᵒ
infix 1 ∃ᵒ-syntax
syntax ∃ᵒ-syntax (λ x → P) = ∃ᵒ[ x ] P

constᵒ : Set → Setᵒ
constᵒ S = record { # = λ { zero → ⊤ ; (suc k) → S }
             ; down = λ { k Sk zero j≤k → tt
                        ; (suc k) Sk (suc j) j≤k → Sk}
             ; tz = tt
             }

laterᵒ : Setᵒ → Setᵒ
laterᵒ P = record
             { # = λ { zero → ⊤ ; (suc k) → # P k }
             ; down = λ { zero ▷Pn .zero z≤n → tt
                        ; (suc n) ▷Pn .zero z≤n → tt
                        ; (suc n) ▷Pn (suc k) (s≤s k≤n) → down P n ▷Pn k k≤n}
             ; tz = tt
             }

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

approxᵒ : ℕ → Setᵒ → Setᵒ
approxᵒ k S = record { # = ↓ₒ k S 
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

beforeᵒ : Setᵒ → Setᵒ
beforeᵒ P = record { # = λ { zero → ⊤ ; (suc k) → # P (suc (suc k)) }
              ; down = λ { zero ◁Pk .zero z≤n → tt
                         ; (suc k) ◁Pk zero j≤k → tt
                         ; (suc k) ◁Pk (suc j) j≤k →
                            down P (suc (suc k)) ◁Pk (suc (suc j)) (s≤s j≤k)}
              ; tz = tt }
instance
  SILᵒ : StepIndexedFormula
  SILᵒ = record
           { Frmᵒ = Setᵒ ; ⊥ᵒ = botᵒ ; ⊤ᵒ = topᵒ ; _ᵒ = constᵒ
           ; _×ᵒ_ = andᵒ ; _⊎ᵒ_ = orᵒ ; _→ᵒ_ = impliesᵒ
           ; ∀ᵒ = allᵒ ; ∃ᵒ = existᵒ
           ; ▷ᵒ_ = laterᵒ ; ◁ᵒ_ = beforeᵒ ; ↓ᵒ = approxᵒ
           }

{- Step Indexed Predicates -}

flipᵖ : ∀{A}{B}
   → (A → Predᵒ B)
     -------------
   → (B → Predᵒ A)
flipᵖ F b = λ a → F a b

infixr 8 _ˢ
_ˢ  : Setᵒ → ∀{A} → Predᵒ A
(S ˢ) {A} = λ a → S

instance
  SILᵖ : ∀{A : Set} → StepIndexedFormula
  SILᵖ {A} = record
             { Frmᵒ = Predᵒ A
             ; ⊥ᵒ = λ a → ⊤ᵒ
             ; ⊤ᵒ = λ a → ⊤ᵒ
             ; _ᵒ = λ S a → S ᵒ
             ; _×ᵒ_ = λ P Q a → P a ×ᵒ Q a
             ; _⊎ᵒ_ = λ P Q a → P a ⊎ᵒ Q a
             ; _→ᵒ_ = λ P Q a → (P a →ᵒ Q a)
             ; ∀ᵒ = λ {A} F b → ∀ᵒ {A} (flipᵖ F b)
             ; ∃ᵒ = λ {A} F b → ∃ᵒ {A} (flipᵖ F b)
             ; ▷ᵒ_ = λ P a → ▷ᵒ (P a)
             ; ◁ᵒ_ = λ P a → ◁ᵒ (P a)
             ; ↓ᵒ = λ k P a → approxᵒ k (P a)
             } 

{------------ Continuous and Wellfounded Functions on Step Indexed Predicates -}

congᵖ : ∀{A}{B} (F : Predᵒ A → Predᵒ B) → Set₁
congᵖ F = ∀ {P Q} → P ≡ᵖ Q → (F P) ≡ᵖ (F Q)

abstract
  cong-↓ : ∀{A}{k : ℕ}
    → congᵖ{A}{A} (↓ᵒ k)
  cong-↓ {k}{P}{Q} PQ x zero = ⇔-intro (λ x → tt) (λ x → tt)
  cong-↓ {k}{P}{Q} PQ x (suc i) =
      ⇔-intro
       (λ { (si<k , Pxsi) → si<k , let P→Q = (PQ x (suc i)) in ⇔-to P→Q Pxsi})
       (λ {(si<k , Qxsi) → si<k , let Q→P = (PQ x (suc i)) in ⇔-fro Q→P Qxsi})
                
continuous : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
continuous F = ∀ {P k} → ↓ᵒ k (F P) ≡ᵖ ↓ᵒ k (F (↓ᵒ k P))

wellfounded : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
wellfounded F = ∀ {P k} → ↓ᵒ (suc k) (F P) ≡ᵖ ↓ᵒ (suc k) (F (↓ᵒ k P))

data Kind : Set where
  Now : Kind
  Later : Kind

goodness : Kind → ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
goodness Now F = continuous F
goodness Later F = wellfounded F

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
  → Eq._≡_ (iter j F (iter (k ∸ j) F P)) (iter k F P)
iter-subtract {A = A} {P} F .zero k z≤n = refl
iter-subtract {A = A} {P} F (suc j) (suc k) (s≤s j≤k)
  rewrite iter-subtract{A = A}{P} F j k j≤k = refl


abstract 
  ↓ᵒ-zero : ∀{A}{P Q : Predᵒ A} → ↓ᵒ zero P ≡ᵖ ↓ᵒ zero Q
  ↓ᵒ-zero v zero = ⇔-intro (λ x → tt) (λ x → tt)
  ↓ᵒ-zero v (suc i) = ⇔-intro (λ{()}) (λ{()})

lemma15a : ∀{A} {P Q : Predᵒ A}{j}
  → (F : Fun A A Later)
  → ↓ᵒ j (iter j (fun F) P) ≡ᵖ ↓ᵒ j (iter j (fun F) Q)
lemma15a {A} {P}{Q} {zero} F = ↓ᵒ-zero
lemma15a {A} {P}{Q} {suc j} F =
    let f = fun F in
    ↓ᵒ (suc j) (f (iter j f P))                                    ⩦⟨ good F ⟩ 
    ↓ᵒ (suc j) (f (↓ᵒ j (iter j f P)))      ⩦⟨ cong-↓ (congr F (lemma15a F)) ⟩
    ↓ᵒ (suc j) (f (↓ᵒ j (iter j f Q)))                    ⩦⟨ ≡ᵖ-sym (good F) ⟩
    ↓ᵒ (suc j) (f (iter j f Q))
  ∎

lemma15b : ∀{A}(P : Predᵒ A){j k}
  → (F : Fun A A Later)
  → j ≤ k
  → ↓ᵒ j (iter j (fun F) P) ≡ᵖ ↓ᵒ j (iter k (fun F) P)
lemma15b{A} P {j}{k} F j≤k =
  let f = fun F in
  ↓ᵒ j (iter j f P)                                           ⩦⟨ lemma15a F ⟩
  ↓ᵒ j (iter j f (iter (k ∸ j) f P))
                              ⩦⟨ cong-↓ (≡ᵖ-refl (iter-subtract f j k j≤k)) ⟩
  ↓ᵒ j (iter k f P)
  ∎

dc-iter : ∀(i : ℕ){A}
   → (F : Predᵒ A → Predᵒ A)
   → ∀ v → downClosed (#(iter i F ⊤ᵒ v))
dc-iter zero F = λ v n _ k _ → tt
dc-iter (suc i) F = λ v → down (F (iter i F ⊤ᵒ) v)

μₚ : ∀{A} → (Predᵒ A → Predᵒ A) → (A → ℕ → Set)
μₚ F a k = #(iter (suc k) F ⊤ᵒ a) k

μᵒ : ∀{A}
   → Fun A A Later
     -------------------
   → Predᵒ A
μᵒ F a =  record { # = μₚ (fun F) a
                 ; down = dc-μ F a
                 ; tz = tz ((fun F (id ⊤ᵒ)) a)
                 }
  where
  dc-μ : ∀{A}
       (F : Fun A A Later)
     → (a : A)
     → downClosed (μₚ (fun F) a)
  dc-μ {A} F a k μFak zero j≤k = tz (fun F ⊤ᵒ a)
  dc-μ {A} F a (suc k′) μFak (suc j′) (s≤s j′≤k) = T
   where
   Y : # (iter (suc (suc k′)) (fun F) ⊤ᵒ a) (suc j′)
   Y = dc-iter (suc (suc k′)) (fun F) a (suc k′) μFak (suc j′) (s≤s j′≤k)
   Z : # (↓ᵒ (suc (suc j′)) (iter (suc (suc k′)) (fun F) ⊤ᵒ) a) (suc j′)
   Z = ↓ₒ-intro ((iter (suc (suc k′)) (fun F) ⊤ᵒ) a) ≤-refl Y
   eq = lemma15b ⊤ᵒ F (s≤s (s≤s j′≤k))
   W : # (↓ᵒ (suc (suc j′)) (iter (suc (suc j′)) (fun F) ⊤ᵒ) a) (suc j′)
   W = ≡ᵒ-to (apply-≡ᵖ (≡ᵖ-sym eq) a) (suc j′) Z 
   T : #(iter (suc (suc j′)) (fun F) ⊤ᵒ a) (suc j′)
   T = proj₂ W

{------------ Auxiliary Lemmas ----------}

abstract
  cong-→ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
     → P ≡ᵖ P′
     → Q ≡ᵖ Q′
     → (P →ᵒ Q)  ≡ᵖ  (P′ →ᵒ Q′)
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
     → P ×ᵒ Q  ≡ᵖ  P′ ×ᵒ Q′
  cong-×ᵖ {A}{P}{P′}{Q}{Q′} PP′ QQ′ v k = ⇔-intro to fro
    where
    to : # ((P ×ᵒ Q) v) k → # ((P′ ×ᵒ Q′) v) k
    to (Pvk , Qvk) = (⇔-to (PP′ v k) Pvk) , (⇔-to (QQ′ v k) Qvk)
    fro  : #((P′ ×ᵒ Q′) v) k → #((P ×ᵒ Q) v) k
    fro (P′vk , Q′vk) = (⇔-fro (PP′ v k) P′vk) , (⇔-fro (QQ′ v k) Q′vk)

  cong-⊎ᵖ : ∀{A}{P P′ Q Q′ : Predᵒ A}
     → P ≡ᵖ P′
     → Q ≡ᵖ Q′
     → P ⊎ᵒ Q  ≡ᵖ  P′ ⊎ᵒ Q′
  cong-⊎ᵖ {A}{P}{P′}{Q}{Q′} PP′ QQ′ v k = ⇔-intro to fro
    where
    to : #((P ⊎ᵒ Q) v) k → #((P′ ⊎ᵒ Q′) v) k
    to (inj₁ Pvk) = inj₁ (⇔-to (PP′ v k) Pvk)
    to (inj₂ Qvk) = inj₂ (⇔-to (QQ′ v k) Qvk)
    fro : #((P′ ⊎ᵒ Q′) v) k → #((P ⊎ᵒ Q) v) k
    fro (inj₁ P′vk) = inj₁ (⇔-fro (PP′ v k) P′vk)
    fro (inj₂ Q′vk) = inj₂ (⇔-fro (QQ′ v k) Q′vk)

  cong-▷ᵖ : ∀{A}{P P′ : Predᵒ A}
     → P ≡ᵖ P′
     → ▷ᵒ P ≡ᵖ ▷ᵒ P′
  cong-▷ᵖ PP′ v zero = ⇔-intro (λ x → tt) (λ x → tt)
  cong-▷ᵖ PP′ v (suc k) = ⇔-intro (λ x → ⇔-to (PP′ v k) x) (⇔-fro (PP′ v k))

{- ↓ᵒ is idempotent -}
abstract
  lemma17 : ∀{A}{P : Predᵒ A}{k}
     → ↓ᵒ k (↓ᵒ (suc k) P) ≡ᵖ ↓ᵒ k P
  lemma17 {A} x zero = ⇔-intro (λ x → tt) (λ x → tt)
  lemma17 {A} x (suc i) =
    ⇔-intro
      (λ { (fst , fst₁ , snd) → fst , snd})
      (λ { (fst , snd) → fst , (s≤s (<⇒≤ fst)) , snd})

  ↓-zero : ∀{A}{P Q : Predᵒ A}
     → ↓ᵒ 0 P ≡ᵖ ↓ᵒ 0 Q
  ↓-zero v zero = ⇔-intro (λ x → tt) (λ x → tt)
  ↓-zero v (suc i) = ⇔-intro (λ { (() , _)}) (λ {(() , _)})

wellfounded⇒continuous : ∀{A}{B}
   → (F : Fun A B Later)
   → continuous (fun F)
wellfounded⇒continuous F {P}{zero} = ↓-zero 
wellfounded⇒continuous F {P}{suc k} =
    let f = fun F in
    ↓ᵒ (suc k) (f P)                      ⩦⟨ good F ⟩
    ↓ᵒ (suc k) (f (↓ᵒ k P))              ⩦⟨ cong-↓ (congr F (≡ᵖ-sym lemma17)) ⟩
    ↓ᵒ (suc k) (f (↓ᵒ k (↓ᵒ (suc k) P)))  ⩦⟨ ≡ᵖ-sym (good F) ⟩
    ↓ᵒ (suc k) (f (↓ᵒ (suc k) P))
    ∎

WF⇒C : ∀{A}{B}
   → Fun A B Later
   → Fun A B Now
WF⇒C F = record { fun = fun F
                ; good = wellfounded⇒continuous F
                ; congr = congr F }   

choose : Kind → Kind → Kind
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later

{-------------- Functions on Step Index Predicates  --------------}

{------- Implication --------}

abstract
  down-fun : ∀{A} {P Q : Predᵒ A}{k}
     → ↓ᵒ k (P →ᵒ Q) ≡ᵖ ↓ᵒ k ((↓ᵒ k P) →ᵒ (↓ᵒ k Q))
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

continuous-→ : ∀{A}{B}(F G : Fun A B Now)
   → continuous (λ P → (fun F) P →ᵒ (fun G) P)
continuous-→ {A}{B} F G {P}{k} =
   let f = fun F in let g = fun G in
   ↓ᵒ k (f P →ᵒ g P)                                             ⩦⟨ down-fun ⟩
   ↓ᵒ k (↓ᵒ k (f P) →ᵒ ↓ᵒ k (g P))   ⩦⟨ cong-↓ (cong-→ᵖ (good F) (good G)) ⟩
   ↓ᵒ k (↓ᵒ k (f (↓ᵒ k P)) →ᵒ ↓ᵒ k (g (↓ᵒ k P)))          ⩦⟨ ≡ᵖ-sym down-fun ⟩
   ↓ᵒ k (f (↓ᵒ k P) →ᵒ g (↓ᵒ k P))
   ∎

wellfounded-→ : ∀{A}{B}(F G : Fun A B Later)
   → wellfounded (λ P → (fun F) P →ᵒ (fun G) P)
wellfounded-→ {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵒ (suc k) (f P →ᵒ g P)                                      ⩦⟨ down-fun ⟩
    ↓ᵒ (suc k) (↓ᵒ (suc k) (f P) →ᵒ ↓ᵒ (suc k) (g P))
                                     ⩦⟨ cong-↓ (cong-→ᵖ (good F) (good G)) ⟩
    ↓ᵒ (suc k) (↓ᵒ (suc k) (f (↓ᵒ k P)) →ᵒ ↓ᵒ (suc k) (g (↓ᵒ k P)))
                                                          ⩦⟨ ≡ᵖ-sym down-fun ⟩
    ↓ᵒ (suc k) (f (↓ᵒ k P) →ᵒ g (↓ᵒ k P))
    ∎

goodness-→ : ∀ {kf kg : Kind} {A}{B}
     (F : Fun A B kf)
     (G : Fun A B kg)
   → goodness (choose kf kg) (λ P → (fun F) P →ᵒ (fun G) P)
goodness-→ {Now}{Now} F G  = continuous-→ F G
goodness-→ {Now}{Later} F G = continuous-→ F (WF⇒C G)
goodness-→ {Later}{Now} F G = continuous-→ (WF⇒C F) G
goodness-→ {Later}{Later} F G = wellfounded-→ F G 

abstract
  cong-→ : ∀{A}{B}{kf}{kg}
       (F : Fun A B kf)
       (G : Fun A B kg)
     → congᵖ (λ P → (fun F) P →ᵒ (fun G) P)
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
  record { fun = λ P → fun F P →ᵒ fun G P
         ; good = goodness-→ F G
         ; congr = cong-→ F G
         }

{------- Conjunction --------}

abstract
  down-× : ∀{A}{P Q : Predᵒ A}{k}
     → ↓ᵒ k (P ×ᵒ Q) ≡ᵖ ↓ᵒ k ((↓ᵒ k P) ×ᵒ (↓ᵒ k Q))
  down-× x zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-× x (suc i) =
      ⇔-intro
      (λ { (si<k , Pxsi , Qxsi) → si<k , ((si<k , Pxsi) , (si<k , Qxsi))})
      (λ { (si<k , (_ , Pxsi) , _ , Qxsi) → si<k , Pxsi , Qxsi})

continuous-× : ∀{A}{B}
    (F G : Fun A B Now)
   → continuous (λ P → (fun F) P ×ᵒ (fun G) P)
continuous-× {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵒ k (f P ×ᵒ g P)                                              ⩦⟨ down-× ⟩
    ↓ᵒ k (↓ᵒ k (f P) ×ᵒ ↓ᵒ k (g P))    ⩦⟨ cong-↓ (cong-×ᵖ (good F) (good G)) ⟩
    ↓ᵒ k (↓ᵒ k (f (↓ᵒ k P)) ×ᵒ ↓ᵒ k (g (↓ᵒ k P)))           ⩦⟨ ≡ᵖ-sym down-× ⟩
    ↓ᵒ k (f (↓ᵒ k P) ×ᵒ g (↓ᵒ k P))
    ∎

wellfounded-× : ∀{A}{B}
    (F G : Fun A B Later)
   → wellfounded (λ P → (fun F) P ×ᵒ (fun G) P)
wellfounded-× {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵒ (suc k) (f P ×ᵒ g P)                                       ⩦⟨ down-× ⟩
    ↓ᵒ (suc k) (↓ᵒ (suc k) (f P) ×ᵒ ↓ᵒ (suc k) (g P))
                                       ⩦⟨ cong-↓ (cong-×ᵖ (good F) (good G)) ⟩
    ↓ᵒ (suc k) (↓ᵒ (suc k) (f (↓ᵒ k P)) ×ᵒ ↓ᵒ (suc k) (g (↓ᵒ k P)))
                                                            ⩦⟨ ≡ᵖ-sym down-× ⟩
    ↓ᵒ (suc k) (f (↓ᵒ k P) ×ᵒ g (↓ᵒ k P))
    ∎

goodness-× : ∀ {kf kg : Kind} {A}{B}
    (F : Fun A B kf)
    (G : Fun A B kg)
   → goodness (choose kf kg) (λ P → (fun F) P ×ᵒ (fun G) P)
goodness-× {Now}{Now} F G = continuous-× F G 
goodness-× {Now}{Later} F G = continuous-× F (WF⇒C G)
goodness-× {Later}{Now} F G = continuous-× (WF⇒C F) G
goodness-× {Later}{Later} F G = wellfounded-× F G 

abstract
  cong-× : ∀{A}{B}{kf}{kg}
       (F : Fun A B kf)
       (G : Fun A B kg)
     → congᵖ (λ P → (fun F) P ×ᵒ (fun G) P)
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
  record { fun = λ P → (fun F) P ×ᵒ (fun G) P
         ; good = goodness-× F G
         ; congr = cong-× F G
         }

{------- Disjunction --------}

abstract
  down-⊎ : ∀{A}{P Q : Predᵒ A}{k}
     → ↓ᵒ k (P ⊎ᵒ Q) ≡ᵖ ↓ᵒ k ((↓ᵒ k P) ⊎ᵒ (↓ᵒ k Q))
  down-⊎ {A}{P}{Q} {k} x i = ⇔-intro (to i) (fro i)
    where
    to : ∀ i →  #(↓ᵒ k (P ⊎ᵒ Q) x) i → #(↓ᵒ k (↓ᵒ k P ⊎ᵒ ↓ᵒ k Q) x) i
    to zero _ = tt
    to (suc i) (si<k , inj₁ Psi) = si<k , (inj₁ (si<k , Psi))
    to (suc i) (si<k , inj₂ Qsi) = si<k , (inj₂ (si<k , Qsi))

    fro : ∀ i → #(↓ᵒ k (↓ᵒ k P ⊎ᵒ ↓ᵒ k Q) x) i → #(↓ᵒ k (P ⊎ᵒ Q) x) i
    fro zero x = tt
    fro (suc i) (si<k , inj₁ (_ , Psi)) = si<k , inj₁ Psi
    fro (suc i) (si<k , inj₂ (_ , Qsi)) = si<k , (inj₂ Qsi)
  
continuous-⊎ : ∀{A}{B}(F G : Fun A B Now)
   → continuous (λ P → (fun F) P ⊎ᵒ (fun G) P)
continuous-⊎ {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵒ k (f P ⊎ᵒ g P)                              ⩦⟨ down-⊎ ⟩
    ↓ᵒ k (↓ᵒ k (f P) ⊎ᵒ ↓ᵒ k (g P))     ⩦⟨ cong-↓ (cong-⊎ᵖ (good F) (good G)) ⟩
    ↓ᵒ k (↓ᵒ k (f (↓ᵒ k P)) ⊎ᵒ ↓ᵒ k (g (↓ᵒ k P)))           ⩦⟨ ≡ᵖ-sym down-⊎ ⟩
    ↓ᵒ k (f (↓ᵒ k P) ⊎ᵒ g (↓ᵒ k P))
    ∎

wellfounded-⊎ : ∀{A}{B}(F G : Fun A B Later)
   → wellfounded (λ P → (fun F) P ⊎ᵒ (fun G) P)
wellfounded-⊎ {A}{B} F G {P}{k} =
    let f = fun F in let g = fun G in
    ↓ᵒ (suc k) (f P ⊎ᵒ g P)                                       ⩦⟨ down-⊎ ⟩
    ↓ᵒ (suc k) (↓ᵒ (suc k) (f P) ⊎ᵒ ↓ᵒ (suc k) (g P))
                                        ⩦⟨ cong-↓ (cong-⊎ᵖ (good F) (good G)) ⟩
    ↓ᵒ (suc k) (↓ᵒ (suc k) (f (↓ᵒ k P)) ⊎ᵒ ↓ᵒ (suc k) (g (↓ᵒ k P)))
                                                             ⩦⟨ ≡ᵖ-sym down-⊎ ⟩
    ↓ᵒ (suc k) (f (↓ᵒ k P) ⊎ᵒ g (↓ᵒ k P))
    ∎

goodness-⊎ : ∀ {kf kg : Kind} {A}{B}
     (F : Fun A B kf)
     (G : Fun A B kg)
   → goodness (choose kf kg) (λ P → (fun F) P ⊎ᵒ (fun G) P)
goodness-⊎ {Now}{Now} F G = continuous-⊎ F G 
goodness-⊎ {Now}{Later} F G = continuous-⊎ F (WF⇒C G)
goodness-⊎ {Later}{Now} F G = continuous-⊎ (WF⇒C F) G
goodness-⊎ {Later}{Later} F G = wellfounded-⊎ F G

abstract
  cong-⊎ : ∀{A}{B}{kf}{kg}
       (F : Fun A B kf)
       (G : Fun A B kg)
     → congᵖ (λ P → (fun F) P ⊎ᵒ (fun G) P)
  cong-⊎ {A}{B} F G {P}{Q} PQ x i = ⇔-intro to fro
    where
    to : #(((fun F) P ⊎ᵒ (fun G) P) x) i → #(((fun F) Q ⊎ᵒ (fun G) Q) x) i
    to (inj₁ FPi) = inj₁ (⇔-to (congr F {P}{Q} PQ x i) FPi)
    to (inj₂ GPi) = inj₂ (⇔-to (congr G {P}{Q} PQ x i) GPi)

    fro : #(((fun F) Q ⊎ᵒ (fun G) Q) x) i → #(((fun F) P ⊎ᵒ (fun G) P) x) i
    fro (inj₁ FQi) = inj₁ (⇔-fro (congr F {P}{Q} PQ x i) FQi)
    fro (inj₂ GQi) = inj₂ (⇔-fro (congr G PQ x i) GQi)

infixr 6 _⊎ᶠ_
_⊎ᶠ_ : ∀{A}{B}{kF kG}
   → Fun A B kF
   → Fun A B kG
     ----------------------
   → Fun A B (choose kF kG)
_⊎ᶠ_ {A}{B}{kF}{kG} F G =
  record { fun = λ P → (fun F) P ⊎ᵒ (fun G) P
         ; good = goodness-⊎ F G
         ; congr = cong-⊎ F G
         }

{------- Forall --------}

abstract
  continuous-all : ∀{A B C}
     → (F : A → Fun B C Now)
     → continuous (λ P → ∀ᵒ[ a ] fun (F a) P)
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
                  (↓ₒ-intro (((fun (F v) (↓ᵒ k P)) x)) si<k (∀FP v) ) in
             proj₂ ↓FP)})

  wellfounded-all : ∀{A B C}
     → (F : A → Fun B C Later)
     → wellfounded (λ P → ∀ᵒ[ a ] fun (F a) P)
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
                          (↓ₒ-intro ((fun (F v) (↓ᵒ k P)) x) i≤k (∀F↓P v))
                   in proj₂ ↓FP)})

goodness-all : ∀{A B C}{K}
   → (F : A → Fun B C K)
   → goodness K (λ P → ∀ᵒ[ a ] fun (F a) P)
goodness-all {A} {B} {C} {Now} F = continuous-all F
goodness-all {A} {B} {C} {Later} F = wellfounded-all F

abstract
  cong-all : ∀{A B C}{K}
     → (F : A → Fun B C K)
     → congᵖ (λ P → ∀ᵒ[ a ] fun (F a) P)
  cong-all F {P}{Q} PQ c i =
    ⇔-intro
    (λ ∀FP v → ⇔-to (congr (F v) PQ c i) (∀FP v))
    (λ ∀FQ v → ⇔-fro (congr (F v) PQ c i) (∀FQ v))

∀ᶠ : ∀{A B C : Set}{K}
   → (A → Fun B C K)
     ---------------
   → Fun B C K
∀ᶠ {A}{B}{C}{K} F =
  record { fun = λ P → ∀ᵒ[ a ] fun (F a) P
         ; good = goodness-all F
         ; congr = cong-all F
         }
  
∀ᶠ-syntax = ∀ᶠ
infix 1 ∀ᶠ-syntax
syntax ∀ᶠ-syntax (λ x → F) = ∀ᶠ[ x ] F

{------- Exists --------}

abstract
  continuous-exist : ∀{A B C}{{_ : Inhabited A}}
     → (F : A → Fun B C Now)
     → continuous (λ P → ∃ᵒ[ a ] fun (F a) P)
  continuous-exist F c zero = (λ x → tt) , (λ x → tt)
  continuous-exist F {P} {zero} c (suc i) = (λ {(() , _)}) , λ {(() , _)}
  continuous-exist F {P} {suc k} c (suc i) =
      (λ (si<sk , (a , FPa)) →
          let ↓F↓P = ⇔-to (good (F a) c (suc i)) (si<sk , FPa) in
          si<sk , (a , proj₂ ↓F↓P))
      ,
      (λ (si<sk , (a , FPa)) →
          let ↓FP = ⇔-fro (good (F a) c (suc i)) (si<sk , FPa) in
          si<sk , (a , proj₂ ↓FP))

  wellfounded-exist : ∀{A B C}{{_ : Inhabited A}}
     → (F : A → Fun B C Later)
     → wellfounded (λ P → ∃ᵒ[ a ] fun (F a) P)
  wellfounded-exist F {P} {k} c zero = (λ x → tt) , (λ x → tt)
  wellfounded-exist F {P} {k} c (suc i) =
      (λ {(s≤s i<k , (a , FPa)) →
          let ↓F↓P = ⇔-to (good (F a) c (suc i)) (s≤s i<k , FPa) in
          (s≤s i<k) , (a , proj₂ ↓F↓P)})
      ,
      (λ {(s≤s i<k , (a , FPa)) →
          let ↓FP = ⇔-fro (good (F a) c (suc i)) (s≤s i<k , FPa) in
          (s≤s i<k) , (a , proj₂ ↓FP)})

goodness-exist : ∀{A B C}{K}{{_ : Inhabited A}}
   → (F : A → Fun B C K)
   → goodness K (λ P → ∃ᵒ[ a ] fun (F a) P)
goodness-exist {A} {B} {C} {Now} F = continuous-exist F
goodness-exist {A} {B} {C} {Later} F = wellfounded-exist F

abstract
  cong-exist : ∀{A B C}{K}{{_ : Inhabited A}}
     → (F : A → Fun B C K)
     → congᵖ (λ P → ∃ᵒ[ a ] fun (F a) P)
  cong-exist F {P}{Q} PQ c i =
      (λ {(a , Fa) → a , ⇔-to (congr (F a) PQ c i) Fa})
      ,
      (λ {(a , Fa) → a , ⇔-fro (congr (F a) PQ c i) Fa})
     
∃ᶠ : ∀{A B C : Set}{K}{{_ : Inhabited A}}
   → (A → Fun B C K)
     ---------------
   → Fun B C K
∃ᶠ {A}{B}{C}{K} F =
  record { fun = λ P → ∃ᵒ[ a ] fun (F a) P
         ; good = goodness-exist F
         ; congr = cong-exist F
         }
  
∃ᶠ-syntax = ∃ᶠ
infix 1 ∃ᶠ-syntax
syntax ∃ᶠ-syntax (λ x → F) = ∃ᶠ[ x ] F


{------- Constant --------}

abstract
  wellfounded-const : ∀{A}{B} (S : Set) → wellfounded{A}{B} (λ P → S ᵒ)
  wellfounded-const S = λ v i → ⇔-intro (λ x → x) (λ x → x)

  cong-const : ∀{A}{B} (S : Set) → congᵖ{A}{B} (λ P → S ᵒ)
  cong-const S = λ _ v i → ⇔-intro (λ x → x) (λ x → x)

_ᶠ : ∀{A}{B}
   → Set
   → Fun A B Later
(S)ᶠ = record { fun = λ P → S ᵒ
              ; good = λ {P}{k} → wellfounded-const S {P}{k}
              ; congr = cong-const S
              }

{------- Later --------}

≤-inv : ∀{i}{j}
   → suc i ≤ suc j
   → i ≤ j
≤-inv (s≤s i≤j) = i≤j

abstract
  down-▷ : ∀{B}{k}(P : Predᵒ B) → ↓ᵒ (suc k) (▷ᵒ P) ≡ᵖ ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k P))
  down-▷ P v zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-▷ P v (suc zero) =
      ⇔-intro (λ {(a , b) → a , tt}) (λ {(a , b) → a , (tz (P v))})
  down-▷ P v (suc (suc i)) =
    ⇔-intro
    (λ {(s≤s i≤1+k , ▷Pvi) →
                 s≤s i≤1+k , i≤1+k , ▷Pvi})
    (λ {(i≤1+k , (_ , ▷Pvi)) → i≤1+k , ▷Pvi})

wellfounded-▷ : ∀{A}{B} (F : Fun A B Now)
   → wellfounded (λ P → ▷ᵒ ((fun F) P))
wellfounded-▷ {A}{B} F {P}{k} =
    let f = fun F in
    ↓ᵒ (suc k) (▷ᵒ (f P))                ⩦⟨ down-▷ (f P) ⟩
    ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k (f P)))         ⩦⟨ cong-↓ EQ2 ⟩
    ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k (f (↓ᵒ k P))))  ⩦⟨ ≡ᵖ-sym (down-▷ (f (↓ᵒ k P))) ⟩
    ↓ᵒ (suc k) (▷ᵒ (f (↓ᵒ k P)))
    ∎
  where
  EQ2 : ▷ᵒ (↓ᵒ k ((fun F) P)) ≡ᵖ ▷ᵒ (↓ᵒ k ((fun F) (↓ᵒ k P)))
  EQ2 = cong-▷ᵖ (good F)

goodness-▷ : ∀ {k : Kind}{A}{B} (F : Fun A B k)
  → wellfounded (λ P → ▷ᵒ ((fun F) P))
goodness-▷ {Now} F = wellfounded-▷ F
goodness-▷ {Later} F = wellfounded-▷ (WF⇒C F)

abstract
  cong-▷ : ∀{A}{B}{kf}
       (F : Fun A B kf)
     → congᵖ (λ P → ▷ᵒ ((fun F) P))
  cong-▷ F PQ x 0 = ⇔-intro (λ x → tt) (λ x → tt)
  cong-▷ F PQ x (suc i) =
      ⇔-intro
        (λ FPxi → ⇔-to (congr F PQ x i) FPxi)
        (λ FQxi → ⇔-fro (congr F PQ x i) FQxi)

▷ᶠ : ∀{A}{B}{kF}
   → Fun A B kF
     -------------------
   → Fun A B Later
▷ᶠ {A}{B}{kF} F = record { fun = (λ P → ▷ᵒ ((fun F) P))
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
  goodness-flip {A}{B}{C} {Now} F b {P}{k} x = good (F x) b
  goodness-flip {A}{B}{C} {Later} F b {P}{k} x = good (F x) b
    
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

recurᶠ : ∀{A}{B}
   → A
     ------------------
   → Fun A B Now
recurᶠ a =
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
     → (F : Fun A A Later)
     → ↓ᵒ k (μᵒ F) ≡ᵖ ↓ᵒ k (iter k (fun F) ⊤ᵒ)
  lemma18a zero F x zero = ⇔-intro (λ x → tt) (λ x → tt)
  lemma18a zero F x (suc i) = ⇔-intro (λ { (() , b)}) (λ { (() , b)})
  lemma18a (suc k′) F v zero = ⇔-intro (λ x → tt) (λ x → tt)
  lemma18a (suc k′) F v (suc j′) =
      let k = suc k′ in
      let j = suc j′ in
      #((↓ᵒ k (μᵒ F)) v) j
                                  ⩦⟨ ⇔-intro (λ { (j<k , μFvj) → j<k , μFvj})
                                              (λ {(j<k , μFvj) → j<k , μFvj}) ⟩
      (j < k  ×  (#((μᵒ F) v) j))             ⩦⟨ ⇔-intro (λ {(a , b) → a , b})
                                                         (λ {(a , b) → a , b}) ⟩
      (j < k  ×  #((iter (suc j) (fun F) ⊤ᵒ) v) j)
                                     ⩦⟨ ⇔-intro (λ {(a , b) → a , ≤-refl , b})
                                          (λ {(s≤s a , (b , c)) → s≤s a , c}) ⟩
      (j < k  ×  #((↓ᵒ (suc j) (iter (suc j) (fun F) ⊤ᵒ)) v) j)        ⩦⟨ EQ4 ⟩
      (j < k  ×  #((↓ᵒ (suc j) (iter k (fun F) ⊤ᵒ)) v) j)
                                    ⩦⟨ ⇔-intro (λ {(a , b) → a , (proj₂ b)})
                                             (λ {(a , b) → a , (≤-refl , b)}) ⟩
      (j < k  ×  #((iter k (fun F) ⊤ᵒ) v) j)
                                  ⩦⟨ ⇔-intro (λ {(a , b) → a , b}) (λ z → z) ⟩
      #((↓ᵒ k (iter k (fun F) ⊤ᵒ)) v) j
      ∎
      where
        k : ℕ
        k = suc k′
        j : ℕ
        j = suc j′
        EQ4 : (j < k  ×  #((↓ᵒ (suc j) (iter (suc j) (fun F) ⊤ᵒ)) v) j)
               ⇔ (j < k  ×  #((↓ᵒ (suc j) (iter k (fun F) ⊤ᵒ)) v) j)  
        EQ4 = ⇔-intro (λ{(s≤s j≤k′ , (j<1+j , FμF)) → s≤s j≤k′ ,
          let ↓FμF = ⇔-to (lemma15b ⊤ᵒ F (s≤s j≤k′) v (suc j′)) (j<1+j , FμF)
          in j<1+j , proj₂ ↓FμF})
         (λ{(s≤s j≤k′ , (j<1+j , FμF)) → s≤s j≤k′ ,
          let ↓FμF = ⇔-fro (lemma15b ⊤ᵒ F (s≤s j≤k′) v (suc j′)) (j<1+j , FμF)
          in  j<1+j , (proj₂ ↓FμF)
          })

lemma18b : ∀{A}
   → (k : ℕ)
   → (F : Fun A A Later)
   → ↓ᵒ (suc k) ((fun F) (μᵒ F)) ≡ᵖ ↓ᵒ (suc k) (iter (suc k) (fun F) ⊤ᵒ)
lemma18b {A} k F =
      ↓ᵒ (suc k) ((fun F) (μᵒ F))                         ⩦⟨ good F ⟩
      ↓ᵒ (suc k) ((fun F) (↓ᵒ k (μᵒ F)))
                                          ⩦⟨ cong-↓ (congr F (lemma18a k F)) ⟩
      ↓ᵒ (suc k) ((fun F) (↓ᵒ k (iter k (fun F) ⊤ᵒ)))     ⩦⟨ ≡ᵖ-sym (good F) ⟩
      ↓ᵒ (suc k) ((fun F) (iter k (fun F) ⊤ᵒ))            ⩦⟨ ≡ᵖ-refl refl ⟩
      ↓ᵒ (suc k) (iter (suc k) (fun F) ⊤ᵒ)
    ∎
    
lemma19 : ∀{A}
   → (k : ℕ)
   → (F : Fun A A Later)
   → ↓ᵒ k (μᵒ F) ≡ᵖ ↓ᵒ k ((fun F) (μᵒ F))
lemma19 {A} k F =
      ↓ᵒ k (μᵒ F)                                  ⩦⟨ lemma18a k F ⟩
      ↓ᵒ k (iter k (fun F) ⊤ᵒ)                     ⩦⟨ lemma15b _ F (n≤1+n k) ⟩
      ↓ᵒ k (iter (suc k) (fun F) ⊤ᵒ)               ⩦⟨ ≡ᵖ-sym lemma17 ⟩
      ↓ᵒ k (↓ᵒ (suc k) (iter (suc k) (fun F) ⊤ᵒ))
                                           ⩦⟨ cong-↓ (≡ᵖ-sym (lemma18b _ F)) ⟩
      ↓ᵒ k (↓ᵒ (suc k) ((fun F) (μᵒ F)))           ⩦⟨ lemma17 ⟩
      ↓ᵒ k ((fun F) (μᵒ F))
    ∎

abstract
  down-eq : ∀{A}{P : Predᵒ A}{x}
     → (i : ℕ)
     → (#((↓ᵒ (suc i) P) x) i) ⇔ (# (P x) i)
  down-eq {A}{P}{x} zero = ⇔-intro (λ _ → tz (P x)) (λ _ → tt)
  down-eq {A}{P}{x} (suc i′) =
      ⇔-intro (λ (i<1+i , Pxi) → Pxi) (λ Pxi → s≤s (s≤s ≤-refl) , Pxi)

abstract
  equiv-down : ∀{A}{P Q : Predᵒ A}
     → (∀ k → ↓ᵒ k P ≡ᵖ ↓ᵒ k Q)
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
   → (F : Fun A A Later)
   → μᵒ F ≡ᵖ (fun F) (μᵒ F)
fixpoint F = equiv-down (λ k → lemma19 k F)

{--------------- Make a Recursive Predicate -------------------}

RecSetᵒ : Set → Kind → Set₁
RecSetᵒ A κ = Fun A ⊤ κ

recursiveᵒ : ∀{A}
   → (A → RecSetᵒ A Later)
     ---------------------
   → Predᵒ A
recursiveᵒ F = μᵒ (flipᶠ F tt)

fixpointᵒ : ∀{A} (F : A → RecSetᵒ A Later) (a : A)
    → recursiveᵒ F a ≡ᵒ fun (F a) (recursiveᵒ F) tt
fixpointᵒ {A} F a =
  recursiveᵒ F a                             ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ (flipᶠ F tt) a                         ⩦⟨ apply-≡ᵖ (fixpoint (flipᶠ F tt)) a ⟩
  (fun (flipᶠ F tt)) (μᵒ (flipᶠ F tt)) a     ⩦⟨ ≡ᵒ-refl refl ⟩
  fun (F a) (recursiveᵒ F) tt                ∎


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
  monoᵒ : ∀ {𝓟}{P}
     → 𝓟 ⊢ᵒ P
       ------------
     → 𝓟 ⊢ᵒ (▷ᵒ P)
  monoᵒ {𝓟}{P} ⊢P zero ⊨𝓟n = tt
  monoᵒ {𝓟}{P} ⊢P (suc n) ⊨𝓟n =
    let ⊨𝓟n = downClosed-Πᵒ 𝓟 (suc n) ⊨𝓟n n (n≤1+n n) in
    ⊢P n ⊨𝓟n

  lobᵒ : ∀ {𝓟}{P}
     → (▷ᵒ P) ∷ 𝓟 ⊢ᵒ P
       -----------------------
     → 𝓟 ⊢ᵒ P
  lobᵒ {𝓟}{P} step zero ⊨𝓟n = tz P
  lobᵒ {𝓟}{P} step (suc n) ⊨𝓟sn =
    let ⊨𝓟n = downClosed-Πᵒ 𝓟 (suc n) ⊨𝓟sn n (n≤1+n n) in
    let Pn = lobᵒ {𝓟}{P} step n ⊨𝓟n in
    step (suc n) (Pn , ⊨𝓟sn)

  ▷× : ∀{𝓟} {P Q : Setᵒ}
     → 𝓟 ⊢ᵒ (▷ᵒ (P ×ᵒ Q))
       ----------------------
     → 𝓟 ⊢ᵒ (▷ᵒ P) ×ᵒ (▷ᵒ Q)
  ▷× ▷P×Q zero = λ _ → tt , tt
  ▷× ▷P×Q (suc n) = ▷P×Q (suc n)

  ▷⊎ : ∀{𝓟}{P Q : Setᵒ}
     → 𝓟 ⊢ᵒ (▷ᵒ (P ⊎ᵒ Q))
       ----------------------
     → 𝓟 ⊢ᵒ (▷ᵒ P) ⊎ᵒ (▷ᵒ Q)
  ▷⊎ ▷P⊎Q zero = λ _ → inj₁ tt
  ▷⊎ ▷P⊎Q (suc n) = ▷P⊎Q (suc n) 

  ▷→ : ∀{𝓟}{P Q : Setᵒ}
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

⊢ᵒ-unfold : ∀ {A}{𝓟}{F : Fun A A Later}{a : A}
  → 𝓟 ⊢ᵒ (μᵒ F) a
    ------------------------------
  → 𝓟 ⊢ᵒ ((fun F) (μᵒ F)) a
⊢ᵒ-unfold {A}{𝓟}{F}{a} ⊢μa =
    ≡ᵖ⇒⊢ᵒ 𝓟 (μᵒ F) ((fun F) (μᵒ F)) ⊢μa (fixpoint F)

⊢ᵒ-fold : ∀ {A}{𝓟}{F : Fun A A Later}{a : A}
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
    → 𝓟 ⊢ᵒ P ⊎ᵒ (Q ⊎ᵒ R)
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
  ▷→▷ : ∀{𝓟}{P Q : Setᵒ}
     → 𝓟 ⊢ᵒ ▷ᵒ P
     → 𝓟 ⊢ᵒ P →ᵒ Q
       ------------
     → 𝓟 ⊢ᵒ ▷ᵒ Q
  ▷→▷ {𝓟}{P}{Q} ▷P P→Q n ⊨𝓟n =
    let ▷Q = appᵒ{𝓟}{▷ᵒ P}{▷ᵒ Q}
                (▷→{𝓟}{P}{Q}
                    (monoᵒ{𝓟}{P →ᵒ Q} P→Q)) ▷P in
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
  ⊢ᵒ-∃-intro : ∀{𝓟 : List Setᵒ }{A}{P : A → Setᵒ}{{_ : Inhabited A}}
    → (a : A)
    → 𝓟 ⊢ᵒ P a
      ----------
    → 𝓟 ⊢ᵒ ∃ᵒ P
  ⊢ᵒ-∃-intro a ⊢Pa n ⊨𝓟n = a , (⊢Pa n ⊨𝓟n)

  ⊢ᵒ-∃-elim : ∀{𝓟 : List Setᵒ }{A}{P : A → Setᵒ}{R : Setᵒ}{{_ : Inhabited A}}
    → 𝓟 ⊢ᵒ ∃ᵒ P
    → (∀ a → P a ∷ 𝓟 ⊢ᵒ R)
      ---------------------
    → 𝓟 ⊢ᵒ R
  ⊢ᵒ-∃-elim{R = R} ⊢∃P cont zero ⊨𝒫n = tz R
  ⊢ᵒ-∃-elim ⊢∃P cont (suc n) ⊨𝒫n
      with ⊢∃P (suc n) ⊨𝒫n
  ... | (a , Pasn) = cont a (suc n) (Pasn , ⊨𝒫n)

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
  constᵒI : ∀{𝓟}{S : Set}
     → S
     → 𝓟 ⊢ᵒ (S)ᵒ
  constᵒI s zero ⊨𝓟n = tt
  constᵒI s (suc n) ⊨𝓟n = s

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

