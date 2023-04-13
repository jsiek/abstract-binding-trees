{-# OPTIONS --without-K --rewriting #-}

{-
 Authors: Siek, Thiemann, and Wadler

 Based on "Logical Step-Indexed Logical Relations"
 by Dreyer, Ahmed, and Birkedal.

 Based on the Agda development of Logical Step-Indexed Logical Relations
 by Philip Wadler (June 1, 2022)

 The proof of the fixpoint theorem is based on "An Indexed Model of
 Recursive Types" by Appel and McAllester.

-}
module rewriting.examples.StepIndexedLogic2 where

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
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import Level using (Lift)

open import rewriting.examples.EquivalenceRelation public

Setₒ : Set₁
Setₒ = ℕ → Set

downClosed : Setₒ → Set
downClosed S = ∀ n → S n → ∀ k → k ≤ n → S k

Predₒ : Set → Set₁
Predₒ A = A → Setₒ

-- downClosedᵖ : ∀{A} → Predₒ A → Set
-- downClosedᵖ P = ∀ a → downClosed (P a)

-- trueZeroᵖ : ∀{A} → Predₒ A → Set
-- trueZeroᵖ P = ∀ a → (P a) 0

Context : Set₁
Context = List Set

-- Preds : Context → Set₁
-- Preds [] = topᵖ 
-- Preds (A ∷ Γ) = (A → ℕ → Set) × Preds Γ

-- downClosedᵖs : ∀{Γ} → Preds Γ → Set
-- downClosedᵖs {[]} μs = ⊤
-- downClosedᵖs {A ∷ Γ} (μP , μs) = (downClosedᵖ μP) × (downClosedᵖs μs)

-- trueZeroᵖs : ∀{Γ} → Preds Γ → Set
-- trueZeroᵖs {[]} μs = ⊤
-- trueZeroᵖs {A ∷ Γ} (μP , μs) = (trueZeroᵖ μP) × (trueZeroᵖs μs)

-- record Predsᵒ (Γ : Context) : Set₁ where
--   field
--     preds : Preds Γ
--     dc : downClosedᵖs preds
--     tz : trueZeroᵖs preds

-- SISet : Context → Set₁
-- SISet Γ = Predsᵒ Γ → Setₒ

-- downClosedᵒ : ∀{Γ} → SISet Γ → Set₁
-- downClosedᵒ {Γ} S = ∀ (μs : Predsᵒ Γ) → downClosed (S μs)

-- trueZeroᵒ : ∀{Γ} → SISet Γ → Set₁
-- trueZeroᵒ {Γ} S = ∀ (μs : Predsᵒ Γ) → (S μs) 0

data Time : Set where
  Now : Time
  Later : Time

-- Phil: would prefer if this were a list
data Times : Context → Set₁ where
  ∅ : Times []
  cons : ∀{Γ}{A} → Time → Times Γ → Times (A ∷ Γ)

↓ : ℕ → Setₒ → Setₒ
-- Phil: let's switch to the following
-- ↓ k S j = j ≤ k  ×  S j
↓ k S zero = ⊤
↓ k S (suc j) = suc j < k × (S (suc j))

--↓ᵖ : ℕ → ∀{A : Set} → Predₒ A → Predₒ A
--↓ᵖ k P a = ↓ k (P a)

record Setᵒ : Set₁ where
  field
    # : Setₒ
    down : downClosed #
    tz : # 0
open Setᵒ public

Predᵒ : Set → Set₁
Predᵒ A = A → Setᵒ

abstract
  infix 2 _≡ᵒ_
  _≡ᵒ_ : Setᵒ → Setᵒ → Set
  S ≡ᵒ T = ∀ k → # S k ⇔ # T k

  ≡ᵒ⇒⇔ : ∀{S T : Setᵒ}{k}
     → S ≡ᵒ T
     → # S k ⇔ # T k
  ≡ᵒ⇒⇔ {S}{T}{k} eq = eq k

  ≡ᵒ-intro : ∀{P Q : Setᵒ}
    → (∀ k → # P k ⇔ # Q k)
      ---------------------
    → P ≡ᵒ Q
  ≡ᵒ-intro P⇔Q k = P⇔Q k

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

≡ᵖ-refl : ∀{A}{P Q : Predᵒ A}
  → P ≡ Q
  → ∀ {a} → P a ≡ᵒ Q a
≡ᵖ-refl refl {a} = ≡ᵒ-refl refl

≡ᵖ-sym : ∀{A}{P Q : Predᵒ A}
  → (∀ {a} → P a ≡ᵒ Q a)
  → ∀ {a} → Q a ≡ᵒ P a
≡ᵖ-sym P=Q {a} = ≡ᵒ-sym P=Q

infixr 7 _×ᵒ_
infixr 7 _⊎ᵒ_
infixr 6 _→ᵒ_
infixr 8 _ᵒ

⊥ᵒ : Setᵒ
⊥ᵒ = record { # = λ { zero → ⊤ ; (suc k) → ⊥}
            ; down = λ { zero x .zero z≤n → tt}
            ; tz = tt
            }

⊤ᵒ : Setᵒ
⊤ᵒ = record { # = λ k → ⊤
            ; down = λ n _ k _ → tt
            ; tz = tt
            }

⊤ᵖ : ∀{A} → Predᵒ A
⊤ᵖ = (λ a → ⊤ᵒ)

_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ×ᵒ Q = record { # = λ k → # P k × # Q k
                ; down = λ k (Pk , Qk) j j≤k →
                          (down P k Pk j j≤k) , (down Q k Qk j j≤k)
                ; tz = (tz P) , (tz Q)
                }
                
_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ⊎ᵒ Q = record { # = λ k → # P k ⊎ # Q k
                ; down = λ { k (inj₁ Pk) j j≤k → inj₁ (down P k Pk j j≤k)
                           ; k (inj₂ Qk) j j≤k → inj₂ (down Q k Qk j j≤k)}
                ; tz = inj₁ (tz P)
                }

_→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P →ᵒ Q = record { # = λ k → ∀ j → j ≤ k → # P j → # Q j
                ; down = λ k P→Q j j≤k i i≤j Pi → P→Q i (≤-trans i≤j j≤k) Pi
                ; tz = λ { .zero z≤n _ → tz Q}
                }

∀ᵒ : ∀{A : Set} → Predᵒ A → Setᵒ
∀ᵒ{A} P = record { # = λ k → ∀ (a : A) → # (P a) k
                   ; down = λ n ∀Pn k k≤n a → down (P a) n (∀Pn a) k k≤n
                   ; tz = λ a → tz (P a) }

∀ᵒ-syntax = ∀ᵒ
infix 1 ∀ᵒ-syntax
syntax ∀ᵒ-syntax (λ x → P) = ∀ᵒ[ x ] P

record Inhabited (A : Set) : Set where
  field
    elt : A
open Inhabited {{...}} public

∃ᵒ : ∀{A : Set}{{_ : Inhabited A}} → Predᵒ A → Setᵒ
∃ᵒ{A} P = record { # = λ k → Σ[ a ∈ A ] # (P a) k
                     ; down = λ n (a , Pa) k k≤n → a , (down (P a) n Pa k k≤n)
                     ; tz = elt , tz (P elt)
                     }

∃ᵒ-syntax = ∃ᵒ
infix 1 ∃ᵒ-syntax
syntax ∃ᵒ-syntax (λ x → P) = ∃ᵒ[ x ] P

_ᵒ : Set → Setᵒ
S ᵒ = record { # = λ { zero → ⊤ ; (suc k) → S }
             ; down = λ { k Sk zero j≤k → tt
                        ; (suc k) Sk (suc j) j≤k → Sk}
             ; tz = tt
             }

▷ᵒ : Setᵒ → Setᵒ
▷ᵒ P = record
             { # = λ { zero → ⊤ ; (suc k) → # P k }
             ; down = λ { zero ▷Pn .zero z≤n → tt
                        ; (suc n) ▷Pn .zero z≤n → tt
                        ; (suc n) ▷Pn (suc k) (s≤s k≤n) → down P n ▷Pn k k≤n}
             ; tz = tt
             }

↓ᵒ : ℕ → Setᵒ → Setᵒ
↓ᵒ k S = record { # = ↓ k (# S)
                ; down = λ { zero x .zero z≤n → tt
                           ; (suc n) (sn<k , Sn) zero j≤n → tt
                           ; (suc n) (sn<k , Ssn) (suc j) (s≤s j≤n) →
                           (≤-trans (s≤s (s≤s j≤n)) sn<k)
                           , (down S (suc n) Ssn (suc j) (s≤s j≤n))}
                ; tz = tt
                }

{-
Product : ∀{ℓ} → List (Set ℓ) → (Set ℓ)
Product [] = topᵖ
Product (x ∷ xs) = x × Product xs

Productᵒ  : Context → Set₁
Productᵒ Γ = Product (Data.List.map (Function.const Setᵒ) Γ)

Predsᵒ : Context → Set₁
Predsᵒ Γ = Product Γ → Productᵒ Γ

↓ʲ : Time → ℕ → Setᵒ → Setᵒ
↓ʲ Now k S = ↓ᵒ k S
↓ʲ Later zero S = ⊥ᵒ 
↓ʲ Later (suc k) S = ↓ᵒ k S

⇓ : ∀{Γ} → Times Γ → ℕ → Productᵒ Γ → Productᵒ Γ
⇓ {[]} ts k γ = ttᵖ
⇓ {A ∷ Γ} (cons t ts) k (a , γ) = (↓ʲ t k a) , (⇓ ts k γ)

⇓ᵖ : ∀{Γ} → Times Γ → ℕ → Predsᵒ Γ → Predsᵒ Γ
⇓ᵖ ts k δ γ = ⇓ ts k (δ γ)

-- This is the simultaneous version. We may instead need
-- it to only talk about one variable at a time.
goodness : {Γ : Context} → Times Γ → (Predsᵒ Γ → Setᵒ) → Set₁
goodness {Γ} ts S = ∀{δ k} → ↓ᵒ k (S δ) ≡ᵒ ↓ᵒ k (S (⇓ᵖ ts k δ))  

-}

Predsᵒ : Context → Set₁
Predsᵒ [] = topᵖ 
Predsᵒ (A ∷ Γ) = (Predᵒ A) × Predsᵒ Γ

↓ᵖ : ℕ → ∀{A} → Predᵒ A → Predᵒ A
↓ᵖ j P a = ↓ᵒ j (P a)

{-
  Variable refering to a recursive predicate (from a μˢ)
-}
data _∋_ : Context → Set → Set₁ where
  zeroˢ : ∀{Γ}{A} → (A ∷ Γ) ∋ A
  sucˢ : ∀{Γ}{A}{B} → Γ ∋ B → (A ∷ Γ) ∋ B

continuousˢ : ∀{Γ}{A} (S : Predsᵒ (A ∷ Γ) → Setᵒ) (δ : Predsᵒ Γ) → Set₁
continuousˢ{Γ}{A} S δ =
  ∀ P k → ↓ᵒ k (S (P , δ)) ≡ᵒ ↓ᵒ k (S ((↓ᵖ k P) , δ))

wellfoundedˢ : ∀{Γ}{A} (S : Predsᵒ (A ∷ Γ) → Setᵒ) (δ : Predsᵒ Γ) → Set₁
wellfoundedˢ{Γ}{A} S δ =
  ∀ P k → ↓ᵒ (suc k) (S (P , δ)) ≡ᵒ ↓ᵒ (suc k) (S ((↓ᵖ k P) , δ))

↓ᵈ : ℕ → ∀{Γ}{A} → Γ ∋ A → Predsᵒ Γ → Predsᵒ Γ
↓ᵈ k {A ∷ Γ} {.A} zeroˢ (P , δ) = ↓ᵖ k P , δ
↓ᵈ k {A ∷ Γ} {B} (sucˢ x) (P , δ) = P , ↓ᵈ k x δ

timeof : ∀{Γ}{A} → (x : Γ ∋ A) → Times Γ → Time
timeof {B ∷ Γ} zeroˢ (cons t ts) = t
timeof {B ∷ Γ} (sucˢ x) (cons t ts) = timeof x ts

good-one : ∀{Γ}{A} → (x : Γ ∋ A) → Time → (Predsᵒ Γ → Setᵒ) → Set₁
good-one {Γ}{A} x Now S =
    ∀ δ j k → k ≤ j → ↓ᵒ k (S δ) ≡ᵒ ↓ᵒ k (S (↓ᵈ j x δ))
good-one {Γ}{A} x Later S =
    ∀ δ j k → k ≤ j → ↓ᵒ (suc k) (S δ) ≡ᵒ ↓ᵒ (suc k) (S (↓ᵈ j x δ))

good-now : ∀{Γ}{A}{x : Γ ∋ A}{ts : Times Γ}{S : Predsᵒ Γ → Setᵒ}
   → good-one x (timeof x ts) S
   → timeof x ts ≡ Now
   → ∀ δ j k → k ≤ j → ↓ᵒ k (S δ) ≡ᵒ ↓ᵒ k (S (↓ᵈ j x δ))
good-now gS eq rewrite eq = gS

good-later : ∀{Γ}{A}{x : Γ ∋ A}{ts : Times Γ}{S : Predsᵒ Γ → Setᵒ}
   → good-one x (timeof x ts) S
   → timeof x ts ≡ Later
   → ∀ δ j k → k ≤ j → ↓ᵒ (suc k) (S δ) ≡ᵒ ↓ᵒ (suc k) (S (↓ᵈ j x δ))
good-later gS eq rewrite eq = gS

goodnesses : ∀{Γ} → Times Γ → (Predsᵒ Γ → Setᵒ) → Set₁
goodnesses {Γ} ts S = ∀{A} (x : Γ ∋ A) → good-one x (timeof x ts) S

goodness : ∀{Γ} → Times Γ → (Predsᵒ Γ → Setᵒ) → Set₁
goodness {[]} ts S = topᵖ
goodness {A ∷ Γ} (cons Now ts) S = ∀ δ → continuousˢ S δ
goodness {A ∷ Γ} (cons Later ts) S = ∀ δ → wellfoundedˢ S δ

g⇒g : ∀{Γ}{ts : Times Γ}{S : Predsᵒ Γ → Setᵒ}
   → goodnesses ts S
   → goodness ts S
g⇒g {[]} {ts} {S} gs = ttᵖ
g⇒g {A ∷ Γ} {cons Now ts} {S} gs δ P k = gs zeroˢ (P , δ) k k ≤-refl
g⇒g {A ∷ Γ} {cons Later ts} {S} gs δ P k = gs zeroˢ (P , δ) k k ≤-refl

_≡ᵈ_ : ∀{Γ} → Predsᵒ Γ → Predsᵒ Γ → Set
_≡ᵈ_ {[]} δ δ′ = ⊤
_≡ᵈ_ {A ∷ Γ} (P , δ) (Q , δ′) = (∀ a → P a ≡ᵒ Q a) × δ ≡ᵈ δ′

≡ᵈ-refl : ∀{Γ}{δ : Predsᵒ Γ}
   → δ ≡ᵈ δ
≡ᵈ-refl {[]} {δ} = tt
≡ᵈ-refl {A ∷ Γ} {(P , δ)} = (λ a → ≡ᵒ-refl refl) , ≡ᵈ-refl

congruent : ∀{Γ : Context} → (Predsᵒ Γ → Setᵒ) → Set₁
congruent S = ∀{δ δ′} → δ ≡ᵈ δ′ → (S δ) ≡ᵒ (S δ′)

cong-head : ∀{Γ : Context} → (Predsᵒ Γ → Setᵒ) → Set₁
cong-head {[]} S = topᵖ
cong-head {A ∷ Γ} S =
  ∀{P Q} → (∀ a → P a ≡ᵒ Q a) → (∀ δ → S (P , δ) ≡ᵒ S (Q , δ))

cong⇒head : ∀{Γ : Context}{S : Predsᵒ Γ → Setᵒ}
  → congruent S
  → cong-head S
cong⇒head {[]} {S} congS′ = ttᵖ
cong⇒head {A ∷ Γ} {S} congS′ P=Q δ = congS′ (P=Q , ≡ᵈ-refl{Γ}{δ})

record Setˢ (Γ : Context) (ts : Times Γ) : Set₁ where
  field
    # : Predsᵒ Γ → Setᵒ 
    good : goodnesses ts #
    congr : congruent #
open Setˢ public

abstract
  infix 2 _≡ˢ_
  _≡ˢ_ : ∀{Γ}{ts : Times Γ} → Setˢ Γ ts → Setˢ Γ ts → Set₁
  S ≡ˢ T = ∀ δ → # S δ ≡ᵒ # T δ

  ≡ˢ-intro : ∀{Γ}{ts : Times Γ}{S T : Setˢ Γ ts}
    → (∀ δ → # S δ ≡ᵒ # T δ)
      ---------------------
    → S ≡ˢ T
  ≡ˢ-intro S=T eq δ = S=T eq δ

  ≡ˢ-refl : ∀{Γ}{ts : Times Γ}{S T : Setˢ Γ ts}
    → S ≡ T
    → S ≡ˢ T
  ≡ˢ-refl{S = S}{T} refl δ = ≡ᵒ-refl{# S δ}{# T δ} refl

  ≡ˢ-sym : ∀{Γ}{ts : Times Γ}{S T : Setˢ Γ ts}
    → S ≡ˢ T
    → T ≡ˢ S
  ≡ˢ-sym{S = S}{T} ST δ = ≡ᵒ-sym{# S δ}{# T δ} (ST δ)

  ≡ˢ-trans : ∀{Γ}{ts : Times Γ}{S T R : Setˢ Γ ts}
    → S ≡ˢ T
    → T ≡ˢ R
    → S ≡ˢ R
  ≡ˢ-trans{S = S}{T}{R} ST TR δ = ≡ᵒ-trans{# S δ}{# T δ}{# R δ} (ST δ) (TR δ)
  
instance
  SIL-Eqˢ : ∀{Γ}{ts : Times Γ} → EquivalenceRelation (Setˢ Γ ts)
  SIL-Eqˢ = record { _⩦_ = _≡ˢ_ ; ⩦-refl = ≡ˢ-refl
                   ; ⩦-sym = ≡ˢ-sym ; ⩦-trans = ≡ˢ-trans }

later : ∀{Γ} (ts : Times Γ) → Times Γ
later {[]} ts = ∅
later {A ∷ Γ} (cons t ts) = cons Later (later ts)

▷ˢ : ∀{Γ}{ts : Times Γ}
   → Setˢ Γ ts
     -----------------
   → Setˢ Γ (later ts)
▷ˢ S = record { # = λ δ → ▷ᵒ (# S δ) ; good = {!!} ; congr = {!!} }

{- Lemma's needed for defining recursive predicates -}

congᵖ : ∀{A}{B} (F : Predᵒ A → Predᵒ B) → Set₁
congᵖ F = ∀ {P Q} → (∀ a → P a ≡ᵒ Q a) → ∀ b → (F P b) ≡ᵒ (F Q b)

abstract
  cong-↓ : ∀{A}{k : ℕ}
     → congᵖ{A}{A} (↓ᵖ k)
  cong-↓ {A} {k} {P} {Q} eq a zero =
     (λ _ → tt) , λ _ → tt
  cong-↓ {A} {k} {P} {Q} eq a (suc i) =
     (λ {(si≤k , Pasi) → si≤k , (proj₁ (eq a (suc i)) Pasi)})
     ,
     λ {(si≤k , Qasi) → si≤k , (proj₂ (eq a (suc i)) Qasi)}

iter : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → (A → A)
iter zero    F  =  id
iter (suc n) F  =  F ∘ iter n F

iter-subtract : ∀{ℓ}{A : Set ℓ}{P : A}
  → (F : A → A)
  → (j k : ℕ)
  → j ≤ k
  → (iter j F (iter (k ∸ j) F P)) ≡ (iter k F P)
iter-subtract {A = A} {P} F .zero k z≤n = refl
iter-subtract {A = A} {P} F (suc j) (suc k) (s≤s j≤k)
  rewrite iter-subtract{A = A}{P} F j k j≤k = refl

toFun : ∀{Γ}{ts : Times Γ}{A}
   → Predsᵒ Γ
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
     ----------------------------------
   → (Predᵒ A → Predᵒ A)
toFun δ P μP = λ a → # (P a) (μP , δ)

abstract 
  ↓ᵒ-zero : ∀{A}{P Q : Predᵒ A} (a : A) → ↓ᵒ zero (P a) ≡ᵒ ↓ᵒ zero (Q a)
  ↓ᵒ-zero{A}{P}{Q} a zero = (λ _ → tt) , λ _ → tt
  ↓ᵒ-zero{A}{P}{Q} a (suc i) = (λ {()}) , (λ {()})

lemma15a : ∀{Γ}{A}{ts : Times Γ}{P Q : Predᵒ A}{δ : Predsᵒ Γ}
  → (j : ℕ)
  → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
  → (a : A)
  → ↓ᵒ j (iter j (toFun δ F) P a) ≡ᵒ ↓ᵒ j (iter j (toFun δ F) Q a)
lemma15a {Γ}{A}{ts}{P}{Q}{δ} zero F a = ↓ᵒ-zero{_}{P}{Q} a
lemma15a {Γ}{A}{ts}{P}{Q}{δ} (suc j) F a =
  let f = toFun δ F in
  let S = # (F a) in
  ↓ᵒ (suc j) (f (iter j f P) a)         ⩦⟨ g⇒g (good (F a)) δ (iter j f P) j ⟩ 
  ↓ᵒ (suc j) (f (↓ᵖ j (iter j f P)) a)
                   ⩦⟨ cong-↓ (λ a → (cong⇒head (congr (F a)))
                                      (λ a → lemma15a j F a) δ) a ⟩
  ↓ᵒ (suc j) (f (↓ᵖ j (iter j f Q)) a)
                               ⩦⟨ ≡ᵒ-sym (g⇒g (good (F a)) δ (iter j f Q) j) ⟩
  ↓ᵒ (suc j) (f (iter j f Q) a)
  ∎

lemma15b : ∀{Γ}{A}{ts : Times Γ}{P : Predᵒ A}{δ : Predsᵒ Γ}
  → (k : ℕ)
  → (j : ℕ)
  → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
  → (a : A)
  → j ≤ k
  → ↓ᵒ j (iter j (toFun δ F) P a) ≡ᵒ ↓ᵒ j (iter k (toFun δ F) P a)
lemma15b{Γ}{A}{ts}{P}{δ} k j F a j≤k =
  let f = toFun δ F in
  ↓ᵒ j (iter j f P a)                     ⩦⟨ lemma15a j F a ⟩
  ↓ᵒ j (iter j f (iter (k ∸ j) f P) a)
                      ⩦⟨ cong-↓{A}{j}{iter j f (iter (k ∸ j) f P)}{iter k f P}
                              (λ a → ≡ᵖ-refl (iter-subtract f j k j≤k)) a ⟩
  ↓ᵒ j (iter k f P a)   ∎

{- ↓ᵖ is idempotent -}
abstract
  lemma17 : ∀{A}{P : Predᵒ A}{k}{a : A}
     → ↓ᵖ k (↓ᵖ (suc k) P) a ≡ᵒ ↓ᵖ k P a
  lemma17 {A} {P} {k} {a} zero = (λ _ → tt) , (λ _ → tt)
  lemma17 {A} {P} {k} {a} (suc i) =
    (λ {(x , (y , z)) → x , z})
    ,
    λ {(x , y) → x , ((s≤s (<⇒≤ x)) , y)}

lemma17b : ∀{A}{P : Predᵒ A}{j}{k}{a : A}
   → suc j ≤′ k
   → ↓ᵖ j (↓ᵖ k P) a ≡ᵒ ↓ᵖ j P a
lemma17b {A} {P} {j} {.(suc j)} {a} _≤′_.≤′-refl = lemma17{A}{P}{j}{a}
lemma17b {A} {P} {j} {suc k} {a} (≤′-step j≤k) =
    ↓ᵖ j (↓ᵖ (suc k) P) a           ⩦⟨ ≡ᵒ-sym (lemma17b{A}{↓ᵖ (suc k) P} j≤k) ⟩
    ↓ᵖ j (↓ᵖ k (↓ᵖ (suc k) P)) a      ⩦⟨ E1 ⟩
    ↓ᵖ j (↓ᵖ k P) a                   ⩦⟨ lemma17b{A}{P}{j}{k}{a} j≤k ⟩ 
    ↓ᵖ j P a   ∎
    where
    E1 = cong-↓{A}{j}{(↓ᵖ k (↓ᵖ (suc k) P))}{(↓ᵖ k P)}
         (λ a → lemma17{A}{P}{k}{a}) a 

lemma17c : ∀{A}{P : Predᵒ A}{j}{k}{a : A}
   → j < k
   → ↓ᵖ j (↓ᵖ k P) a ≡ᵒ ↓ᵖ j P a
lemma17c {A} {P} {j} {k} {a} j<k = lemma17b{A}{P}{j}{k}{a} (≤⇒≤′ j<k)

abstract 
  lemma17d : ∀{A}{P : Predᵒ A}{k}{a : A}
       → ↓ᵖ k (↓ᵖ k P) a ≡ᵒ ↓ᵖ k P a
  lemma17d {A} {P} {k} {a} zero = (λ x → tt) , (λ x → tt)
  lemma17d {A} {P} {k} {a} (suc i) =
      (λ {(x , (y , z)) → y , z})
      ,
      λ {(x , y) → x , (x , y)}

lemma17e : ∀{A}{P : Predᵒ A}{j}{k}{a : A}
   → j ≤ k
   → ↓ᵖ j (↓ᵖ k P) a ≡ᵒ ↓ᵖ j P a
lemma17e {A} {P} {j} {k} {a} j≤k
    with ≤⇒≤′ j≤k
... | _≤′_.≤′-refl = lemma17d{A}{P}
... | ≤′-step j≤n = lemma17c{A}{P} (s≤s (≤′⇒≤ j≤n))

{-
Membership in a recursive predicate.
-}

lookup : ∀{Γ}{ts : Times Γ}{A} → Γ ∋ A → Predsᵒ Γ → Predᵒ A
lookup {B ∷ Γ} {ts} {.B} zeroˢ (P , δ) = P
lookup {B ∷ Γ} {cons t ts} {A} (sucˢ x) (P , δ) = lookup{Γ}{ts}{A} x δ

↓-lookup : ∀{Γ}{ts : Times Γ}{A}{B}{a}{k}{j}{δ : Predsᵒ Γ}
   → (x : Γ ∋ A)
   → (y : Γ ∋ B)
   → k ≤ j
   → ↓ᵒ k (lookup{Γ}{ts}{A} x δ a) ≡ᵒ ↓ᵒ k (lookup{Γ}{ts}{A} x (↓ᵈ j y δ) a)
↓-lookup {C ∷ Γ} {ts} {.C} {.C} {a} {k} {j} {P , δ} zeroˢ zeroˢ k≤j =
    ≡ᵒ-sym (lemma17e{_}{P}{k}{j}{a} k≤j)
↓-lookup {C ∷ Γ} {ts} {.C} {B} {a} {k} {j} {P , δ} zeroˢ (sucˢ y) k≤j =
    ≡ᵒ-refl refl
↓-lookup {C ∷ Γ} {cons t ts} {A} {.C} {a} {k} {j} {P , δ} (sucˢ x) zeroˢ k≤j =
   ≡ᵒ-refl refl
↓-lookup {C ∷ Γ} {cons t ts} {A}{B}{a}{k} {j} {P , δ} (sucˢ x) (sucˢ y) k≤j =
   ↓-lookup x y k≤j

lookup-diff : ∀{Γ}{ts : Times Γ}{A}{B}{δ : Predsᵒ Γ}{j}
   → (x : Γ ∋ A)
   → (y : Γ ∋ B)
   → timeof x ts ≢ timeof y ts
   → lookup{Γ}{ts}{A} x (↓ᵈ j y δ) ≡ lookup{Γ}{ts}{A} x δ
lookup-diff {C ∷ Γ} {cons t ts} zeroˢ zeroˢ neq = ⊥-elim (neq refl)
lookup-diff {C ∷ Γ} {cons t ts} zeroˢ (sucˢ y) neq = refl
lookup-diff {C ∷ Γ} {cons t ts} (sucˢ x) zeroˢ neq = refl
lookup-diff {C ∷ Γ} {cons t ts} (sucˢ x) (sucˢ y) neq = lookup-diff x y neq

timeof-diff : ∀{Γ}{ts : Times Γ}{A}{B} (x : Γ ∋ A) (y : Γ ∋ B)
   → timeof x ts ≡ Now → timeof y ts ≡ Later
   → timeof x ts ≢ timeof y ts
timeof-diff x y eq1 eq2 rewrite eq1 | eq2 = λ ()

good-lookup : ∀{Γ}{ts : Times Γ}{A}{a}
  → (x : Γ ∋ A)
  → timeof x ts ≡ Now
  → goodnesses ts (λ δ → lookup{Γ}{ts}{A} x δ a)
good-lookup {B ∷ Γ} {cons Now ts} {.B} zeroˢ time-x zeroˢ (P , δ) j k k≤j =
   ≡ᵒ-sym (lemma17e{_}{P} k≤j)
good-lookup {B ∷ Γ} {cons Now ts} {.B} zeroˢ time-x (sucˢ y) 
    with timeof y ts in eq
... | Now = λ{(P , δ) j k k≤j → ≡ᵒ-refl refl}
... | Later = λ{(P , δ) j k k≤j → ≡ᵒ-refl refl}
good-lookup {B ∷ Γ} {cons Now ts} {A} (sucˢ x) time-x zeroˢ (P , δ) j k k≤j =
    ≡ᵒ-refl refl
good-lookup {B ∷ Γ} {cons Later ts} {A} (sucˢ x) time-x zeroˢ (P , δ) j k k≤j =
    ≡ᵒ-refl refl
good-lookup {B ∷ Γ} {cons t ts} {A}{a} (sucˢ x) time-x (sucˢ y)
    with timeof y ts in eq-y
... | Now = λ{(P , δ) j k k≤j → ↓-lookup x y k≤j }
... | Later =
      λ{(P , δ) j k k≤j →
          let eq = (lookup-diff{Γ}{ts}{A}{_}{δ}{j} x y
                        (timeof-diff x y time-x eq-y)) in
          subst (λ X → ↓ᵒ (suc k) (lookup x δ a) ≡ᵒ ↓ᵒ (suc k) (X a))
                (sym eq) (≡ᵒ-refl refl)}

_∈_ : ∀{Γ}{ts : Times Γ}{A}
   → A
   → (x : Γ ∋ A)
   → {now : timeof x ts ≡ Now}
   → Setˢ Γ ts
(_∈_ {Γ}{ts}{A} a x) {now} =
  record { # = λ δ → (lookup{Γ}{ts}{A} x δ) a
         ; good = good-lookup x now
         ; congr = {!!}
         }

dc-iter : ∀(i : ℕ){A}
   → (F : Predᵒ A → Predᵒ A)
   → ∀ a → downClosed (#(iter i F ⊤ᵖ a))
dc-iter zero F = λ a n _ k _ → tt
dc-iter (suc i) F = λ a → down (F (iter i F ⊤ᵖ) a)

cong-iter : ∀{A}{a : A}
  → (i : ℕ)
  → (F G : Predᵒ A → Predᵒ A)
  → (∀ P Q a → (∀ b → P b ≡ᵒ Q b) → F P a ≡ᵒ G Q a)
  → (I : Predᵒ A)
  → iter i F I a ≡ᵒ iter i G I a
cong-iter zero F G F=G I = ≡ᵒ-refl refl
cong-iter{A}{a} (suc i) F G F=G I =
  let IH = λ b → cong-iter{A}{b} i F G F=G I in
  F=G (iter i F I) (iter i G I) a IH

μₒ : ∀{A} → (Predᵒ A → Predᵒ A) → A → Setₒ 
μₒ {A} F a k = #(iter{_}{Predᵒ A} (suc k) F ⊤ᵖ a) k

muˢ : ∀{Γ}{ts : Times Γ}{A}
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
   → Predsᵒ Γ
   → (A → Setᵒ)
muˢ {Γ}{ts}{A} P δ a =
  record { # = μₒ (toFun δ P) a
         ; down = dc
         ; tz = tz ((toFun δ P) ⊤ᵖ a)
         }
  where
  dc : downClosed (μₒ (toFun δ P) a)
  dc k iterskPk zero j≤k = tz (toFun δ P (id ⊤ᵖ) a)
  dc (suc k′) μPa (suc j′) (s≤s j′≤k′) =
    let f = toFun δ P in
    let dc-iter-ssk : downClosed (# ((iter (suc (suc k′)) f ⊤ᵖ) a))
        dc-iter-ssk = dc-iter (suc (suc k′)) (toFun δ P) a in
    let ↓-iter-ssk : #(↓ᵒ (suc (suc j′)) ((iter (suc (suc k′)) f ⊤ᵖ) a)) (suc j′)
        ↓-iter-ssk = ≤-refl , (dc-iter-ssk (suc k′) μPa (suc j′) (s≤s j′≤k′)) in
    let eq : ↓ᵒ (suc (suc j′)) ((iter (suc (suc j′)) (toFun δ P) ⊤ᵖ) a)
          ≡ᵒ ↓ᵒ (suc (suc j′)) ((iter (suc (suc k′)) (toFun δ P) ⊤ᵖ) a)
        eq = lemma15b {P = ⊤ᵖ}{δ} (suc (suc k′)) (suc (suc j′)) P a (s≤s (s≤s j′≤k′)) in
    let ↓-iter-ssj : #(↓ᵒ (suc (suc j′)) ((iter (suc (suc j′)) f ⊤ᵖ) a)) (suc j′)
        ↓-iter-ssj = ≡ᵒ-to (≡ᵒ-sym eq) (suc j′) ↓-iter-ssk in
    proj₂ ↓-iter-ssj

abstract
  lemma18a : ∀{Γ}{ts : Times Γ}{A}
     → (k : ℕ)
     → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
     → (a : A)
     → (δ : Predsᵒ Γ)
     → ↓ᵒ k (muˢ F δ a) ≡ᵒ ↓ᵒ k (iter k (toFun δ F) ⊤ᵖ a)
  lemma18a zero F a δ zero = (λ x → tt) , (λ {x → tt})
  lemma18a zero F a δ (suc j) = (λ {()}) , λ {()}
  lemma18a (suc k) F a δ zero = (λ {x → tt}) , λ {x → tt}
  lemma18a (suc k′) F a δ (suc j′) =
    let k = suc k′ in
    let j = suc j′ in 
    ↓ k (λ j₁ → # (toFun δ F (iter j₁ (toFun δ F) ⊤ᵖ) a) j₁) j
         ⩦⟨ ⩦-refl refl ⟩    
    j < k  ×  # (iter (suc j) (toFun δ F) ⊤ᵖ a) j
         ⩦⟨ (λ {(s≤s x , y) → s≤s x , ≤-refl , y})
            , (λ {(s≤s x , (y , z)) → (s≤s x) , z}) ⟩
    j < k  ×  # (↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)) j
         ⩦⟨ EQ  ⟩    
    j < k  ×  # (↓ᵒ (suc j) (iter k (toFun δ F) ⊤ᵖ a)) j
         ⩦⟨ (λ {(s≤s x , (s≤s y , z)) → (s≤s x) , z})
             , (λ {(x , y) → x , (≤-refl , y)})  ⟩
    j < k  ×  # (iter k (toFun δ F) ⊤ᵖ a) j
       ⩦⟨ ⩦-refl refl  ⟩    
    ↓ k (# (iter k (toFun δ F) ⊤ᵖ a)) j   ∎
    where
    k : ℕ
    k = suc k′
    j : ℕ
    j = suc j′
    EQ : (j < k  ×  # (↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)) j)
         ⇔ (j < k  ×  # (↓ᵒ (suc j) (iter k (toFun δ F) ⊤ᵖ a)) j)
    EQ =
      (λ {(s≤s x , y) →
        let xx = proj₁ ((lemma15b (suc k′) (suc j) F a (s≤s x)) j) y in
        (s≤s x) , (≤-refl , proj₂ xx)})
      ,
      λ {(s≤s x , (s≤s y , z)) →
        let xx = proj₂ ((lemma15b(suc k′)(suc j) F a (s≤s x)) j) (≤-refl , z) in
        s≤s x , (≤-refl , (proj₂ xx))}

lemma18b : ∀{Γ}{ts : Times Γ}{A}
     → (j : ℕ)
     → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
     → (a : A)
     → (δ : Predsᵒ Γ)
     → ↓ᵒ (suc j) (# (F a) (muˢ F δ , δ))
       ≡ᵒ ↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)
lemma18b{Γ}{ts}{A} j F a δ =
   ↓ᵒ (suc j) (# (F a) (muˢ F δ , δ))      ⩦⟨ g⇒g (good (F a)) δ (muˢ F δ) j ⟩
   ↓ᵒ (suc j) (# (F a) (↓ᵖ j (muˢ F δ) , δ))
                                     ⩦⟨ cong-↓ (λ a → cong⇒head (congr (F a))
                                               (λ a → lemma18a j F a δ ) δ) a ⟩
   ↓ᵒ (suc j) (# (F a) (↓ᵖ j (iter j (toFun δ F) ⊤ᵖ) , δ))
             ⩦⟨ ≡ᵖ-sym{A} (g⇒g (good (F a)) δ (iter j (toFun δ F) ⊤ᵖ) j) {a} ⟩
   ↓ᵒ (suc j) (# (F a) (iter j (toFun δ F) ⊤ᵖ , δ))           ⩦⟨ ≡ᵒ-refl refl ⟩
   ↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)     ∎
       
lemma19a : ∀{Γ}{ts : Times Γ}{A}
   (F : A → Setˢ (A ∷ Γ) (cons Later ts))
   (a : A)
   (j : ℕ)
   (δ : Predsᵒ Γ)
   → ↓ᵒ j (muˢ F δ a) ≡ᵒ ↓ᵒ j (# (F a) (muˢ F δ , δ))
lemma19a{Γ}{ts}{A} F a j δ = 
    ↓ᵒ j (muˢ F δ a)                                     ⩦⟨ lemma18a j F a δ  ⟩
    ↓ᵒ j (iter j (toFun δ F) ⊤ᵖ a)        ⩦⟨ lemma15b (suc j) j F a (n≤1+n j) ⟩
    ↓ᵒ j (iter (suc j) (toFun δ F) ⊤ᵖ a)
              ⩦⟨ ≡ᵖ-sym (lemma17{A}{(iter (suc j) (toFun δ F) ⊤ᵖ)}{j}{a}) {a} ⟩
    ↓ᵒ j (↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a))
                              ⩦⟨ cong-↓ (λ a → ≡ᵒ-sym (lemma18b j F a δ))  a  ⟩
    ↓ᵒ j (↓ᵒ (suc j) (# (F a) (muˢ F δ , δ)))
                         ⩦⟨ lemma17{A}{λ a → (# (F a) (muˢ F δ , δ))}{j}{a}  ⟩
    ↓ᵒ j (# (F a) (muˢ F δ , δ))                      ∎

{-
↓⇔ : ∀{j k : ℕ}{P Q : Setₒ}
   → (j < k → P j ⇔ Q j)
   → ↓ k P j ⇔ ↓ k Q j
↓⇔ {zero} {k} {P} {Q} imp = (λ x → tt) , (λ x → tt)
↓⇔ {suc j} {zero} {P} {Q} imp = (λ{()}) , (λ{()})
↓⇔ {suc j} {suc k} {P} {Q} imp =
    (λ {(x , y) → x , proj₁ (imp x) y})
     , (λ {(x , y) → x , (proj₂ (imp x) y)})
-}

good-now-mu : ∀{Γ}{ts : Times Γ}{A}{B}
   → (S : A → Setˢ (A ∷ Γ) (cons Later ts))
     (a : A) (x : Γ ∋ B)
   → timeof x ts ≡ Now
   → (δ : Predsᵒ Γ) (k j : ℕ)
   → (k ≤ j)
   → ↓ᵒ k (muˢ S δ a) ≡ᵒ ↓ᵒ k (muˢ S (↓ᵈ j x δ) a)
good-now-mu {Γ} {ts} {A} S a x time-x δ zero j k≤j =
    ↓ᵒ-zero{A}{muˢ S δ}{muˢ S (↓ᵈ _ x δ)} a
good-now-mu {Γ} {ts} {A} S a x time-x δ (suc k′) j k≤j =
  let k = suc k′ in
  let gSa = good-now{ts = cons Later ts}
              (good (S a) (sucˢ x)) time-x (muˢ S δ , δ)
              j k k≤j in
  let gSaz = good (S a) zeroˢ (muˢ S δ , ↓ᵈ j x δ) k′ k′ ≤-refl in
  let gSaz2 = good (S a) zeroˢ (muˢ S (↓ᵈ j x δ) , ↓ᵈ j x δ) k′ k′ ≤-refl in
  let IH = cong-↓ (λ a → congr (S a)
           ((λ a → good-now-mu S a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j))
            , ≡ᵈ-refl)) a in
  ↓ᵒ k (muˢ S δ a)                                        ⩦⟨ lemma19a S a k δ ⟩
  ↓ᵒ k (# (S a) (muˢ S δ , δ))                                         ⩦⟨ gSa ⟩
  ↓ᵒ k (# (S a) (muˢ S δ , ↓ᵈ j x δ))                                 ⩦⟨ gSaz ⟩
  ↓ᵒ k (# (S a) (↓ᵖ k′ (muˢ S δ) , ↓ᵈ j x δ))                           ⩦⟨ IH ⟩
  ↓ᵒ k (# (S a) (↓ᵖ k′ (muˢ S (↓ᵈ j x δ)) , ↓ᵈ j x δ))        ⩦⟨ ≡ᵒ-sym gSaz2 ⟩
  ↓ᵒ k (# (S a) (muˢ S (↓ᵈ j x δ) , ↓ᵈ j x δ))
                                        ⩦⟨ ≡ᵒ-sym (lemma19a S a k (↓ᵈ j x δ)) ⟩
  ↓ᵒ k (muˢ S (↓ᵈ j x δ) a)   ∎

abstract
  down-1-mu : ∀{Γ}{ts : Times Γ}{A}{B}
       (S : A → Setˢ (A ∷ Γ) (cons Later ts))
       (a : A) (x : Γ ∋ B) (δ : Predsᵒ Γ) (j : ℕ)
   → ↓ᵒ 1 (muˢ S δ a) ≡ᵒ ↓ᵒ 1 (muˢ S (↓ᵈ j x δ) a)
  down-1-mu S a x δ j zero = (λ _ → tt) , (λ _ → tt)
  down-1-mu S a x δ j (suc i) = (λ { (s≤s () , _)}) , λ { (s≤s () , _)}

good-later-mu : ∀{Γ}{ts : Times Γ}{A}{B}
   → (S : A → Setˢ (A ∷ Γ) (cons Later ts))
     (a : A) (x : Γ ∋ B)
   → timeof x ts ≡ Later
   → (δ : Predsᵒ Γ) (k j : ℕ)
   → (k ≤ j)
   → ↓ᵒ (suc k) (muˢ S δ a) ≡ᵒ ↓ᵒ (suc k) (muˢ S (↓ᵈ j x δ) a)
good-later-mu {Γ} {ts} {A} S a x time-x δ zero j k≤j = down-1-mu S a x δ j
good-later-mu {Γ} {ts} {A} S a x time-x δ (suc k′) j k≤j =
  let k = suc k′ in
  let gSa = good-later{ts = cons Later ts}
              (good (S a) (sucˢ x)) time-x (muˢ S δ , δ)
              j k k≤j in
  let gSaz = good (S a) zeroˢ (muˢ S δ , ↓ᵈ j x δ) (suc k′) k ≤-refl in
  let gSaz2 = good (S a) zeroˢ (muˢ S (↓ᵈ j x δ) , ↓ᵈ j x δ) k k ≤-refl in
  let IH = cong-↓ (λ a → congr (S a)
           ((λ a → good-later-mu S a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j))
            , ≡ᵈ-refl)) a in

  ↓ᵒ (suc k) (muˢ S δ a)                            ⩦⟨ lemma19a S a (suc k) δ ⟩
  ↓ᵒ (suc k) (# (S a) (muˢ S δ , δ))                                   ⩦⟨ gSa ⟩
  ↓ᵒ (suc k) (# (S a) (muˢ S δ , ↓ᵈ j x δ))                           ⩦⟨ gSaz ⟩
  ↓ᵒ (suc k) (# (S a) (↓ᵖ k (muˢ S δ) , ↓ᵈ j x δ))                      ⩦⟨ IH ⟩
  ↓ᵒ (suc k) (# (S a) (↓ᵖ k (muˢ S (↓ᵈ j x δ)) , ↓ᵈ j x δ))   ⩦⟨ ≡ᵒ-sym gSaz2 ⟩
  ↓ᵒ (suc k) (# (S a) (muˢ S (↓ᵈ j x δ) , (↓ᵈ j x δ)))
                              ⩦⟨ ≡ᵒ-sym (lemma19a S a (suc k) (↓ᵈ j x δ)) ⟩
  ↓ᵒ (suc k) (muˢ S (↓ᵈ j x δ) a)   ∎

goodnesses-mu : ∀{Γ}{ts : Times Γ}{A}
   → (S : A → Setˢ (A ∷ Γ) (cons Later ts))
   → (a : A)
   → goodnesses ts (λ δ → muˢ S δ a)
goodnesses-mu {Γ} {ts} {A} S a x
    with timeof x ts in time-x
... | Now = λ δ j k k≤j → good-now-mu S a x time-x δ k j k≤j
... | Later = λ δ j k k≤j → good-later-mu S a x time-x δ k j k≤j

cong-toFun : ∀{A}{Γ}{δ δ′ : Predsᵒ Γ}{ts : Times Γ}
   → (S : A → Setˢ (A ∷ Γ) (cons Later ts))
   → δ ≡ᵈ δ′
   → (P Q : Predᵒ A)
   → (a : A)
   → (∀ b → P b ≡ᵒ Q b)
   → toFun δ S P a ≡ᵒ toFun δ′ S Q a
cong-toFun{A}{Γ}{δ}{δ′} S δ=δ′ P Q a P=Q =
  let Pδ=Qδ′ : (P , δ) ≡ᵈ (Q , δ′)
      Pδ=Qδ′ = P=Q , δ=δ′ in
  congr (S a) Pδ=Qδ′

congruent-mu : ∀{Γ}{ts : Times Γ}{A}
   (P : A → Setˢ (A ∷ Γ) (cons Later ts))
   (a : A)
   → congruent (λ δ → muˢ P δ a)
congruent-mu{Γ}{ts}{A} P a {δ}{δ′} δ=δ′ = ≡ᵒ-intro Goal
  where
  Goal : (k : ℕ) → μₒ (toFun δ P) a k ⇔ μₒ (toFun δ′ P) a k
  Goal k = ≡ᵒ⇒⇔ (cong-iter{A}{a} (suc k) (toFun δ P) (toFun δ′ P)
                    (cong-toFun P δ=δ′) ⊤ᵖ)

μˢ : ∀{Γ}{ts : Times Γ}{A}
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
   → (A → Setˢ Γ ts)
μˢ {Γ}{ts}{A} P a =
  record { # = λ δ → muˢ P δ a
         ; good = goodnesses-mu P a
         ; congr = congruent-mu P a
         }

∀ˢ : ∀{Γ}{ts : Times Γ}{A : Set}
   → (A → Setˢ Γ ts)
   → Setˢ Γ ts
∀ˢ{Γ}{ts}{A} P =
  record { # = λ δ → ∀ᵒ[ a ] # (P a) δ
         ; good = {!!}
         ; congr = {!!}}

∀ˢ-syntax = ∀ˢ
infix 1 ∀ˢ-syntax
syntax ∀ˢ-syntax (λ x → P) = ∀ˢ[ x ] P

choose : Time → Time → Time
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later

combine : ∀{Γ} (ts₁ ts₂ : Times Γ) → Times Γ
combine {[]} ts₁ ts₂ = ∅
combine {A ∷ Γ} (cons x ts₁) (cons y ts₂) = cons (choose x y) (combine ts₁ ts₂)

infixr 7 _×ˢ_
_×ˢ_ : ∀{Γ}{ts₁ ts₂ : Times Γ}
   → Setˢ Γ ts₁
   → Setˢ Γ ts₂
     ------------------------
   → Setˢ Γ (combine ts₁ ts₂)
S ×ˢ T = record { # = λ δ → # S δ ×ᵒ # T δ ; good = {!!} ; congr = {!!}}

↓ˢ : ∀{Γ}{ts : Times Γ}
   → ℕ
   → Setˢ Γ ts
     ----------
   → Setˢ Γ ts
↓ˢ k S = record { # = λ δ → ↓ᵒ k (# S δ) ; good = {!!} ; congr = {!!}}

applyˢ : ∀ {Γ}{ts : Times Γ}{A}
   (S : Setˢ (A ∷ Γ) (cons Later ts))
   (P : A → Setˢ Γ ts)
   → Setˢ Γ ts   
applyˢ S P =
  record { # = λ δ → (# S) ((λ a → #(P a) δ) , δ) ; good = {!!} ; congr = {!!}}

abstract
  equiv-downᵒ : ∀{S T : Setᵒ}
    → (∀ j → ↓ᵒ j S ≡ᵒ ↓ᵒ j T)
    → S ≡ᵒ T
  equiv-downᵒ {S} {T} ↓S=↓T zero = (λ _ → tz T) , (λ _ → tz S)
  equiv-downᵒ {S} {T} ↓S=↓T (suc k) =
    (λ Ssk → proj₂ (proj₁ (↓S=↓T (suc (suc k)) (suc k)) (≤-refl , Ssk)))
    ,
    λ Tsk → proj₂ (proj₂ (↓S=↓T (suc (suc k)) (suc k)) (≤-refl , Tsk))
  
  equiv-downˢ : ∀{Γ}{ts : Times Γ}{S T : Setˢ Γ ts}
    → (∀ j → ↓ˢ j S ≡ˢ ↓ˢ j T)
    → S ≡ˢ T
  equiv-downˢ {Γ}{ts}{S}{T} ↓S=↓T δ =
     equiv-downᵒ{# S δ}{# T δ} λ j → (↓S=↓T j) δ

continuous : ∀{A} (F : Predᵒ A → Predᵒ A) (a : A) → Set₁
continuous F a = ∀ P k → ↓ᵒ k (F P a) ≡ᵒ ↓ᵒ k (F (↓ᵖ k P) a)

continuous′ : ∀{Γ}{A}{ts : Times Γ}{δ : Predsᵒ Γ}
  (F : A → Setˢ (A ∷ Γ) (cons Later ts)) (a : A) → Set₁
continuous′{Γ}{A}{ts}{δ} F a =
  ∀ P k → ↓ᵒ k (# (F a) (P , δ)) ≡ᵒ ↓ᵒ k (# (F a) ((↓ᵖ k P) , δ))

{- sanity check -}
cont-toFun : ∀{Γ}{A}{ts : Times Γ}{δ : Predsᵒ Γ}
  → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
  → (a : A)
  → continuous′{δ = δ} F a
  → continuous (toFun δ F) a
cont-toFun{Γ}{A}{ts}{δ} F a cont′ = cont′

wellfounded : ∀{A} (F : Predᵒ A → Predᵒ A) (a : A) → Set₁
wellfounded F a = ∀ P k → ↓ᵒ (suc k) (F P a) ≡ᵒ ↓ᵒ (suc k) (F (↓ᵖ k P) a)

wellfounded′ : ∀{Γ}{A}{ts : Times Γ}{δ : Predsᵒ Γ}
  (F : A → Setˢ (A ∷ Γ) (cons Later ts)) (a : A) → Set₁
wellfounded′{Γ}{A}{ts}{δ} F a =
  ∀ P k → ↓ᵒ (suc k) (# (F a) (P , δ))
       ≡ᵒ ↓ᵒ (suc k) (# (F a) ((↓ᵖ k P) , δ))

{- sanity check -}
WF-toFun : ∀{Γ}{A}{ts : Times Γ}{δ : Predsᵒ Γ}
  → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
  → (a : A)
  → wellfounded′{δ = δ} F a
  → wellfounded (toFun δ F) a
WF-toFun{Γ}{A}{ts}{δ} F a cont′ = cont′

cong-⇔-× : ∀{P P′ Q Q′ : Set}
   → P ⇔ P′
   → Q ⇔ Q′
   → (P × Q) ⇔ (P′ × Q′)
cong-⇔-× P=P′ Q=Q′ = {!!}



lemma19 : ∀{Γ}{ts : Times Γ}{A}
   (F : A → Setˢ (A ∷ Γ) (cons Later ts))
   (a : A)
   (j : ℕ)
   → ↓ˢ j (μˢ F a) ≡ˢ ↓ˢ j (applyˢ (F a) (μˢ F))
lemma19{Γ}{ts}{A} F a j = ≡ˢ-intro (lemma19a F a j)

fixpointˢ : ∀{Γ}{ts : Times Γ}{A}
   (F : A → Setˢ (A ∷ Γ) (cons Later ts))
   (a : A)
   → μˢ F a ≡ˢ applyˢ (F a) (μˢ F)
fixpointˢ F a = equiv-downˢ (lemma19 F a)
