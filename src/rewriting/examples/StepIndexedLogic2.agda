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

▷ᵒ_ : Setᵒ → Setᵒ
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

nonexpansiveˢ : ∀{Γ}{A} (S : Predsᵒ (A ∷ Γ) → Setᵒ) (δ : Predsᵒ Γ) → Set₁
nonexpansiveˢ{Γ}{A} S δ =
  ∀ P k → ↓ᵒ k (S (P , δ)) ≡ᵒ ↓ᵒ k (S ((↓ᵖ k P) , δ))

wellfoundedˢ : ∀{Γ}{A} (S : Predsᵒ (A ∷ Γ) → Setᵒ) (δ : Predsᵒ Γ) → Set₁
wellfoundedˢ{Γ}{A} S δ =
  ∀ P k → ↓ᵒ (suc k) (S (P , δ)) ≡ᵒ ↓ᵒ (suc k) (S ((↓ᵖ k P) , δ))

goodness : ∀{Γ} → Times Γ → (Predsᵒ Γ → Setᵒ) → Set₁
goodness {[]} ts S = topᵖ
goodness {A ∷ Γ} (cons Now ts) S = ∀ δ → nonexpansiveˢ S δ
goodness {A ∷ Γ} (cons Later ts) S = ∀ δ → wellfoundedˢ S δ

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

  ≡ˢ-elim : ∀{Γ}{ts : Times Γ}{S T : Setˢ Γ ts}
    → S ≡ˢ T
      ---------------------
    → (∀ δ → # S δ ≡ᵒ # T δ)
  ≡ˢ-elim S=T δ = S=T δ

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

-- TODO: replace uses of later with laters
later : ∀{Γ} (ts : Times Γ) → Times Γ
later {[]} ts = ∅
later {A ∷ Γ} (cons t ts) = cons Later (later ts)

laters : ∀ (Γ : Context) → Times Γ
laters [] = ∅
laters (A ∷ Γ) = cons Later (laters Γ)

timeof-later : ∀{Γ}{ts : Times Γ}{A}
   → (x : Γ ∋ A)
  → (timeof x (later ts)) ≡ Later
timeof-later {B ∷ Γ} {cons t ts} zeroˢ = refl
timeof-later {B ∷ Γ} {cons t ts} (sucˢ x) = timeof-later x

abstract
  cong-↓ᵒ : ∀{P Q : Setᵒ}
    → (k : ℕ)
    → P ≡ᵒ Q
    → ↓ᵒ k P ≡ᵒ ↓ᵒ k Q
  cong-↓ᵒ {P} {Q} k P=Q zero = (λ x → tt) , (λ x → tt)
  cong-↓ᵒ {P} {Q} k P=Q (suc i) =
      (λ {(a , b) → a , proj₁ (P=Q (suc i)) b})
      , λ {(a , b) → a , proj₂ (P=Q (suc i)) b}

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

{---------------------- Later Operator ---------------------}

abstract
  cong-▷ : ∀{S T : Setᵒ}
    → S ≡ᵒ T
    → ▷ᵒ S ≡ᵒ ▷ᵒ T
  cong-▷ S=T zero = (λ x → tt) , (λ x → tt)
  cong-▷ S=T (suc i) = (proj₁ (S=T i)) , (proj₂ (S=T i))

abstract
  down-▷ : ∀{k} (S : Setᵒ)
    → ↓ᵒ (suc k) (▷ᵒ S) ≡ᵒ ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k S))
  down-▷ S zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-▷ S (suc zero) =
      ⇔-intro (λ {(a , b) → a , tt}) (λ {(a , b) → a , (tz S)})
  down-▷ S (suc (suc i)) =
    ⇔-intro
    (λ {(s≤s i≤1+k , ▷Si) →
                 s≤s i≤1+k , i≤1+k , ▷Si})
    (λ {(i≤1+k , (_ , ▷Si)) → i≤1+k , ▷Si})

abstract
  lemma17ᵒ : ∀{S : Setᵒ}
     → (k : ℕ)
     → ↓ᵒ k (↓ᵒ (suc k) S) ≡ᵒ ↓ᵒ k S
  lemma17ᵒ {S} k zero = (λ _ → tt) , (λ _ → tt)
  lemma17ᵒ {S} k (suc i) =
    (λ {(x , (y , z)) → x , z})
    ,
    λ {(x , y) → x , ((s≤s (<⇒≤ x)) , y)}

good-▷ : ∀{Γ}{ts : Times Γ}
   → (S : Setˢ Γ ts)
   → goodnesses (later ts) (λ δ → ▷ᵒ (# S δ))
good-▷{Γ}{ts} S x
    with good S x
... | gS
    with timeof x ts
... | Now rewrite timeof-later{Γ}{ts} x =
  λ δ j k k≤j →
  ↓ᵒ (suc k) (▷ᵒ (# S δ))                              ⩦⟨ down-▷ {k} (# S δ) ⟩ 
  ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k (# S δ)))  ⩦⟨ cong-↓ᵒ (suc k) (cong-▷ (gS δ j k k≤j)) ⟩ 
  ↓ᵒ (suc k) (▷ᵒ (↓ᵒ k (# S (↓ᵈ j x δ))))
                                     ⩦⟨ ≡ᵒ-sym (down-▷ {k} (# S (↓ᵈ j x δ))) ⟩ 
  ↓ᵒ (suc k) (▷ᵒ (# S (↓ᵈ j x δ)))   ∎
... | Later rewrite timeof-later{Γ}{ts} x =
  λ δ j k k≤j →
  ↓ᵒ (suc k) (▷ᵒ (# S δ))                       ⩦⟨ ≡ᵒ-sym (lemma17ᵒ (suc k)) ⟩ 
  ↓ᵒ (suc k) (↓ᵒ (suc (suc k)) (▷ᵒ (# S δ)))    ⩦⟨ cong-↓ᵒ (suc k) (down-▷ _) ⟩
  ↓ᵒ (suc k) (↓ᵒ (suc (suc k)) (▷ᵒ (↓ᵒ (suc k) (# S δ))))
           ⩦⟨ cong-↓ᵒ (suc k) (cong-↓ᵒ (suc (suc k)) (cong-▷ (gS δ j k k≤j))) ⟩
  ↓ᵒ (suc k) (↓ᵒ (suc (suc k)) (▷ᵒ (↓ᵒ (suc k) (# S (↓ᵈ j x δ)))))
                                       ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ (suc k) (down-▷ _)) ⟩
  ↓ᵒ (suc k) (↓ᵒ (suc (suc k)) (▷ᵒ (# S (↓ᵈ j x δ))))     ⩦⟨ lemma17ᵒ (suc k) ⟩
  ↓ᵒ (suc k) (▷ᵒ (# S (↓ᵈ j x δ)))    ∎

▷ˢ : ∀{Γ}{ts : Times Γ}
   → Setˢ Γ ts
     -----------------
   → Setˢ Γ (later ts)
▷ˢ S = record { # = λ δ → ▷ᵒ (# S δ)
              ; good = good-▷ S
              ; congr = λ d=d′ → cong-▷ (congr S d=d′)
              }

{- Lemma's needed for defining recursive predicates -}

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
{- TODO: condense, cleanup, and refactor the lemma17's -}
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
  lemma17f : ∀{S : Setᵒ}{k}
       → ↓ᵒ k (↓ᵒ k S) ≡ᵒ ↓ᵒ k S
  lemma17f {S} {k} zero = (λ x → tt) , (λ x → tt)
  lemma17f {S} {k} (suc i) =
      (λ {(x , (y , z)) → y , z})
      ,
      λ {(x , y) → x , (x , y)}

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

{---------------------- Membership in Recursive Predicate ---------------------}

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

cong-lookup : ∀{Γ}{ts : Times Γ}{A}{δ δ′ : Predsᵒ Γ}
   → (x : Γ ∋ A)
   → (a : A)
   → δ ≡ᵈ δ′
   → lookup{ts = ts} x δ a ≡ᵒ lookup{ts = ts} x δ′ a
cong-lookup {B ∷ Γ} {ts} {.B}{P , δ}{P′ , δ′} zeroˢ a (P=P′ , d=d′) = P=P′ a
cong-lookup {B ∷ Γ} {cons t ts} {A}{P , δ}{P′ , δ′} (sucˢ x) a (P=P′ , d=d′) =
   cong-lookup{ts = ts} x a d=d′

congruent-lookup : ∀{Γ}{ts : Times Γ}{A}
   → (x : Γ ∋ A)
   → (a : A)
   → congruent (λ δ → lookup{ts = ts} x δ a)
congruent-lookup {Γ}{ts}{A} x a d=d′ = cong-lookup x a d=d′

_∈_ : ∀{Γ}{ts : Times Γ}{A}
   → A
   → (x : Γ ∋ A)
   → {now : timeof x ts ≡ Now}
   → Setˢ Γ ts
(_∈_ {Γ}{ts}{A} a x) {now} =
  record { # = λ δ → (lookup{Γ}{ts}{A} x δ) a
         ; good = good-lookup x now
         ; congr = congruent-lookup x a
         }

{---------------------- Recursive Predicate -----------------------------------}
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

μᵒ : ∀{Γ}{ts : Times Γ}{A}
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
   → Predsᵒ Γ
   → (A → Setᵒ)
μᵒ {Γ}{ts}{A} P δ a =
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
     → ↓ᵒ k (μᵒ F δ a) ≡ᵒ ↓ᵒ k (iter k (toFun δ F) ⊤ᵖ a)
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
     → ↓ᵒ (suc j) (# (F a) (μᵒ F δ , δ))
       ≡ᵒ ↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)
lemma18b{Γ}{ts}{A} j F a δ =
   ↓ᵒ (suc j) (# (F a) (μᵒ F δ , δ))      ⩦⟨ g⇒g (good (F a)) δ (μᵒ F δ) j ⟩
   ↓ᵒ (suc j) (# (F a) (↓ᵖ j (μᵒ F δ) , δ))
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
   → ↓ᵒ j (μᵒ F δ a) ≡ᵒ ↓ᵒ j (# (F a) (μᵒ F δ , δ))
lemma19a{Γ}{ts}{A} F a j δ = 
    ↓ᵒ j (μᵒ F δ a)                                     ⩦⟨ lemma18a j F a δ  ⟩
    ↓ᵒ j (iter j (toFun δ F) ⊤ᵖ a)        ⩦⟨ lemma15b (suc j) j F a (n≤1+n j) ⟩
    ↓ᵒ j (iter (suc j) (toFun δ F) ⊤ᵖ a)
              ⩦⟨ ≡ᵖ-sym (lemma17{A}{(iter (suc j) (toFun δ F) ⊤ᵖ)}{j}{a}) {a} ⟩
    ↓ᵒ j (↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a))
                              ⩦⟨ cong-↓ (λ a → ≡ᵒ-sym (lemma18b j F a δ))  a  ⟩
    ↓ᵒ j (↓ᵒ (suc j) (# (F a) (μᵒ F δ , δ)))
                         ⩦⟨ lemma17{A}{λ a → (# (F a) (μᵒ F δ , δ))}{j}{a}  ⟩
    ↓ᵒ j (# (F a) (μᵒ F δ , δ))                      ∎

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
   → ↓ᵒ k (μᵒ S δ a) ≡ᵒ ↓ᵒ k (μᵒ S (↓ᵈ j x δ) a)
good-now-mu {Γ} {ts} {A} S a x time-x δ zero j k≤j =
    ↓ᵒ-zero{A}{μᵒ S δ}{μᵒ S (↓ᵈ _ x δ)} a
good-now-mu {Γ} {ts} {A} S a x time-x δ (suc k′) j k≤j =
  let k = suc k′ in
  let gSa = good-now{ts = cons Later ts}
              (good (S a) (sucˢ x)) time-x (μᵒ S δ , δ)
              j k k≤j in
  let gSaz = good (S a) zeroˢ (μᵒ S δ , ↓ᵈ j x δ) k′ k′ ≤-refl in
  let gSaz2 = good (S a) zeroˢ (μᵒ S (↓ᵈ j x δ) , ↓ᵈ j x δ) k′ k′ ≤-refl in
  let IH = cong-↓ (λ a → congr (S a)
           ((λ a → good-now-mu S a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j))
            , ≡ᵈ-refl)) a in
  ↓ᵒ k (μᵒ S δ a)                                        ⩦⟨ lemma19a S a k δ ⟩
  ↓ᵒ k (# (S a) (μᵒ S δ , δ))                                         ⩦⟨ gSa ⟩
  ↓ᵒ k (# (S a) (μᵒ S δ , ↓ᵈ j x δ))                                 ⩦⟨ gSaz ⟩
  ↓ᵒ k (# (S a) (↓ᵖ k′ (μᵒ S δ) , ↓ᵈ j x δ))                           ⩦⟨ IH ⟩
  ↓ᵒ k (# (S a) (↓ᵖ k′ (μᵒ S (↓ᵈ j x δ)) , ↓ᵈ j x δ))        ⩦⟨ ≡ᵒ-sym gSaz2 ⟩
  ↓ᵒ k (# (S a) (μᵒ S (↓ᵈ j x δ) , ↓ᵈ j x δ))
                                        ⩦⟨ ≡ᵒ-sym (lemma19a S a k (↓ᵈ j x δ)) ⟩
  ↓ᵒ k (μᵒ S (↓ᵈ j x δ) a)   ∎

abstract
  down-1-mu : ∀{Γ}{ts : Times Γ}{A}{B}
       (S : A → Setˢ (A ∷ Γ) (cons Later ts))
       (a : A) (x : Γ ∋ B) (δ : Predsᵒ Γ) (j : ℕ)
   → ↓ᵒ 1 (μᵒ S δ a) ≡ᵒ ↓ᵒ 1 (μᵒ S (↓ᵈ j x δ) a)
  down-1-mu S a x δ j zero = (λ _ → tt) , (λ _ → tt)
  down-1-mu S a x δ j (suc i) = (λ { (s≤s () , _)}) , λ { (s≤s () , _)}

good-later-mu : ∀{Γ}{ts : Times Γ}{A}{B}
   → (S : A → Setˢ (A ∷ Γ) (cons Later ts))
     (a : A) (x : Γ ∋ B)
   → timeof x ts ≡ Later
   → (δ : Predsᵒ Γ) (k j : ℕ)
   → (k ≤ j)
   → ↓ᵒ (suc k) (μᵒ S δ a) ≡ᵒ ↓ᵒ (suc k) (μᵒ S (↓ᵈ j x δ) a)
good-later-mu {Γ} {ts} {A} S a x time-x δ zero j k≤j = down-1-mu S a x δ j
good-later-mu {Γ} {ts} {A} S a x time-x δ (suc k′) j k≤j =
  let k = suc k′ in
  let gSa = good-later{ts = cons Later ts}
              (good (S a) (sucˢ x)) time-x (μᵒ S δ , δ)
              j k k≤j in
  let gSaz = good (S a) zeroˢ (μᵒ S δ , ↓ᵈ j x δ) (suc k′) k ≤-refl in
  let gSaz2 = good (S a) zeroˢ (μᵒ S (↓ᵈ j x δ) , ↓ᵈ j x δ) k k ≤-refl in
  let IH = cong-↓ (λ a → congr (S a)
           ((λ a → good-later-mu S a x time-x δ k′ j (≤-trans (n≤1+n _) k≤j))
            , ≡ᵈ-refl)) a in

  ↓ᵒ (suc k) (μᵒ S δ a)                            ⩦⟨ lemma19a S a (suc k) δ ⟩
  ↓ᵒ (suc k) (# (S a) (μᵒ S δ , δ))                                   ⩦⟨ gSa ⟩
  ↓ᵒ (suc k) (# (S a) (μᵒ S δ , ↓ᵈ j x δ))                           ⩦⟨ gSaz ⟩
  ↓ᵒ (suc k) (# (S a) (↓ᵖ k (μᵒ S δ) , ↓ᵈ j x δ))                      ⩦⟨ IH ⟩
  ↓ᵒ (suc k) (# (S a) (↓ᵖ k (μᵒ S (↓ᵈ j x δ)) , ↓ᵈ j x δ))   ⩦⟨ ≡ᵒ-sym gSaz2 ⟩
  ↓ᵒ (suc k) (# (S a) (μᵒ S (↓ᵈ j x δ) , (↓ᵈ j x δ)))
                              ⩦⟨ ≡ᵒ-sym (lemma19a S a (suc k) (↓ᵈ j x δ)) ⟩
  ↓ᵒ (suc k) (μᵒ S (↓ᵈ j x δ) a)   ∎

goodnesses-mu : ∀{Γ}{ts : Times Γ}{A}
   → (S : A → Setˢ (A ∷ Γ) (cons Later ts))
   → (a : A)
   → goodnesses ts (λ δ → μᵒ S δ a)
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
   → congruent (λ δ → μᵒ P δ a)
congruent-mu{Γ}{ts}{A} P a {δ}{δ′} δ=δ′ = ≡ᵒ-intro Goal
  where
  Goal : (k : ℕ) → μₒ (toFun δ P) a k ⇔ μₒ (toFun δ′ P) a k
  Goal k = ≡ᵒ⇒⇔ (cong-iter{A}{a} (suc k) (toFun δ P) (toFun δ′ P)
                    (cong-toFun P δ=δ′) ⊤ᵖ)

μˢ : ∀{Γ}{ts : Times Γ}{A}
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
   → (A → Setˢ Γ ts)
μˢ {Γ}{ts}{A} P a =
  record { # = λ δ → μᵒ P δ a
         ; good = goodnesses-mu P a
         ; congr = congruent-mu P a
         }

{---------------------- Forall -----------------------------------------}

abstract
  down-∀ : ∀{A}{P : Predᵒ A}{k}
    → ↓ᵒ k (∀ᵒ[ a ] P a) ≡ᵒ ↓ᵒ k (∀ᵒ[ a ] ↓ᵒ k (P a))
  down-∀ {A} {P} {k} zero = (λ x → tt) , (λ x → tt)
  down-∀ {A} {P} {k} (suc i) =
    (λ {(a , b) → a , (λ c → a , b c)})
    , λ {(a , b) → a , (λ a → proj₂ (b a))}

  cong-∀ : ∀{A}{P Q : Predᵒ A}
    → (∀ a → P a ≡ᵒ Q a)
    → (∀ᵒ P) ≡ᵒ (∀ᵒ Q)
  cong-∀ {A} {P} {k} P=Q zero =
      (λ z a → proj₁ (P=Q a zero) (z a)) , (λ _ a → tz (P a))
  cong-∀ {A} {P} {k} P=Q (suc i) =
        (λ z a → proj₁ (P=Q a (suc i)) (z a))
      , (λ z a → proj₂ (P=Q a (suc i)) (z a))
  
good-all : ∀{Γ}{ts : Times Γ}{A : Set}
   (P : A → Setˢ Γ ts)
  → goodnesses ts (λ δ → ∀ᵒ-syntax (λ a → # (P a) δ))
good-all {Γ}{ts}{A} P x
    with timeof x ts in time-x
... | Now = λ δ j k k≤j →
      ↓ᵒ k (∀ᵒ[ a ] # (P a) δ)                                      ⩦⟨ down-∀ ⟩
      ↓ᵒ k (∀ᵒ[ a ] ↓ᵒ k (# (P a) δ))
          ⩦⟨ cong-↓ᵒ k (cong-∀(λ a → good-now(good(P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ k (∀ᵒ[ a ] ↓ᵒ k (# (P a) (↓ᵈ j x δ)))               ⩦⟨ ≡ᵒ-sym down-∀ ⟩
      ↓ᵒ k (∀ᵒ[ a ] # (P a) (↓ᵈ j x δ))   ∎

... | Later = λ δ j k k≤j → 
      ↓ᵒ (suc k) (∀ᵒ[ a ] # (P a) δ)                                ⩦⟨ down-∀ ⟩
      ↓ᵒ (suc k) (∀ᵒ[ a ] ↓ᵒ (suc k) (# (P a) δ))
                      ⩦⟨ cong-↓ᵒ (suc k) (cong-∀
                          (λ a → good-later (good (P a) x) time-x δ j k k≤j)) ⟩
      ↓ᵒ (suc k) (∀ᵒ[ a ] ↓ᵒ (suc k) (# (P a) (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym down-∀ ⟩
      ↓ᵒ (suc k) (∀ᵒ[ a ] # (P a) (↓ᵈ j x δ))            ∎

∀ˢ : ∀{Γ}{ts : Times Γ}{A : Set}
   → (A → Setˢ Γ ts)
   → Setˢ Γ ts
∀ˢ{Γ}{ts}{A} P =
  record { # = λ δ → ∀ᵒ[ a ] # (P a) δ
         ; good = good-all P
         ; congr = λ d=d′ → cong-∀ λ a → congr (P a) d=d′
         }

∀ˢ-syntax = ∀ˢ
infix 1 ∀ˢ-syntax
syntax ∀ˢ-syntax (λ x → P) = ∀ˢ[ x ] P

{---------------------- Constant -----------------------------------------}

const-good : ∀{Γ}{ts : Times Γ}{A}
   → (S : Set)
   → (x : Γ ∋ A)
   → good-one x (timeof x ts) (λ δ → S ᵒ)
const-good{Γ}{ts} S x
    with timeof x ts
... | Now = λ δ j k k≤j → ≡ᵒ-refl refl
... | Later = λ δ j k k≤j → ≡ᵒ-refl refl

_ˢ : ∀{Γ} → Set → Setˢ Γ (laters Γ)
S ˢ = record { # = λ δ → S ᵒ
             ; good = λ x → const-good S x
             ; congr = λ d=d′ → ≡ᵒ-refl refl
             }
{---------------------- Conjunction -----------------------------------------}

choose : Time → Time → Time
choose Now Now = Now
choose Now Later = Now
choose Later Now = Now
choose Later Later = Later

combine : ∀{Γ} (ts₁ ts₂ : Times Γ) → Times Γ
combine {[]} ts₁ ts₂ = ∅
combine {A ∷ Γ} (cons x ts₁) (cons y ts₂) = cons (choose x y) (combine ts₁ ts₂)

timeof-combine : ∀{Γ}{ts₁ ts₂ : Times Γ}{A}{x : Γ ∋ A}
   → timeof x (combine ts₁ ts₂) ≡ choose (timeof x ts₁) (timeof x ts₂)
timeof-combine {B ∷ Γ} {cons s ts₁} {cons t ts₂} {.B} {zeroˢ} = refl
timeof-combine {B ∷ Γ} {cons s ts₁} {cons t ts₂} {A} {sucˢ x} =
  timeof-combine {Γ} {ts₁} {ts₂} {A} {x}

abstract
  down-× : ∀{S T : Setᵒ}{k}
     → ↓ᵒ k (S ×ᵒ T) ≡ᵒ ↓ᵒ k ((↓ᵒ k S) ×ᵒ (↓ᵒ k T))
  down-× zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-× (suc i) =
      ⇔-intro
      (λ { (si<k , Ssi , Tsi) → si<k , ((si<k , Ssi) , (si<k , Tsi))})
      (λ { (si<k , (_ , Ssi) , _ , Tsi) → si<k , Ssi , Tsi})

  cong-×ᵒ : ∀{S S′ T T′ : Setᵒ}
     → S ≡ᵒ S′
     → T ≡ᵒ T′
     → S ×ᵒ T ≡ᵒ S′ ×ᵒ T′
  cong-×ᵒ {S}{S′}{T}{T′} SS′ TT′ k = ⇔-intro to fro
    where
    to : # (S ×ᵒ T) k → # (S′ ×ᵒ T′) k
    to (Sk , Tk) = (⇔-to (SS′ k) Sk) , (⇔-to (TT′ k) Tk)
    fro  : #(S′ ×ᵒ T′) k → #(S ×ᵒ T) k
    fro (S′k , T′k) = (⇔-fro (SS′ k) S′k) , (⇔-fro (TT′ k) T′k)

good-pair : ∀{Γ}{ts₁ ts₂ : Times Γ}
   (S : Setˢ Γ ts₁) (T : Setˢ Γ ts₂)
   → goodnesses (combine ts₁ ts₂) (λ δ → # S δ ×ᵒ # T δ)
good-pair {Γ}{ts₁}{ts₂} S T {A} x
    rewrite timeof-combine {Γ}{ts₁}{ts₂}{A}{x}
    with timeof x ts₁ in time-x1 | timeof x ts₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (# S δ ×ᵒ # T δ)                                         ⩦⟨ down-× ⟩ 
    ↓ᵒ k (↓ᵒ k (# S δ) ×ᵒ ↓ᵒ k (# T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-×ᵒ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (# T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-×ᵒ (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym down-× ⟩
    ↓ᵒ k (# S (↓ᵈ j x δ) ×ᵒ # T (↓ᵈ j x δ))  ∎
... | Now | Later = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (# S δ ×ᵒ # T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S δ ×ᵒ # T δ))                ⩦⟨ cong-↓ᵒ k down-× ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) ×ᵒ ↓ᵒ (suc k) (# T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-×ᵒ (≡ᵒ-refl refl) gT)) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) ×ᵒ ↓ᵒ (suc k) (# T (↓ᵈ j x δ))))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-×) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S δ ×ᵒ # T (↓ᵈ j x δ)))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (# S δ ×ᵒ # T (↓ᵈ j x δ))
               ⩦⟨ down-× ⟩ 
    ↓ᵒ k (↓ᵒ k (# S δ) ×ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
               ⩦⟨ cong-↓ᵒ k (cong-×ᵒ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-× ⟩ 
    ↓ᵒ k (# S (↓ᵈ j x δ) ×ᵒ # T (↓ᵈ j x δ))    ∎
... | Later | Now = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (# S δ ×ᵒ # T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S δ ×ᵒ # T δ))                ⩦⟨ cong-↓ᵒ k down-× ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) ×ᵒ ↓ᵒ (suc k) (# T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-×ᵒ gS (≡ᵒ-refl refl))) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ (suc k) (# T δ)))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-×) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S (↓ᵈ j x δ) ×ᵒ # T δ))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (# S (↓ᵈ j x δ) ×ᵒ # T δ)
               ⩦⟨ down-× ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (# T δ))
               ⩦⟨ cong-↓ᵒ k (cong-×ᵒ (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ×ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-× ⟩ 
    ↓ᵒ k (# S (↓ᵈ j x δ) ×ᵒ # T (↓ᵈ j x δ))    ∎
... | Later | Later = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ (suc k) (# S δ ×ᵒ # T δ)                ⩦⟨ down-× ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) ×ᵒ ↓ᵒ (suc k) (# T δ))
                   ⩦⟨ cong-↓ᵒ (suc k) (cong-×ᵒ gS gT) ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (# S (↓ᵈ j x δ))
                                  ×ᵒ ↓ᵒ (suc k) (# T (↓ᵈ j x δ)))
                                                ⩦⟨ ≡ᵒ-sym down-× ⟩ 
    ↓ᵒ (suc k) (# S (↓ᵈ j x δ) ×ᵒ # T (↓ᵈ j x δ))   ∎

infixr 7 _×ˢ_
_×ˢ_ : ∀{Γ}{ts₁ ts₂ : Times Γ}
   → Setˢ Γ ts₁
   → Setˢ Γ ts₂
     ------------------------
   → Setˢ Γ (combine ts₁ ts₂)
S ×ˢ T = record { # = λ δ → # S δ ×ᵒ # T δ
                ; good = good-pair S T
                ; congr = λ d=d′ → cong-×ᵒ (congr S d=d′) (congr T d=d′)
                }

{---------------------- Disjunction -----------------------------------------}

abstract
  down-⊎ : ∀{S T : Setᵒ}{k}
     → ↓ᵒ k (S ⊎ᵒ T) ≡ᵒ ↓ᵒ k ((↓ᵒ k S) ⊎ᵒ (↓ᵒ k T))
  down-⊎ zero = ⇔-intro (λ x → tt) (λ x → tt)
  down-⊎ (suc i) =
      (λ { (x , inj₁ x₁) → x , inj₁ (x , x₁)
         ; (x , inj₂ y) → x , inj₂ (x , y)})
      ,
      λ { (x , inj₁ x₁) → x , inj₁ (proj₂ x₁)
        ; (x , inj₂ y) → x , inj₂ (proj₂ y)}

  cong-⊎ᵒ : ∀{S S′ T T′ : Setᵒ}
     → S ≡ᵒ S′
     → T ≡ᵒ T′
     → S ⊎ᵒ T ≡ᵒ S′ ⊎ᵒ T′
  cong-⊎ᵒ {S}{S′}{T}{T′} SS′ TT′ k = ⇔-intro to fro
    where
    to : # (S ⊎ᵒ T) k → # (S′ ⊎ᵒ T′) k
    to (inj₁ x) = inj₁ (proj₁ (SS′ k) x)
    to (inj₂ y) = inj₂ (proj₁ (TT′ k) y)
    fro  : #(S′ ⊎ᵒ T′) k → #(S ⊎ᵒ T) k
    fro (inj₁ x) = inj₁ (proj₂ (SS′ k) x)
    fro (inj₂ y) = inj₂ (proj₂ (TT′ k) y)

good-sum : ∀{Γ}{ts₁ ts₂ : Times Γ}
   (S : Setˢ Γ ts₁) (T : Setˢ Γ ts₂)
   → goodnesses (combine ts₁ ts₂) (λ δ → # S δ ⊎ᵒ # T δ)
good-sum {Γ}{ts₁}{ts₂} S T {A} x
    rewrite timeof-combine {Γ}{ts₁}{ts₂}{A}{x}
    with timeof x ts₁ in time-x1 | timeof x ts₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (# S δ ⊎ᵒ # T δ)                                         ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ k (# S δ) ⊎ᵒ ↓ᵒ k (# T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (# T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))   ⩦⟨ ≡ᵒ-sym down-⊎ ⟩
    ↓ᵒ k (# S (↓ᵈ j x δ) ⊎ᵒ # T (↓ᵈ j x δ))  ∎
... | Now | Later = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (# S δ ⊎ᵒ # T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S δ ⊎ᵒ # T δ))                ⩦⟨ cong-↓ᵒ k down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) ⊎ᵒ ↓ᵒ (suc k) (# T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-⊎ᵒ (≡ᵒ-refl refl) gT)) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) ⊎ᵒ ↓ᵒ (suc k) (# T (↓ᵈ j x δ))))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-⊎) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S δ ⊎ᵒ # T (↓ᵈ j x δ)))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (# S δ ⊎ᵒ # T (↓ᵈ j x δ))
               ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ k (# S δ) ⊎ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
               ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-⊎ ⟩ 
    ↓ᵒ k (# S (↓ᵈ j x δ) ⊎ᵒ # T (↓ᵈ j x δ))    ∎
... | Later | Now = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (# S δ ⊎ᵒ # T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S δ ⊎ᵒ # T δ))                ⩦⟨ cong-↓ᵒ k down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) ⊎ᵒ ↓ᵒ (suc k) (# T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-⊎ᵒ gS (≡ᵒ-refl refl))) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ (suc k) (# T δ)))
                                                ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k down-⊎) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S (↓ᵈ j x δ) ⊎ᵒ # T δ))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (# S (↓ᵈ j x δ) ⊎ᵒ # T δ)
               ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (# T δ))
               ⩦⟨ cong-↓ᵒ k (cong-⊎ᵒ (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) ⊎ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym down-⊎ ⟩ 
    ↓ᵒ k (# S (↓ᵈ j x δ) ⊎ᵒ # T (↓ᵈ j x δ))    ∎
... | Later | Later = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ (suc k) (# S δ ⊎ᵒ # T δ)                ⩦⟨ down-⊎ ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) ⊎ᵒ ↓ᵒ (suc k) (# T δ))
                   ⩦⟨ cong-↓ᵒ (suc k) (cong-⊎ᵒ gS gT) ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (# S (↓ᵈ j x δ))
                                  ⊎ᵒ ↓ᵒ (suc k) (# T (↓ᵈ j x δ)))
                                                ⩦⟨ ≡ᵒ-sym down-⊎ ⟩ 
    ↓ᵒ (suc k) (# S (↓ᵈ j x δ) ⊎ᵒ # T (↓ᵈ j x δ))   ∎

infixr 7 _⊎ˢ_
_⊎ˢ_ : ∀{Γ}{ts₁ ts₂ : Times Γ}
   → Setˢ Γ ts₁
   → Setˢ Γ ts₂
     ------------------------
   → Setˢ Γ (combine ts₁ ts₂)
S ⊎ˢ T = record { # = λ δ → # S δ ⊎ᵒ # T δ
                ; good = good-sum S T
                ; congr = λ d=d′ → cong-⊎ᵒ (congr S d=d′) (congr T d=d′)
                }

{---------------------- Implication -----------------------------------------}

abstract
  down-→ : ∀{S T : Setᵒ}{k}
     → ↓ᵒ k (S →ᵒ T) ≡ᵒ ↓ᵒ k ((↓ᵒ k S) →ᵒ (↓ᵒ k T))
  down-→ zero = (λ x → tt) , (λ x → tt)
  down-→{S}{T} (suc i) =
      (λ {(x , y) → x , (λ { zero x₁ x₂ → tt
                           ; (suc j) x₁ (x₂ , x₃) → x₂ , y (suc j) x₁ x₃})})
      , λ {(x , y) → x , (λ { zero x₁ x₂ → tz T
                            ; (suc j) x₁ x₂ →
                              let z = y (suc j) x₁ ((≤-trans (s≤s x₁) x) , x₂)
                              in proj₂ z})}

  cong-→ : ∀{S S′ T T′ : Setᵒ}
     → S ≡ᵒ S′
     → T ≡ᵒ T′
     → S →ᵒ T ≡ᵒ S′ →ᵒ T′
  cong-→ {S}{S′}{T}{T′} SS′ TT′ k =
    (λ x j x₁ x₂ → proj₁ (TT′ j) (x j x₁ (proj₂ (SS′ j) x₂)))
    , (λ z j z₁ z₂ → proj₂ (TT′ j) (z j z₁ (proj₁ (SS′ j) z₂)))

good-fun : ∀{Γ}{ts₁ ts₂ : Times Γ}
   (S : Setˢ Γ ts₁) (T : Setˢ Γ ts₂)
   → goodnesses (combine ts₁ ts₂) (λ δ → # S δ →ᵒ # T δ)
good-fun {Γ}{ts₁}{ts₂} S T {A} x
    rewrite timeof-combine {Γ}{ts₁}{ts₂}{A}{x}
    with timeof x ts₁ in time-x1 | timeof x ts₂ in time-x2
... | Now | Now = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (# S δ →ᵒ # T δ)                         ⩦⟨ down-→{# S δ}{# T δ} ⟩ 
    ↓ᵒ k (↓ᵒ k (# S δ) →ᵒ ↓ᵒ k (# T δ))
                                     ⩦⟨ cong-↓ᵒ k (cong-→ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (# T δ))
                       ⩦⟨ cong-↓ᵒ k (cong-→{↓ᵒ k (# S (↓ᵈ j x δ))}
                                           {↓ᵒ k (# S (↓ᵈ j x δ))}
                                           {↓ᵒ k (# T δ)}
                                           {↓ᵒ k (# T (↓ᵈ j x δ))}
                                    (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
                          ⩦⟨ ≡ᵒ-sym (down-→{# S (↓ᵈ j x δ)}{# T (↓ᵈ j x δ)}) ⟩
    ↓ᵒ k (# S (↓ᵈ j x δ) →ᵒ # T (↓ᵈ j x δ))  ∎
... | Now | Later = λ δ j k k≤j →
    let gS = good-now (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (# S δ →ᵒ # T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S δ →ᵒ # T δ))   ⩦⟨ cong-↓ᵒ k (down-→{# S δ}{# T δ}) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) →ᵒ ↓ᵒ (suc k) (# T δ)))
         ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k)
             (cong-→{↓ᵒ (suc k) (# S δ)}{↓ᵒ (suc k) (# S δ)}
                     {↓ᵒ (suc k) (# T δ)}{ ↓ᵒ (suc k) (# T (↓ᵈ j x δ))}
                     (≡ᵒ-refl refl) gT)) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) →ᵒ ↓ᵒ (suc k) (# T (↓ᵈ j x δ))))
                       ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k (down-→{# S δ}{# T (↓ᵈ j x δ)})) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S δ →ᵒ # T (↓ᵈ j x δ)))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (# S δ →ᵒ # T (↓ᵈ j x δ))
               ⩦⟨ down-→{# S δ}{# T (↓ᵈ j x δ)} ⟩ 
    ↓ᵒ k (↓ᵒ k (# S δ) →ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
               ⩦⟨ cong-↓ᵒ k (cong-→ gS (≡ᵒ-refl refl)) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym (down-→{# S (↓ᵈ j x δ)}{# T (↓ᵈ j x δ)}) ⟩ 
    ↓ᵒ k (# S (↓ᵈ j x δ) →ᵒ # T (↓ᵈ j x δ))    ∎
... | Later | Now = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-now (good T x) time-x2 δ j k k≤j in
    ↓ᵒ k (# S δ →ᵒ # T δ)                             ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S δ →ᵒ # T δ))   ⩦⟨ cong-↓ᵒ k (down-→{# S δ}{# T δ}) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) →ᵒ ↓ᵒ (suc k) (# T δ)))
                   ⩦⟨ cong-↓ᵒ k (cong-↓ᵒ (suc k) (cong-→ gS (≡ᵒ-refl refl))) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (↓ᵒ (suc k) (# S (↓ᵈ j x δ)) →ᵒ ↓ᵒ (suc k) (# T δ)))
                       ⩦⟨ ≡ᵒ-sym (cong-↓ᵒ k (down-→{# S (↓ᵈ j x δ)}{# T δ})) ⟩ 
    ↓ᵒ k (↓ᵒ (suc k) (# S (↓ᵈ j x δ) →ᵒ # T δ))
               ⩦⟨ lemma17ᵒ k ⟩ 
    ↓ᵒ k (# S (↓ᵈ j x δ) →ᵒ # T δ)
               ⩦⟨ down-→{# S (↓ᵈ j x δ)}{# T δ} ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (# T δ))
               ⩦⟨ cong-↓ᵒ k (cong-→{↓ᵒ k (# S (↓ᵈ j x δ))}
                     {↓ᵒ k (# S (↓ᵈ j x δ))}
                     {↓ᵒ k (# T δ)}{↓ᵒ k (# T (↓ᵈ j x δ))} (≡ᵒ-refl refl) gT) ⟩ 
    ↓ᵒ k (↓ᵒ k (# S (↓ᵈ j x δ)) →ᵒ ↓ᵒ k (# T (↓ᵈ j x δ)))
               ⩦⟨ ≡ᵒ-sym (down-→{# S (↓ᵈ j x δ)}{# T (↓ᵈ j x δ)}) ⟩ 
    ↓ᵒ k (# S (↓ᵈ j x δ) →ᵒ # T (↓ᵈ j x δ))    ∎
... | Later | Later = λ δ j k k≤j →
    let gS = good-later (good S x) time-x1 δ j k k≤j in
    let gT = good-later (good T x) time-x2 δ j k k≤j in
    ↓ᵒ (suc k) (# S δ →ᵒ # T δ)                ⩦⟨ down-→{# S δ}{# T δ} ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (# S δ) →ᵒ ↓ᵒ (suc k) (# T δ))
                   ⩦⟨ cong-↓ᵒ (suc k) (cong-→ gS gT) ⟩ 
    ↓ᵒ (suc k) (↓ᵒ (suc k) (# S (↓ᵈ j x δ))
                                  →ᵒ ↓ᵒ (suc k) (# T (↓ᵈ j x δ)))
                         ⩦⟨ ≡ᵒ-sym (down-→{# S (↓ᵈ j x δ)}{# T (↓ᵈ j x δ)}) ⟩ 
    ↓ᵒ (suc k) (# S (↓ᵈ j x δ) →ᵒ # T (↓ᵈ j x δ))   ∎

infixr 6 _→ˢ_
_→ˢ_ : ∀{Γ}{ts₁ ts₂ : Times Γ}
   → Setˢ Γ ts₁
   → Setˢ Γ ts₂
     ------------------------
   → Setˢ Γ (combine ts₁ ts₂)
S →ˢ T = record { # = λ δ → # S δ →ᵒ # T δ
                ; good = good-fun S T
                ; congr = λ d=d′ → cong-→ (congr S d=d′) (congr T d=d′)
                }

{---------------------- Approximation Operator (↓) ----------------------------}

abstract
  permute-↓ : ∀{S : Setᵒ}{j}{k}
     → ↓ᵒ k (↓ᵒ j S) ≡ᵒ ↓ᵒ j (↓ᵒ k S)
  permute-↓ {S} {j} {k} zero = (λ x → tt) , (λ x → tt)
  permute-↓ {S} {j} {k} (suc i) =
    (λ {(x , (y , z)) → y , x , z}) , λ {(x , (y , z)) → y , x , z}

good-↓ : ∀{Γ}{ts : Times Γ}{i}
   (S : Setˢ Γ ts)
   → goodnesses ts (λ δ → ↓ᵒ i (# S δ))
good-↓ {Γ}{ts}{i} S {A} x
    with timeof x ts in time-x
... | Now = λ δ j k k≤j → 
    let gS = good-now (good S x) time-x δ j k k≤j in
    ↓ᵒ k (↓ᵒ i (# S δ))              ⩦⟨ permute-↓  ⟩ 
    ↓ᵒ i (↓ᵒ k (# S δ))              ⩦⟨ cong-↓ᵒ i gS ⟩ 
    ↓ᵒ i (↓ᵒ k (# S (↓ᵈ j x δ)))     ⩦⟨ permute-↓ ⟩
    ↓ᵒ k (↓ᵒ i (# S (↓ᵈ j x δ)))  ∎
... | Later = λ δ j k k≤j →
    let gS = good-later (good S x) time-x δ j k k≤j in
    ↓ᵒ (suc k) (↓ᵒ i (# S δ))              ⩦⟨ permute-↓  ⟩ 
    ↓ᵒ i (↓ᵒ (suc k) (# S δ))              ⩦⟨ cong-↓ᵒ i gS ⟩ 
    ↓ᵒ i (↓ᵒ (suc k) (# S (↓ᵈ j x δ)))     ⩦⟨ permute-↓ ⟩
    ↓ᵒ (suc k) (↓ᵒ i (# S (↓ᵈ j x δ)))  ∎

↓ˢ : ∀{Γ}{ts : Times Γ}
   → ℕ
   → Setˢ Γ ts
     ----------
   → Setˢ Γ ts
↓ˢ k S = record { # = λ δ → ↓ᵒ k (# S δ)
                ; good = good-↓ S
                ; congr = λ d=d′ → cong-↓ᵒ k (congr S d=d′)}

⇓ : ℕ → ∀{Γ} → Predsᵒ Γ → Predsᵒ Γ
⇓ k {[]} ttᵖ = ttᵖ
⇓ k {A ∷ Γ} (P , δ) = ↓ᵖ k P , ⇓ k δ

{---------------------- Predicate Application ----------------------------}

good-apply : ∀{Γ}{ts : Times Γ}{A}
   (S : Setˢ (A ∷ Γ) (cons Later ts))
   (P : A → Setˢ Γ ts)
   → goodnesses ts (λ δ → # S ((λ a → # (P a) δ) , δ))
good-apply {Γ}{ts}{A} S P x
   with timeof x ts in time-x
... | Now = λ δ j k k≤j →
    let gSz = ((good S) zeroˢ) ((λ a → # (P a) δ) , δ) j k k≤j in
    let gSz2 = ((good S) zeroˢ) ((λ a → # (P a) (↓ᵈ j x δ)) , (↓ᵈ j x δ))
                   j k k≤j in
    let gSsx = good-now{ts = cons Now ts} ((good S) (sucˢ x)) time-x
                 ((λ a → ↓ᵒ j (# (P a) δ)) , δ) j k k≤j in

    let EQ : ((λ a → ↓ᵒ j (# (P a) δ)) , ↓ᵈ j x δ)
              ≡ᵈ ((λ a → ↓ᵒ j  (# (P a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)
        EQ = (λ a → good-now (good (P a) x) time-x δ j j ≤-refl) , ≡ᵈ-refl in
    
    ↓ᵒ k (# S ((λ a → # (P a) δ) , δ))               ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩
    ↓ᵒ k (↓ᵒ (suc k) (# S ((λ a → # (P a) δ) , δ)))
      ⩦⟨ cong-↓ᵒ k gSz ⟩
    ↓ᵒ k (↓ᵒ (suc k) (# S ((λ a → ↓ᵒ j (# (P a) δ)) , δ)))
      ⩦⟨ lemma17ᵒ k ⟩
    ↓ᵒ k (# S ((λ a → ↓ᵒ j (# (P a) δ)) , δ))
      ⩦⟨ gSsx ⟩
    ↓ᵒ k (# S ((λ a → ↓ᵒ j (# (P a) δ)) , ↓ᵈ j x δ))
      ⩦⟨ cong-↓ᵒ k (congr S EQ) ⟩
    ↓ᵒ k (# S ((λ a → ↓ᵒ j (# (P a) (↓ᵈ j x δ))) , ↓ᵈ j x δ))
                        ⩦⟨ ≡ᵒ-sym (lemma17ᵒ k) ⟩
    ↓ᵒ k (↓ᵒ (suc k) (# S ((λ a → ↓ᵒ j (# (P a) (↓ᵈ j x δ))) , ↓ᵈ j x δ)))
      ⩦⟨ cong-↓ᵒ k (≡ᵒ-sym gSz2) ⟩
    ↓ᵒ k (↓ᵒ (suc k) (# S ((λ a → # (P a) (↓ᵈ j x δ)) , ↓ᵈ j x δ)))
      ⩦⟨ lemma17ᵒ k ⟩
    ↓ᵒ k (# S ((λ a → # (P a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))   ∎

... | Later = λ δ j k k≤j →
    let gSz = ((good S) zeroˢ) ((λ a → # (P a) δ) , δ) (suc j) k
                    (≤-trans k≤j (n≤1+n _)) in
    let gSz2 = ((good S) zeroˢ) (((λ a → # (P a) (↓ᵈ j x δ))) , δ) (suc j) k
                    (≤-trans k≤j (n≤1+n _)) in
    let EQ : ((λ a → ↓ᵒ (suc j) (# (P a) δ)) , δ)
              ≡ᵈ ((λ a → ↓ᵒ (suc j)  (# (P a) (↓ᵈ j x δ))) , δ)
        EQ = (λ a → good-later (good (P a) x) time-x δ j j ≤-refl) , ≡ᵈ-refl in
    let gSsx = good-later{ts = cons Now ts} ((good S) (sucˢ x)) time-x
                 ((λ a → # (P a) (↓ᵈ j x δ)) , δ) j k k≤j in
    ↓ᵒ (suc k) (# S ((λ a → # (P a) δ) , δ)) 
      ⩦⟨ gSz ⟩
    ↓ᵒ (suc k) (# S (↓ᵖ (suc j) (λ a → # (P a) δ) , δ)) 
      ⩦⟨ cong-↓ᵒ (suc k) (congr S EQ) ⟩
    ↓ᵒ (suc k) (# S (↓ᵖ (suc j) (λ a → # (P a) (↓ᵈ j x δ)) , δ)) 
      ⩦⟨ ≡ᵒ-sym gSz2 ⟩
    ↓ᵒ (suc k) (# S ((λ a → # (P a) (↓ᵈ j x δ)) , δ)) 
      ⩦⟨ gSsx ⟩
    ↓ᵒ (suc k) (# S ((λ a → # (P a) (↓ᵈ j x δ)) , ↓ᵈ j x δ))  ∎

applyˢ : ∀ {Γ}{ts : Times Γ}{A}
   (S : Setˢ (A ∷ Γ) (cons Later ts))
   (P : A → Setˢ Γ ts)
   → Setˢ Γ ts   
applyˢ S P =
  record { # = λ δ → (# S) ((λ a → #(P a) δ) , δ)
         ; good = good-apply S P
         ; congr = λ d=d′ → congr S ((λ a → congr (P a) d=d′) , d=d′)
         }

{---------------------- Fixpoint Theorem --------------------------------------}

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

nonexpansive : ∀{A} (F : Predᵒ A → Predᵒ A) (a : A) → Set₁
nonexpansive F a = ∀ P k → ↓ᵒ k (F P a) ≡ᵒ ↓ᵒ k (F (↓ᵖ k P) a)

nonexpansive′ : ∀{Γ}{A}{ts : Times Γ}{δ : Predsᵒ Γ}
  (F : A → Setˢ (A ∷ Γ) (cons Later ts)) (a : A) → Set₁
nonexpansive′{Γ}{A}{ts}{δ} F a =
  ∀ P k → ↓ᵒ k (# (F a) (P , δ)) ≡ᵒ ↓ᵒ k (# (F a) ((↓ᵖ k P) , δ))

{- sanity check -}
cont-toFun : ∀{Γ}{A}{ts : Times Γ}{δ : Predsᵒ Γ}
  → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
  → (a : A)
  → nonexpansive′{δ = δ} F a
  → nonexpansive (toFun δ F) a
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
     → 𝓟 ⊢ᵒ (∀ᵒ[ a ] ▷ᵒ (P a))
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
    → (∀ a → P a ≡ᵒ Q a)
      ------------------
    → 𝓟 ⊢ᵒ Q a
  ≡ᵖ⇒⊢ᵒ 𝓟 {A} P Q {a} 𝓟⊢P P=Q n ⊨𝓟n =
      let Pan = 𝓟⊢P n ⊨𝓟n in
      let Qan = ⇔-to (P=Q a n) Pan in
      Qan

{-
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
-}

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

{-
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
-}

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
