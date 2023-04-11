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
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
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

continuousˢ : ∀{Γ}{A} (S : Predsᵒ (A ∷ Γ) → Setᵒ) (δ : Predsᵒ Γ) → Set₁
continuousˢ{Γ}{A} S δ =
  ∀ P k → ↓ᵒ k (S (P , δ)) ≡ᵒ ↓ᵒ k (S ((↓ᵖ k P) , δ))

wellfoundedˢ : ∀{Γ}{A} (S : Predsᵒ (A ∷ Γ) → Setᵒ) (δ : Predsᵒ Γ) → Set₁
wellfoundedˢ{Γ}{A} S δ =
  ∀ P k → ↓ᵒ (suc k) (S (P , δ)) ≡ᵒ ↓ᵒ (suc k) (S ((↓ᵖ k P) , δ))

goodness : ∀{Γ} → Times Γ → (Predsᵒ Γ → Setᵒ) → Set₁
goodness {[]} ts S = topᵖ
goodness {A ∷ Γ} (cons Now ts) S = ∀ δ → continuousˢ S δ
goodness {A ∷ Γ} (cons Later ts) S = ∀ δ → wellfoundedˢ S δ


congruent : ∀{Γ} → Times Γ → (Predsᵒ Γ → Setᵒ) → Set₁
congruent {[]} ts S = topᵖ
congruent {A ∷ Γ} (cons t ts) S =
  ∀{P Q} → (∀ a → P a ≡ᵒ Q a) → (∀ δ → S (P , δ) ≡ᵒ S (Q , δ))

record Setˢ (Γ : Context) (ts : Times Γ) : Set₁ where
  field
    # : Predsᵒ Γ → Setᵒ 
    good : goodness ts #
    congr : congruent ts #
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


{-
  Variable refering to a recursive predicate (from a μˢ)
-}
data _⊢_ : Context → Set → Set₁ where
  ze : ∀{Γ}{A} → (A ∷ Γ) ⊢ A
  sc : ∀{Γ}{A}{B} → Γ ⊢ B → (A ∷ Γ) ⊢ B

{-
Apply recursive predicate to an argument.
-}
_·_ : ∀{Γ}{ts : Times Γ}{A} → (x : Γ ⊢ A) → A → Setˢ Γ ts
ze · a = record { # = λ (μP , δ) → μP a ; good = {!!} ; congr = {!!} }
_·_ {A ∷ Γ}{cons t ts} (sc x) a =
    record { # = λ {(μP , δ) → # (_·_{Γ}{ts} x a) δ} ; good = {!!} ; congr = {!!}}

iter : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → (A → A)
iter zero    F  =  id
iter (suc n) F  =  F ∘ iter n F

toFun : ∀{Γ}{ts : Times Γ}{A}
   → Predsᵒ Γ
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
     ----------------------------------
   → (Predᵒ A → Predᵒ A)
toFun δ P μP = λ a → # (P a) (μP , δ)

muˢ : ∀{Γ}{ts : Times Γ}{A}
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
   → Predsᵒ Γ
   → (A → Setᵒ)
muˢ {Γ}{ts}{A} P δ a =
  record { # = λ k → #(iter{_}{Predᵒ A} (suc k) (toFun δ P) ⊤ᵖ a) k
         ; down = {!!}
         ; tz = {!!}
         }

μˢ : ∀{Γ}{ts : Times Γ}{A}
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
   → (A → Setˢ Γ ts)
μˢ {Γ}{ts}{A} P a = record { # = λ δ → muˢ P δ a ; good = {!!} ; congr = {!!} }


∀ˢ : ∀{Γ}{ts : Times Γ}{A : Set}
   → (A → Setˢ Γ ts)
   → Setˢ Γ ts
∀ˢ{Γ}{ts}{A} P = record { # = λ δ → ∀ᵒ[ a ] # (P a) δ ; good = {!!} ; congr = {!!}}

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

abstract 
  ↓ᵒ-zero : ∀{A}{P Q : Predᵒ A} (a : A) → ↓ᵒ zero (P a) ≡ᵒ ↓ᵒ zero (Q a)
  ↓ᵒ-zero{A}{P}{Q} a zero = (λ _ → tt) , λ _ → tt
  ↓ᵒ-zero{A}{P}{Q} a (suc i) = (λ {()}) , (λ {()})


continuous : ∀{A} (F : Predᵒ A → Predᵒ A) (a : A) → Set₁
continuous F a = ∀ P k → ↓ᵒ k (F P a) ≡ᵒ ↓ᵒ k (F (↓ᵖ k P) a)

continuous′ : ∀{Γ}{A}{ts : Times Γ}{δ : Predsᵒ Γ}
  (F : A → Setˢ (A ∷ Γ) (cons Later ts)) (a : A) → Set₁
continuous′{Γ}{A}{ts}{δ} F a =
  ∀ P k → ↓ᵒ k (# (F a) (P , δ))
       ≡ᵒ ↓ᵒ k (# (F a) ((↓ᵖ k P) , δ))

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

lemma15a : ∀{Γ}{A}{ts : Times Γ}{P Q : Predᵒ A}{δ : Predsᵒ Γ}
  → (j : ℕ)
  → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
  → (a : A)
  → ↓ᵒ j (iter j (toFun δ F) P a) ≡ᵒ ↓ᵒ j (iter j (toFun δ F) Q a)
lemma15a {Γ}{A}{ts}{P}{Q}{δ} zero F a = ↓ᵒ-zero{_}{P}{Q} a
lemma15a {Γ}{A}{ts}{P}{Q}{δ} (suc j) F a =
  let f = toFun δ F in
  ↓ᵒ (suc j) (f (iter j f P) a)             ⩦⟨ good (F a) δ (iter j f P) j ⟩ 
  ↓ᵒ (suc j) (f (↓ᵖ j (iter j f P)) a)
                   ⩦⟨ cong-↓ (λ a → congr (F a) (λ a → lemma15a j F a) δ) a ⟩
  ↓ᵒ (suc j) (f (↓ᵖ j (iter j f Q)) a)
                                    ⩦⟨ ≡ᵒ-sym (good (F a) δ (iter j f Q) j) ⟩
  ↓ᵒ (suc j) (f (iter j f Q) a)
  ∎

iter-subtract : ∀{ℓ}{A : Set ℓ}{P : A}
  → (F : A → A)
  → (j k : ℕ)
  → j ≤ k
  → (iter j F (iter (k ∸ j) F P)) ≡ (iter k F P)
iter-subtract {A = A} {P} F .zero k z≤n = refl
iter-subtract {A = A} {P} F (suc j) (suc k) (s≤s j≤k)
  rewrite iter-subtract{A = A}{P} F j k j≤k = refl

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

cong-⇔-× : ∀{P P′ Q Q′ : Set}
   → P ⇔ P′
   → Q ⇔ Q′
   → (P × Q) ⇔ (P′ × Q′)
cong-⇔-× P=P′ Q=Q′ = {!!}

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
   ↓ᵒ (suc j) (# (F a) (muˢ F δ , δ))            ⩦⟨ good (F a) δ (muˢ F δ) j ⟩
   ↓ᵒ (suc j) (# (F a) (↓ᵖ j (muˢ F δ) , δ))
                  ⩦⟨ cong-↓ (λ a → congr (F a) (λ a → lemma18a j F a δ ) δ) a ⟩
   ↓ᵒ (suc j) (# (F a) (↓ᵖ j (iter j (toFun δ F) ⊤ᵖ) , δ))
                    ⩦⟨ ≡ᵖ-sym{A} (good (F a) δ (iter j (toFun δ F) ⊤ᵖ) j) {a} ⟩
   ↓ᵒ (suc j) (# (F a) (iter j (toFun δ F) ⊤ᵖ , δ))           ⩦⟨ ≡ᵒ-refl refl ⟩
   ↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)     ∎
       
{- ↓ᵒ is idempotent -}
abstract
  lemma17 : ∀{A}{P : Predᵒ A}{k}{a : A}
     → ↓ᵖ k (↓ᵖ (suc k) P) a ≡ᵒ ↓ᵖ k P a
  lemma17 {A} {P} {k} {a} zero = (λ _ → tt) , (λ _ → tt)
  lemma17 {A} {P} {k} {a} (suc i) =
    (λ {(x , (y , z)) → x , z})
    ,
    λ {(x , y) → x , ((s≤s (<⇒≤ x)) , y)}
  
lemma19 : ∀{Γ}{ts : Times Γ}{A}
   (F : A → Setˢ (A ∷ Γ) (cons Later ts))
   (a : A)
   (j : ℕ)
   → ↓ˢ j (μˢ F a) ≡ˢ ↓ˢ j (applyˢ (F a) (μˢ F))
lemma19{Γ}{ts}{A} F a j = ≡ˢ-intro λ δ → Goal δ
  where
  Goal : (δ : Predsᵒ Γ) →
      ↓ᵒ j (muˢ F δ a) ≡ᵒ ↓ᵒ j (# (F a) (muˢ F δ , δ))
  Goal δ =
    ↓ᵒ j (muˢ F δ a)                                     ⩦⟨ lemma18a j F a δ  ⟩
    ↓ᵒ j (iter j (toFun δ F) ⊤ᵖ a)        ⩦⟨ lemma15b (suc j) j F a (n≤1+n j) ⟩
    ↓ᵒ j (iter (suc j) (toFun δ F) ⊤ᵖ a)
              ⩦⟨ ≡ᵖ-sym (lemma17{A}{(iter (suc j) (toFun δ F) ⊤ᵖ)}{j}{a}) {a} ⟩
    ↓ᵒ j (↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a))
                              ⩦⟨ cong-↓ (λ a → ≡ᵒ-sym (lemma18b j F a δ))  a  ⟩
    ↓ᵒ j (↓ᵒ (suc j) (# (F a) (muˢ F δ , δ)))
                         ⩦⟨ lemma17{A}{λ a → (# (F a) (muˢ F δ , δ))}{j}{a}  ⟩
    ↓ᵒ j (# (F a) (muˢ F δ , δ))                      ∎

fixpointˢ : ∀{Γ}{ts : Times Γ}{A}
   (F : A → Setˢ (A ∷ Γ) (cons Later ts))
   (a : A)
   → μˢ F a ≡ˢ applyˢ (F a) (μˢ F)
fixpointˢ F a = equiv-downˢ (lemma19 F a)
