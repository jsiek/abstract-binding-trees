{-# OPTIONS --without-K --rewriting #-}

{-

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
↓ k S j = j ≤ k  ×  S j
--↓ k S zero = ⊤
--↓ k S (suc j) = suc j < k × (S (suc j))

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
                ; down = λ {j (j≤k , Sj) i i≤j →
                             ≤-trans i≤j j≤k , down S j Sj i i≤j}
                ; tz = z≤n  , tz S
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

record Setˢ (Γ : Context) (ts : Times Γ) : Set₁ where
  field
    # : Predsᵒ Γ → Setᵒ 
    good : goodness ts #
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
    → Eq._≡_ S T
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
▷ˢ S = record { # = λ δ → ▷ᵒ (# S δ) }


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
ze · a = record { # = λ (μP , δ) → μP a }
_·_ {A ∷ Γ}{cons t ts} (sc x) a =
    record { # = λ {(μP , δ) → # (_·_{Γ}{ts} x a) δ} }

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
  record { # = λ k → #(iter{_}{Predᵒ A} (suc k) (toFun δ P) (λ a → ⊤ᵒ) a) k
         ; down = {!!}
         ; tz = {!!}
         }

μˢ : ∀{Γ}{ts : Times Γ}{A}
   → (A → Setˢ (A ∷ Γ) (cons Later ts))
   → (A → Setˢ Γ ts)
μˢ {Γ}{ts}{A} P a = record { # = λ δ → muˢ P δ a ; good = {!!} }


∀ˢ : ∀{Γ}{ts : Times Γ}{A : Set}
   → (A → Setˢ Γ ts)
   → Setˢ Γ ts
∀ˢ{Γ}{ts}{A} P = record { # = λ δ → ∀ᵒ[ a ] # (P a) δ ; good = {!!} }

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
S ×ˢ T = record { # = λ δ → # S δ ×ᵒ # T δ }

↓ˢ : ∀{Γ}{ts : Times Γ}
   → ℕ
   → Setˢ Γ ts
     ----------
   → Setˢ Γ ts
↓ˢ k S = record { # = λ δ → ↓ᵒ k (# S δ) }

applyˢ : ∀ {Γ}{ts : Times Γ}{A}
   (S : Setˢ (A ∷ Γ) (cons Later ts))
   (P : A → Setˢ Γ ts)
   → Setˢ Γ ts   
applyˢ S P =
  record { # = λ δ → (# S) ((λ a → #(P a) δ) , δ) }

abstract
  equiv-downᵒ : ∀{S T : Setᵒ}
    → (∀ j → ↓ᵒ j S ≡ᵒ ↓ᵒ j T)
    → S ≡ᵒ T
  equiv-downᵒ {S} {T} ↓S=↓T zero = (λ _ → tz T) , (λ _ → tz S)
  equiv-downᵒ {S} {T} ↓S=↓T (suc k) =
    (λ Ssk → proj₂ (proj₁ (↓S=↓T (suc k) (suc k)) (≤-refl , Ssk)))
    ,
    (λ Tsk → proj₂ (proj₂ (↓S=↓T (suc k) (suc k)) (≤-refl , Tsk)))
  
  equiv-downˢ : ∀{Γ}{ts : Times Γ}{S T : Setˢ Γ ts}
    → (∀ j → ↓ˢ j S ≡ˢ ↓ˢ j T)
    → S ≡ˢ T
  equiv-downˢ {Γ}{ts}{S}{T} ↓S=↓T δ =
     equiv-downᵒ{# S δ}{# T δ} λ j → (↓S=↓T j) δ

abstract 
  ↓ᵒ-zero : ∀{A}{P Q : Predᵒ A} (a : A) → ↓ᵒ zero (P a) ≡ᵒ ↓ᵒ zero (Q a)
  ↓ᵒ-zero{A}{P}{Q} a zero = (λ _ → z≤n , tz (Q a)) , (λ _ → z≤n , tz (P a))
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
                                  ⩦⟨ {!!} {- cong-↓ (congr F (lemma15a F)) -} ⟩
    ↓ᵒ (suc j) (f (↓ᵖ j (iter j f Q)) a)
                                      ⩦⟨ ≡ᵒ-sym (good (F a) δ (iter j f Q) j) ⟩
    ↓ᵒ (suc j) (f (iter j f Q) a)
  ∎


cong-⇔-× : ∀{P P′ Q Q′ : Set}
   → P ⇔ P′
   → Q ⇔ Q′
   → (P × Q) ⇔ (P′ × Q′)
cong-⇔-× P=P′ Q=Q′ = {!!}

lemma18a : ∀{Γ}{ts : Times Γ}{A}
   → (k : ℕ)
   → (F : A → Setˢ (A ∷ Γ) (cons Later ts))
   → (a : A)
   → (δ : Predsᵒ Γ)
   → ↓ᵒ k (muˢ F δ a) ≡ᵒ ↓ᵒ k (iter k (toFun δ F) (λ a → ⊤ᵒ) a)
lemma18a k F a δ = ≡ᵒ-intro Goal
  where
  Goal : (j : ℕ) →
         ↓ k (λ j₁ → # (toFun δ F (iter j₁ (toFun δ F) (λ a₁ → ⊤ᵒ)) a) j₁) j
       ⇔ ↓ k (# (iter k (toFun δ F) (λ a₁ → ⊤ᵒ) a)) j
  Goal j =
    ↓ k (λ j₁ → # (toFun δ F (iter j₁ (toFun δ F) (λ a₁ → ⊤ᵒ)) a) j₁) j
       ⩦⟨ ⩦-refl refl ⟩    
    j ≤ k  ×  # (iter (suc j) (toFun δ F) (λ a₁ → ⊤ᵒ) a) j
       ⩦⟨ {!!} ⟩
    j ≤ k  ×  # (↓ᵒ (suc j) (iter (suc j) (toFun δ F) (λ a₁ → ⊤ᵒ) a)) j
       ⩦⟨ {!!}  ⟩    
    j ≤ k  ×  # (↓ᵒ (suc j) (iter k (toFun δ F) (λ a₁ → ⊤ᵒ) a)) j
       ⩦⟨ {!!}  ⟩    
    j ≤ k  ×  # (iter k (toFun δ F) (λ a₁ → ⊤ᵒ) a) j
       ⩦⟨ ⩦-refl refl  ⟩    
    ↓ k (# (iter k (toFun δ F) (λ a₁ → ⊤ᵒ) a)) j   ∎


lemma19 : ∀{Γ}{ts : Times Γ}{A}
   (F : A → Setˢ (A ∷ Γ) (cons Later ts))
   (a : A)
   (j : ℕ)
   → ↓ˢ j (μˢ F a) ≡ˢ ↓ˢ j (applyˢ (F a) (μˢ F))
lemma19{Γ} F a j = ≡ˢ-intro λ δ → Goal δ -- ≡ᵒ-intro λ k → {!!}
  where
  Goal : (δ : Predsᵒ Γ) →
      ↓ᵒ j (muˢ F δ a) ≡ᵒ ↓ᵒ j (# (F a) (muˢ F δ , δ))
  Goal δ =
    ↓ᵒ j (muˢ F δ a)                                 ⩦⟨ lemma18a j F a δ  ⟩
    ↓ᵒ j (iter j (toFun δ F) (λ a → ⊤ᵒ) a)           ⩦⟨ {!!}  ⟩
    ↓ᵒ j (iter (suc j) (toFun δ F) (λ a → ⊤ᵒ) a)     ⩦⟨ {!!}  ⟩
    ↓ᵒ j (↓ᵒ (suc j) (iter (suc j) (toFun δ F) (λ a → ⊤ᵒ) a))  ⩦⟨ {!!}  ⟩
    ↓ᵒ j (↓ᵒ (suc j) (# (F a) (muˢ F δ , δ)))        ⩦⟨ {!!}  ⟩
    ↓ᵒ j (# (F a) (muˢ F δ , δ))                      ∎


--    ↓ˢ j (μˢ F a)                  ⩦⟨ {!!} ⟩
--    ↓ˢ j (applyˢ (F a) (μˢ F))     ∎

    -- ↓ˢ a (μˢ j F)                                  ⩦⟨ {!!} ⟩
    -- ↓ˢ a (iter j ? ?)                               ⩦⟨ {!!} ⟩
    -- ↓ˢ a (applyˢ (j F) (μˢ j))                     ∎

fixpointˢ : ∀{Γ}{ts : Times Γ}{A}
   (F : A → Setˢ (A ∷ Γ) (cons Later ts))
   (a : A)
   → μˢ F a ≡ˢ applyˢ (F a) (μˢ F)
fixpointˢ F a = equiv-downˢ (lemma19 F a)
