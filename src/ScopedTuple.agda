{-# OPTIONS --without-K --safe #-}
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Sig

module ScopedTuple where

{- Scet: A scoped Set -}
Scet : {ℓ : Level} → Set (lsuc ℓ)
Scet {ℓ} = Sig → Set ℓ

_⇨_ : {ℓ₁ ℓ₂ : Level} → Scet {ℓ₁} → Scet {ℓ₂} → Set (ℓ₁ ⊔ ℓ₂)
A ⇨ B = (∀ {b : Sig} → A b → B b)

𝒫 : {ℓ : Level} → Scet {ℓ} → Set (lsuc ℓ)
𝒫 {ℓ} A = (∀ {b : Sig} → A b → Set ℓ)

_✖_ : {ℓ₁ ℓ₂ : Level} → Scet {ℓ₁} → Scet {ℓ₂} → Set (lsuc (ℓ₁ ⊔ ℓ₂))
_✖_ {ℓ₁}{ℓ₂} A B = (∀ {b : Sig} → A b → B b → Set (ℓ₁ ⊔ ℓ₂))

Sigs : Set
Sigs = List Sig

Tuple : {ℓ : Level} → Sigs → Scet {ℓ} → Set ℓ
Tuple [] A = ⊤
Tuple (b ∷ bs) A = A b × Tuple bs A

map : ∀{ℓ ℓ′ : Level}{A : Scet {ℓ}}{B : Scet {ℓ′}} → (A ⇨ B) → {bs : Sigs}
   → Tuple {ℓ} bs A → Tuple {ℓ′} bs B
map f {[]} ⊤ = tt
map f {b ∷ bs} ⟨ x , xs ⟩ = ⟨ f x , map f xs ⟩

foldr : ∀{ℓ : Level}{A}{B : Set} → (∀ {b} → A b → B → B)
   → B → {bs : Sigs} → Tuple {ℓ} bs A → B
foldr c n {[]} tt = n
foldr c n {b ∷ bs} ⟨ x , xs ⟩ = c x (foldr c n xs)

all : ∀{A} → 𝒫 A → {bs : Sigs} → Tuple bs A → Set
all {A} P {[]} tt = ⊤
all {A} P {b ∷ bs} ⟨ x , xs ⟩ = P x × (all P xs)

zip : ∀{ℓ₁}{ℓ₂}{A B} → _✖_ {ℓ₁}{ℓ₂} A B → {bs : Sigs}
   → Tuple bs A → Tuple bs B → Set (ℓ₁ ⊔ ℓ₂)
zip R {[]} tt tt = ⊤
zip R {b ∷ bs} ⟨ a₁ , as₁ ⟩ ⟨ a₂ , as₂ ⟩ = R a₁ a₂ × zip R as₁ as₂

map-cong : ∀{ℓ}{A B : Scet {ℓ}}{f g : A ⇨ B} {bs} {xs : Tuple bs A}
  → (∀{b} (x : A b) → f x ≡ g x)
  →  map f xs ≡ map g xs
map-cong {bs = []} {tt} eq = refl
map-cong {bs = b ∷ bs} {⟨ x , xs ⟩} eq = cong₂ ⟨_,_⟩ (eq x) (map-cong eq)

map-compose : ∀{ℓ}{A B C : Scet {ℓ}} {g : B ⇨ C} {f : A ⇨ B} {bs : Sigs}
   {xs : Tuple bs A}
   → (map g (map f xs)) ≡ (map (g ∘ f) xs)
map-compose {A = A}{B}{C} {g} {f} {[]} {tt} = refl
map-compose {A = A}{B}{C} {g} {f} {b ∷ bs} {⟨ x , xs ⟩} =
    cong₂ ⟨_,_⟩ refl map-compose

tuple-pred : ∀{ℓ}{A : Scet {ℓ}}{P : 𝒫 A}
  → (P× : ∀ bs → Tuple bs A → Set)
  → (∀ (b : Sig) → (a : A b) → P {b} a)
  → {bs : Sigs} → (xs : Tuple bs A)
  → (P× [] tt)
  → (∀{b : Sig}{bs : Sigs}{x xs}
       → P {b} x  →  P× bs xs  →  P× (b ∷ bs) ⟨ x , xs ⟩)
  →  P× bs xs
tuple-pred {A} {P} P× f {[]} tt base step = base
tuple-pred {A} {P} P× f {x ∷ bs} ⟨ fst , snd ⟩ base step =
    step (f x fst) (tuple-pred P× f snd base step)




all-intro : ∀{A : Scet} → (P : 𝒫 A)
  → (∀ {b} (a : A b) → P {b} a)
  → {bs : Sigs} → (xs : Tuple bs A)
  → all P xs
all-intro {A} P f {[]} tt = tt
all-intro {A} P f {b ∷ bs} ⟨ x , xs ⟩  = ⟨ (f x) , (all-intro P f xs) ⟩

zip-refl : ∀{ℓ}{bs A} (xs : Tuple {ℓ} bs A) → zip {ℓ} _≡_ xs xs
zip-refl {ℓ}{[]} tt = tt
zip-refl {ℓ}{b ∷ bs} {A} ⟨ x , xs ⟩ = ⟨ refl , zip-refl xs ⟩

zip-intro : ∀{ℓ}{A B : Scet {ℓ}} → (R : A ✖ B)
  → (∀ {c} (a : A c) (b : B c) → R {c} a b)
  → {bs : Sigs} → (xs : Tuple bs A) → (ys : Tuple bs B)
  → zip R xs ys
zip-intro {A} {B} R f {[]} tt tt = tt
zip-intro {A} {B} R f {b ∷ bs} ⟨ x , xs ⟩ ⟨ y , ys ⟩ =
    ⟨ (f x y) , (zip-intro R f xs ys) ⟩

map-pres-zip : ∀{ℓ₁ ℓ₂}{bs}{A1 B1 : Scet {ℓ₁}}{A2 B2 : Scet {ℓ₂}} {xs ys}
  → (P : A1 ✖ B1) → (Q : A2 ✖ B2) → (f : A1 ⇨ A2) → (g : B1 ⇨ B2)
  → zip (λ{b} → P {b}) {bs} xs ys
  → (∀{b}{x}{y} →  P {b} x y  →  Q (f x) (g y))
  → zip Q (map f xs) (map g ys)
map-pres-zip {bs = []} {xs = tt} {tt} P Q f g tt pres = tt
map-pres-zip {bs = b ∷ bs}{xs = ⟨ x , xs ⟩} {⟨ y , ys ⟩} P Q f g ⟨ z , zs ⟩
    pres =
    ⟨ pres z , map-pres-zip P Q f g zs pres ⟩

record Lift-Pred-Tuple {ℓ}{A : Scet{ℓ}} (P : 𝒫 A)
  (P× : ∀{bs} → Tuple bs A → Set) : Set ℓ where
  field base : (P× {bs = []} tt)
        step : (∀{b : Sig}{bs : Sigs}{x xs}
               → P {b} x  →  P× {bs} xs  →  P× ⟨ x , xs ⟩)

record Lift-Rel-Tuple {ℓ}{A B : Scet{ℓ}} (R : A ✖ B)
  (R× : ∀{bs} → Tuple bs A → Tuple bs B → Set) : Set ℓ where
  field base : (R× {bs = []} tt tt)
        step : (∀{b : Sig}{bs : Sigs}{x xs}{y ys}
               → R {b} x y  →  R× {bs} xs ys  →  R× ⟨ x , xs ⟩ ⟨ y , ys ⟩)

Lift-Eq-Tuple : ∀{A : Set} → Lift-Rel-Tuple {A = λ _ → A}{λ _ → A} _≡_ _≡_
Lift-Eq-Tuple = record { base = refl ; step = λ { refl refl → refl } }

all→pred : ∀{bs A xs}
  → (P : 𝒫 A)  →  (P× : ∀ {bs} → Tuple bs A → Set)
  → (L : Lift-Pred-Tuple P P×)
  → all P {bs} xs  →  P× xs
all→pred {[]} {xs = tt} P P× L tt = Lift-Pred-Tuple.base L 
all→pred {b ∷ bs} {xs = ⟨ x , xs ⟩} P P× L ⟨ z , zs ⟩ =
    let IH = all→pred {bs} {xs = xs} P P× L zs in
    Lift-Pred-Tuple.step L z IH

lift-pred : ∀{A : Scet} → (P : 𝒫 A) → (P× : ∀ {bs} → Tuple bs A → Set)
  → (L : Lift-Pred-Tuple P P×)
  → (∀ {b} (a : A b) → P {b} a)
  → {bs : Sigs} → (xs : Tuple bs A)
  →  P× xs
lift-pred {A} P P× L f {bs} xs =
  all→pred {bs}{A}{xs} P P× L (all-intro {A} P f {bs} xs)

zip→rel : ∀{ℓ}{bs}{A B : Scet{ℓ}}{xs ys}
  → (R : A ✖ B)  →  (R× : ∀ {bs} → Tuple bs A → Tuple bs B → Set)
  → (L : Lift-Rel-Tuple R R×)
  → zip R {bs} xs ys  →  R× xs ys
zip→rel {bs = []} {xs = tt} {tt} R R× L tt = Lift-Rel-Tuple.base L 
zip→rel {bs = b ∷ bs} {xs = ⟨ x , xs ⟩} {⟨ y , ys ⟩} R R× L ⟨ z , zs ⟩ =
    let IH = zip→rel {bs = bs} {xs = xs} {ys} R R× L zs in
    Lift-Rel-Tuple.step L z IH

zip-map→rel  : ∀{ℓ₁ ℓ₂}{bs}{A1 B1 : Scet {ℓ₁}}{A2 B2 : Scet {ℓ₂}}{xs ys}
  → (P : A1 ✖ B1)  →  (Q : A2 ✖ B2)
  → (R : ∀ {bs} → Tuple bs A2 → Tuple bs B2 → Set)
  → (f : A1 ⇨ A2)  →  (g : B1 ⇨ B2)
  → (∀{b}{x}{y} →  P{b} x y  →  Q{b} (f x) (g y))
  → (L : Lift-Rel-Tuple Q R)
  → zip P {bs} xs ys  →  R {bs} (map f xs) (map g ys)
zip-map→rel P Q R f g P→Q L zs = zip→rel Q R L (map-pres-zip P Q f g zs P→Q)

map-compose-zip : ∀{ℓ}{A B C C′ : Scet{ℓ}}
   {g : B ⇨ C} {f : A ⇨ B}{h : A ⇨ C′}
   {bs : Sigs}{R : C ✖ C′}
   {xs : Tuple bs A}
   → (∀ {b : Sig} x → R {b} (g (f x)) (h x))
   → zip R (map g (map f xs)) (map h xs)
map-compose-zip {bs = []} {R} {tt} gf=h = tt
map-compose-zip {bs = b ∷ bs} {R} {⟨ x , xs ⟩} gf=h =
    ⟨ (gf=h x) , (map-compose-zip gf=h) ⟩

