open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Size

module experimental.ScopedTuple where

{- Scet: A scoped Set -}
Scet : Set₁
Scet = ℕ → Set

_⇨_ : Scet → Scet → Set
A ⇨ B = (∀ {b : ℕ} → A b → B b)

𝒫 : Scet → Set₁
𝒫 A = (∀ {b : ℕ} → A b → Set)

_✖_ : Scet → Scet → Set₁
A ✖ B = (∀ {b : ℕ} → A b → B b → Set)

Sig : Set
Sig = List ℕ

Tuple : Sig → Scet → Set
Tuple [] A = ⊤
Tuple (b ∷ bs) A = A b × Tuple bs A

map : ∀{A B} → (A ⇨ B) → {bs : Sig} → Tuple bs A → Tuple bs B
map f {[]} ⊤ = tt
map f {b ∷ bs} ⟨ x , xs ⟩ = ⟨ f x , map f xs ⟩

foldr : ∀{A}{B : Set} → (∀ {b} → A b → B → B)
   → B → {bs : Sig} → Tuple bs A → B
foldr c n {[]} tt = n
foldr c n {b ∷ bs} ⟨ x , xs ⟩ = c x (foldr c n xs)

all : ∀{A} → 𝒫 A → {bs : Sig} → Tuple bs A → Set
all {A} P {[]} tt = ⊤
all {A} P {b ∷ bs} ⟨ x , xs ⟩ = P x × (all P xs)

zip : ∀{A B} → A ✖ B → {bs : Sig} → Tuple bs A → Tuple bs B → Set
zip R {[]} tt tt = ⊤
zip R {b ∷ bs} ⟨ a₁ , as₁ ⟩ ⟨ a₂ , as₂ ⟩ = R a₁ a₂ × zip R as₁ as₂

zip-refl : ∀{bs A} (xs : Tuple bs A) → zip _≡_ xs xs
zip-refl {[]} tt = tt
zip-refl {b ∷ bs} {A} ⟨ x , xs ⟩ = ⟨ refl , zip-refl xs ⟩

map-pres-zip : ∀{bs A1 B1 A2 B2 xs ys}
  → (P : A1 ✖ B1) → (Q : A2 ✖ B2) → (f : A1 ⇨ A2) → (g : B1 ⇨ B2)
  → zip (λ{b} → P {b}) {bs} xs ys
  → (∀{b}{x}{y} →  P {b} x y  →  Q (f x) (g y))
  → zip Q (map f xs) (map g ys)
map-pres-zip {[]} {xs = tt} {tt} P Q f g tt pres = tt
map-pres-zip {b ∷ bs}{xs = ⟨ x , xs ⟩} {⟨ y , ys ⟩} P Q f g ⟨ z , zs ⟩ pres =
    ⟨ pres z , map-pres-zip P Q f g zs pres ⟩

record Lift-Rel-Tuple {A B} (R : A ✖ B)
  (R× : ∀{bs} → Tuple bs A → Tuple bs B → Set) : Set where
  field base : (R× {bs = []} tt tt)
        step : (∀{b : ℕ}{bs : Sig}{x xs}{y ys}
               → R {b} x y  →  R× {bs} xs ys  →  R× ⟨ x , xs ⟩ ⟨ y , ys ⟩)

Lift-Eq-Tuple : ∀{A : Set} → Lift-Rel-Tuple {λ _ → A}{λ _ → A} _≡_ _≡_
Lift-Eq-Tuple = record { base = refl ; step = λ { refl refl → refl } }

zip→rel : ∀{bs A B xs ys}
  → (R : A ✖ B)  →  (R× : ∀ {bs} → Tuple bs A → Tuple bs B → Set)
  → (L : Lift-Rel-Tuple R R×)
  → zip R {bs} xs ys  →  R× xs ys
zip→rel {[]} {xs = tt} {tt} R R× L tt = Lift-Rel-Tuple.base L 
zip→rel {b ∷ bs} {xs = ⟨ x , xs ⟩} {⟨ y , ys ⟩} R R× L ⟨ z , zs ⟩ =
    let IH = zip→rel {bs} {xs = xs} {ys} R R× L zs in
    Lift-Rel-Tuple.step L z IH

zip-map→rel  : ∀{bs A1 B1 A2 B2 xs ys}
  → (P : A1 ✖ B1)  →  (Q : A2 ✖ B2)
  → (R : ∀ {bs} → Tuple bs A2 → Tuple bs B2 → Set)
  → (f : A1 ⇨ A2)  →  (g : B1 ⇨ B2)
  → (∀{b}{x}{y} →  P{b} x y  →  Q{b} (f x) (g y))
  → (L : Lift-Rel-Tuple Q R)
  → zip P {bs} xs ys  →  R {bs} (map f xs) (map g ys)
zip-map→rel P Q R f g P→Q L zs = zip→rel Q R L (map-pres-zip P Q f g zs P→Q)

map-compose-zip : ∀{A B C C′}
   {g : B ⇨ C} {f : A ⇨ B}{h : A ⇨ C′}
   {bs : Sig}{R : C ✖ C′}
   {xs : Tuple bs A}
   → (∀ {b : ℕ} x → R {b} (g (f x)) (h x))
   → zip R (map g (map f xs)) (map h xs)
map-compose-zip {A}{B}{C}{C′} {g} {f} {h} {[]} {R} {tt} gf=h = tt
map-compose-zip {A}{B}{C}{C′} {g} {f} {h} {b ∷ bs} {R} {⟨ x , xs ⟩} gf=h =
    ⟨ (gf=h x) , (map-compose-zip gf=h) ⟩

map-compose : ∀{A B C} {g : B ⇨ C} {f : A ⇨ B} {bs : Sig} {xs : Tuple bs A}
   → (map g (map f xs)) ≡ (map (g ∘ f) xs)
map-compose {A}{B}{C} {g} {f} {[]} {tt} = refl
map-compose {A}{B}{C} {g} {f} {b ∷ bs} {⟨ x , xs ⟩} =
    cong₂ ⟨_,_⟩ refl map-compose

