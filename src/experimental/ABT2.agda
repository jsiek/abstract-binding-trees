open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax)
    renaming (_,_ to ⟨_,_⟩ )
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Var

module experimental.ABT2 (Op : Set) (sig : Op → List ℕ) where

Sig : Set
Sig = List ℕ

Scet : Set₁
Scet = ℕ → Set

data Args (A : Scet) : Sig → Set

data ABT : Set where
  `_ : Var → ABT
  _⦅_⦆ : (op : Op) → Args (λ _ → ABT) (sig op) → ABT

data Args A where
  nil : Args A []
  cons : ∀{b bs} → A b → Args A bs → Args A (b ∷ bs)

_⇨_ : Scet → Scet → Set
A ⇨ B = (∀ {b : ℕ} → A b → B b)

𝒫 : Scet → Set₁
𝒫 A = (∀ {b : ℕ} → A b → Set)

_✖_ : Scet → Scet → Set₁
A ✖ B = (∀ {b : ℕ} → A b → B b → Set)

Tuple : Sig → Scet → Set
Tuple bs A = Args A bs

map : ∀{A B} → (A ⇨ B) → {bs : Sig} → Tuple bs A → Tuple bs B
map f {[]} ⊤ = nil
map f {b ∷ bs} (cons x  xs) = cons (f x) (map f xs)

map-cong : ∀{A B}{f g : A ⇨ B} {bs} {xs : Tuple bs A}
  → (∀{b} (x : A b) → f x ≡ g x)
  →  map f xs ≡ map g xs
map-cong {bs = []} {nil} eq = refl
map-cong {bs = b ∷ bs} {cons x xs} eq = cong₂ cons (eq x) (map-cong eq)

map-compose : ∀{A B C} {g : B ⇨ C} {f : A ⇨ B} {bs : Sig} {xs : Tuple bs A}
   → (map g (map f xs)) ≡ (map (g ∘ f) xs)
map-compose {bs = []} {nil} = refl
map-compose {bs = b ∷ bs} {cons x xs} = cong₂ cons refl map-compose

