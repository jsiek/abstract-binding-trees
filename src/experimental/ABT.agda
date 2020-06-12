open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import ScopedTuple using (Sig; Tuple; foldr; map; zip)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Size
open import Var

module experimental.ABT (Op : Set) (sig : Op → Sig) where

data Term : Size → Set where
  `_ : ∀{s} → Var → Term (↑ s)
  _⦅_⦆ : ∀{s} → (op : Op) → Tuple (sig op) (λ _ → Term s) → Term (↑ s)

ABT : Set
ABT = Term ∞


{- An example of a recursive function on Terms. -}

depth : ∀{s} → Term s → ℕ
depth (` x) = 0
depth (op ⦅ args ⦆) = foldr _⊔_ 0 (map depth args)

{- some basic properties -}

var-injective : ∀ {x y} → ` x ≡ ` y → x ≡ y
var-injective refl = refl

{- Heterogeneous equality between terms of different size -}

data _⩭_ : {s : Size} → Term s → {t : Size} → Term t → Set
⟨_⟩_⩭_ : ∀{s t : Size} → (bs : Sig) → Tuple bs (λ _ → Term s)
    → Tuple bs (λ _ → Term t) → Set

data _⩭_ where
  var⩭ : ∀{i j : Size}{k l : Var} → k ≡ l → `_ {s = i} k ⩭ `_ {s = j} l
  node⩭ : ∀{i j : Size}{op}{args args'}
         → ⟨ sig op ⟩ args ⩭ args'
         → _⦅_⦆ {s = i} op args ⩭ _⦅_⦆ {s = j} op args'

⟨ bs ⟩ xs ⩭ ys = zip (λ M N → M ⩭ N) {bs} xs ys


{- Conversion from heterogeneous equality to equality -}

⩭→≡ : ∀ {s : Size}{M N : Term s} → M ⩭ N → M ≡ N
⟨_⟩⩭→≡ : ∀{s : Size} → (bs : Sig) → {xs ys : Tuple bs (λ _ → Term s)}
    → ⟨ bs ⟩ xs ⩭ ys → xs ≡ ys

⩭→≡ {.(Size.↑ _)} {.(` _)} {.(` _)} (var⩭ refl) = refl
⩭→≡ {.(Size.↑ _)} {.(_ ⦅ _ ⦆)} {.(_ ⦅ _ ⦆)} (node⩭ {op = op} args⩭) =
  cong (_⦅_⦆ op) (⟨ sig op ⟩⩭→≡ args⩭)

⟨_⟩⩭→≡ {s} [] {tt} {tt} tt = refl
⟨_⟩⩭→≡ {s} (b ∷ bs) {⟨ x , xs ⟩} {⟨ y , ys ⟩} ⟨ x=y , xs=ys ⟩
    rewrite ⩭→≡ x=y | ⟨ bs ⟩⩭→≡ xs=ys = refl

