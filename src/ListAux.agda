{-# OPTIONS --without-K --safe #-}
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Properties using (length-++; ++-assoc; ≡-dec)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties
    using (+-suc; ≤-trans; ≤-step; ≤-refl; ≤-reflexive; m≤m+n; ≤-pred)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning

module ListAux where

private
  variable I : Set

nth : (xs : List I) → (i : ℕ) → .{i< : i < length xs} → I
nth (x ∷ xs) zero {i<} = x
nth (x ∷ xs) (suc i) {i<} = nth xs i {≤-pred i<}

nth-cong : ∀ (xs ys : List I) (i : ℕ)
  {p : i < length xs }{q : i < length ys }
  → xs ≡ ys
  → nth xs i {p} ≡ nth ys i {q}
nth-cong xs ys i {p}{q} refl = refl

length-++-< : (xs ys : List I) (y : I)
   → length xs < length (xs ++ y ∷ ys)
length-++-< xs ys y rewrite length-++ xs {y ∷ ys}
    | +-suc (length xs) (length ys) = s≤s (m≤m+n _ _)   

nth-++ : ∀ (xs ys : List I) (y : I)
   → nth (xs ++ (y ∷ ys)) (length xs) {length-++-< xs ys y} ≡ y
nth-++ [] ys y = refl
nth-++ (x ∷ xs) ys y = nth-++ xs ys y
