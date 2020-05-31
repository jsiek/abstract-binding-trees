{-

 I shouldn't be trying to fuse two folds as I do below.
 
 Instead I should be folding a fold with a function.

 h (fold σ M) ≡ fold' σ' M 

 where
   σ' x = h (σ x)
   fold' = a version of fold that also does h

-}

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Var
open import GenericSubstitution
open import Function using (_∘_)
open SNF
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
    using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)


module Fold2 (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig

module ArgResult (V : Set) (C : Set) where

  ArgRes : ℕ → Set
  ArgRes 0 = C
  ArgRes (suc n) = V → ArgRes n

  data ArgsRes : List ℕ → Set where
    rnil : ArgsRes []
    rcons : ∀{b bs} → ArgRes b → ArgsRes bs → ArgsRes (b ∷ bs)

record Foldable V C : Set where
  open ArgResult V C
  field ret : V → C
  field fold-free-var : Var → V
  field fold-op : (o : Op) → ArgsRes (sig o) → C
  field shift : V → V

module Folder {V}{C} (F : Foldable V C) where

  open Foldable F
  open ArgResult V C
  open GenericSub V fold-free-var shift using (⧼_⧽; extend)

  fold : Substitution V → ABT → C
  fold-arg : ∀{b} → Substitution V → Arg b → ArgRes b
  fold-args : ∀{bs} → Substitution V → Args bs → ArgsRes bs

  fold σ (` x) = ret (⧼ σ ⧽ x)
  fold σ (o ⦅ args ⦆) = fold-op o (fold-args σ args)

  fold-arg σ (ast M) = fold σ M
  fold-arg σ (bind M) = λ v → fold-arg (extend σ v) M

  fold-args σ nil = rnil
  fold-args σ (cons arg args) = rcons (fold-arg σ arg) (fold-args σ args)

module Fusion {C}
  (F₁ : Foldable ABT ABT)
  (F₂ : Foldable C C)
  where

  open Folder F₁ renaming (fold to fold₁)
  open Folder F₂ renaming (fold to fold₂)
  open Foldable F₁ using ()
      renaming (ret to ret₁; fold-free-var to fold-free-var₁;
                fold-op to fold-op₁; shift to shift₁)
  open Foldable F₂
      renaming (ret to ret₂; fold-free-var to fold-free-var₂;
                fold-op to fold-op₂; shift to shift₂)
{-  
  map : (V → C) → Substitution V → Substitution C
  map f (↑ k) = ↑ k
  map f (v • σ) = f v • map f σ
  
  drop-ret : (k : ℕ) → Substitution V → Substitution C
  drop-ret k (↑ k') = ↑ (k + k')
  drop-ret zero (v • σ) = ret₂ v • map ret₂ σ
  drop-ret (suc k) (v • σ) = drop-ret k σ
-}
  open GenericSub ABT fold-free-var₁ shift₁
    using ()
    renaming (⧼_⧽ to ⧼_⧽₁)

  open GenericSub C fold-free-var₂ shift₂
    using ()
    renaming (drop to drop₂; ⧼_⧽ to ⧼_⧽₂)

  infixr 5 _⨟_
  _⨟_ : Substitution ABT → Substitution C → Substitution C
  ↑ k ⨟ σ₂ = drop₂ k σ₂
  (M • σ₁) ⨟ σ₂ = fold₂ σ₂ M • (σ₁ ⨟ σ₂)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

  compose-is-foldable : Foldable C C
  compose-is-foldable =
      record { ret = ret₂
             ; fold-free-var = (fold₂ id) ∘ fold-free-var₁ {- id?? -}
             ; fold-op = fold-op₂
             ; shift = shift₂ }
  open GenericSub C ((fold₂ id) ∘ fold-free-var₁) shift₂
    using (⧼_⧽)
  open Folder compose-is-foldable

  fusion : ∀ (σ₁ : Substitution ABT) (σ₂ : Substitution C) (M : ABT)
     → fold₂ σ₂ (fold₁ σ₁ M) ≡ fold (σ₁ ⨟ σ₂) M
  fusion σ₁ σ₂ (` x) =
    begin
      fold₂ σ₂ (fold₁ σ₁ (` x))
    ≡⟨⟩
      fold₂ σ₂ (ret₁ (⧼ σ₁ ⧽₁ x))
    ≡⟨ {!!} ⟩
      ret₂ (fold₂ σ₂ (⧼ σ₁ ⧽₁ x))
    ≡⟨ {!!} ⟩
      ret₂ (⧼ σ₁ ⨟ σ₂ ⧽ x)
    ≡⟨⟩
      fold (σ₁ ⨟ σ₂) (` x)
    ∎
  fusion σ₁ σ₂ (op ⦅ args ⦆) = {!!}

