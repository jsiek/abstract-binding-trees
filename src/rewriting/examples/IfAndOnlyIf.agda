{-# OPTIONS --without-K #-}

module rewriting.examples.IfAndOnlyIf where

open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)

abstract
  _⇔_ : Set → Set → Set
  P ⇔ Q = (P → Q) × (Q → P)

  ⇔-intro : ∀{P Q : Set}
    → (P → Q)
    → (Q → P)
      -------
    → P ⇔ Q
  ⇔-intro PQ QP = PQ , QP

  ⇔-elim : ∀{P Q : Set}
    → P ⇔ Q
      -----------------
    → (P → Q) × (Q → P)
  ⇔-elim PQ = PQ

  ⇔-to : ∀{P Q : Set}
    → P ⇔ Q
      -------
    → (P → Q)
  ⇔-to PQ = proj₁ PQ

  ⇔-fro : ∀{P Q : Set}
    → P ⇔ Q
      -------
    → (Q → P)
  ⇔-fro PQ = proj₂ PQ

  ⇔-refl : ∀{P Q : Set}
    → P ≡ Q
      ------
    → P ⇔ Q
  ⇔-refl refl = (λ x → x) , (λ x → x)

  ⇔-sym : ∀{P Q : Set}
    → P ⇔ Q
      ------
    → Q ⇔ P
  ⇔-sym PQ = (proj₂ PQ) , (proj₁ PQ)

  ⇔-trans : ∀{P Q R : Set}
    → P ⇔ Q
    → Q ⇔ R
      ------
    → P ⇔ R
  ⇔-trans PQ QR =
      (λ z → proj₁ QR (proj₁ PQ z)) , (λ z → proj₂ PQ (proj₂ QR z))  

infixr 2 _⇔⟨_⟩_
infix  3 _QED
  
_⇔⟨_⟩_ : 
    (P : Set)
  → ∀{Q} → P ⇔ Q
  → ∀{R} → Q ⇔ R
    -------------
  → P ⇔ R
P ⇔⟨ PQ ⟩ QR = ⇔-trans PQ QR

_QED :
    (P : Set)
    ---------
  → P ⇔ P
P QED = ⇔-refl refl

abstract
  ×-cong-⇔ : ∀{S S′ T T′}
     → S ⇔ S′
     → T ⇔ T′
       -------------------
     → (S × T) ⇔ (S′ × T′)
  ×-cong-⇔ SS′ TT′ = (λ x → (proj₁ SS′ (proj₁ x)) , (proj₁ TT′ (proj₂ x)))
                    , (λ x → (proj₂ SS′ (proj₁ x)) , (proj₂ TT′ (proj₂ x)))
