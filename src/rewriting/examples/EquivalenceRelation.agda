{-# OPTIONS --without-K #-}

module rewriting.examples.EquivalenceRelation where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)

record EquivalenceRelation {ℓ ℓ′ : Level} (A : Set ℓ) : Set (ℓ ⊔ lsuc ℓ′) where
  field
    _⩦_ : A → A → Set ℓ′
    ⩦-refl : ∀{a b : A} → a ≡ b → a ⩦ b
    ⩦-sym : ∀{a b : A} → a ⩦ b → b ⩦ a
    ⩦-trans : ∀{a b c : A} → a ⩦ b → b ⩦ c → a ⩦ c

open EquivalenceRelation {{...}} public

infixr 0 _⩦⟨_⟩_
infix  1 _∎
  
_⩦⟨_⟩_ : ∀{ℓ ℓ′}{A : Set ℓ}{{_ : EquivalenceRelation{ℓ}{ℓ′} A}}
     (P : A)
     {Q : A} → P ⩦ Q
   → {R : A} → Q ⩦ R
   → P ⩦ R
P ⩦⟨ P⩦Q ⟩ Q⩦R = ⩦-trans P⩦Q Q⩦R

_∎ : ∀{ℓ ℓ′}{A : Set ℓ}{{_ : EquivalenceRelation{ℓ}{ℓ′} A}}
    (P : A)
   → P ⩦ P
P ∎ = ⩦-refl refl

instance
  PropEq : ∀{A : Set} → EquivalenceRelation A
  PropEq {A} = record { _⩦_ = _≡_
                      ; ⩦-refl = λ {refl → refl}
                      ; ⩦-sym = sym
                      ; ⩦-trans = trans
                      }

infixr 2 _⇔_
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

instance
  IffEq : EquivalenceRelation Set
  IffEq = record { _⩦_ = λ P Q → P ⇔ Q
                 ; ⩦-refl = λ {refl → (λ x → x) , λ x → x}
                 ; ⩦-sym = λ {(ab , ba) → ba , ab}
                 ; ⩦-trans = λ {(ab , ba) (bc , cb) →
                               (λ x → bc (ab x)) , (λ x → ba (cb x))}
                 }

module Examples where

  open import Data.Nat
  
  X₁ : (1 + 1 + 1) ⩦ 3
  X₁ = 1 + (1 + 1) ⩦⟨ refl ⟩
       1 + 2       ⩦⟨ refl ⟩  
       3           ∎

  open import Data.Unit using (tt; ⊤)
  
  X₂ : ⊤ ⇔ ⊤ × ⊤ × ⊤
  X₂ = ⊤              ⩦⟨ (λ _ → tt , tt) , (λ _ → tt) ⟩
       ⊤ × ⊤          ⩦⟨ (λ _ → tt , tt , tt) , (λ _ → tt , tt) ⟩
       ⊤ × ⊤ × ⊤      ∎
