{-# OPTIONS --without-K --rewriting #-}

{-
 Based on the development of Logical step-indexed logical relation
 by Philip Wadler (June 1, 2022)

 Also based on "An Indexed Model of Recursive Types"
 by Appel and McAllester.
-}
module rewriting.examples.StepIndexedLogic2 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat
   using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_; z≤n; s≤s; _≤′_; ≤′-step)
open import Data.Nat.Properties
   using (≤-refl; ≤-antisym; ≤-trans; ≤-step; s≤s-injective; ≤⇒≤′; ≤′⇒≤; n≤1+n; <⇒≤)
open import Data.Product
   using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import rewriting.examples.IfAndOnlyIf

downClosed : (ℕ → Set) → Set
downClosed P = ∀ n → P n → ∀ k → k ≤ n → P k

downClosedᵖ : ∀{A : Set} → (A → ℕ → Set) → Set
downClosedᵖ P = ∀ v → downClosed (P v)

Setₒ : Set₁
Setₒ = ℕ → Set

⊥ₒ : Setₒ
⊥ₒ zero     =  ⊤
⊥ₒ (suc n)  =  ⊥

⊤ₒ : Setₒ
⊤ₒ n  =  ⊤

infixr 7 _×ₒ_
_×ₒ_ : Setₒ → Setₒ → Setₒ
(P ×ₒ Q) n  = (P n) × (Q n)

infixr 7 _⊎ₒ_
_⊎ₒ_ : Setₒ → Setₒ → Setₒ
(P ⊎ₒ Q) n  = (P n) ⊎ (Q n)

infixr 6 _→ₒ_
_→ₒ_ : Setₒ → Setₒ → Setₒ
(P →ₒ Q) n  = ∀ k → k ≤ n → P k → Q k

∀ₒ : ∀{A} → (A → Setₒ) → Setₒ
∀ₒ {A} F n = ∀ (v : A) → F v n

infixr 8 _ₒ
_ₒ  : Set → Setₒ
(p ₒ) zero = ⊤
(p ₒ) (suc n) = p

▷ₒ_ : Setₒ → Setₒ
(▷ₒ P) n =  ∀ k → k < n → P k

record Setᵒ : Set₁ where
  field
    # : Setₒ
    down : downClosed #
    tz : # 0
open Setᵒ

⊥ᵒ : Setᵒ
⊥ᵒ = record { # = ⊥ₒ
            ; down = λ { zero ⊥n .zero z≤n → tt}
            ; tz = tt
            }

⊤ᵒ : Setᵒ
⊤ᵒ = record { # = ⊤ₒ
            ; down = λ n _ k _ → tt
            ; tz = tt
            }

infixr 7 _×ᵒ_
_×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ×ᵒ Q = record { # = # P ×ₒ # Q
                ; down = λ k (Pk , Qk) j j≤k →
                          (down P k Pk j j≤k) , (down Q k Qk j j≤k)
                ; tz = (tz P) , (tz Q)
                }

infixr 7 _⊎ᵒ_
_⊎ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P ⊎ᵒ Q = record { # = # P ⊎ₒ # Q
                ; down = λ { k (inj₁ Pk) j j≤k → inj₁ (down P k Pk j j≤k)
                           ; k (inj₂ Qk) j j≤k → inj₂ (down Q k Qk j j≤k)}
                ; tz = inj₁ (tz P)
                }

infixr 6 _→ᵒ_
_→ᵒ_ : Setᵒ → Setᵒ → Setᵒ
P →ᵒ Q = record { # = λ k → ∀ j → j ≤ k → # P j → # Q j
                ; down = λ k P→Q j j≤k i i≤j Pi → P→Q i (≤-trans i≤j j≤k) Pi
                ; tz = λ { .zero z≤n _ → tz Q}
                }

infixr 8 _ᵒ
_ᵒ  : Set → Setᵒ
S ᵒ = record { # = λ { zero → ⊤ ; (suc k) → S}
             ; down = λ { k Sk zero j≤k → tt
                        ; (suc k) Sk (suc j) j≤k → Sk}
             ; tz = tt }

infixr 8 ▷ᵒ_
▷ᵒ_ : Setᵒ → Setᵒ
▷ᵒ P = record { # = λ { zero → ⊤ ; (suc k) → # P k}
              ; down = λ { k ▷Pk zero j≤k → tt
                         ; (suc k) ▷Pk (suc j) (s≤s j≤k) → down P k ▷Pk j j≤k}
              ; tz = tt
              }

Predₒ : Set → Set₁
Predₒ A = A → ℕ → Set

⊤ₚ : ∀{A} → Predₒ A
⊤ₚ x = ⊤ₒ

⊥ₚ : ∀{A} → Predₒ A
⊥ₚ x = ⊥ₒ

infixr 7 _×ₚ_
_×ₚ_ : ∀{A} → Predₒ A → Predₒ A → Predₒ A
(P ×ₚ Q) v  =  (P v) ×ₒ (Q v)

infixr 7 _⊎ₚ_
_⊎ₚ_ : ∀{A} → Predₒ A → Predₒ A → Predₒ A
(P ⊎ₚ Q) v  =  (P v) ⊎ₒ (Q v)

infixr 6 _→ₚ_
_→ₚ_ : ∀{A} → Predₒ A → Predₒ A → Predₒ A
(P →ₚ Q) v = P v →ₒ Q v

▷ₚ : ∀{A} → Predₒ A → Predₒ A
▷ₚ P v = ▷ₒ (P v)

record Predᵒ (A : Set) : Set₁ where
  field
    # : A → ℕ → Set -- or Set → Setᵒ?
    down  : downClosedᵖ #
    tz : ∀ v → # v 0
open Predᵒ

∀ᵒ : ∀{A} → Predᵒ A → Setᵒ
∀ᵒ{A} P = record { # = λ k → ∀ v → # P v k
                 ; down = λ k ∀Pk j j≤k v → down P v k (∀Pk v) j j≤k
                 ; tz = tz P
                 }

↓ᵒ : ℕ → Setᵒ → Setᵒ
↓ᵒ k S = record { # = λ j → (j ≤ k) × (# S j)  -- j < k in Appel and McAllester
                ; down = λ n (n<k , Sn) j j≤n →
                             (≤-trans j≤n n<k)
                           , (down S n Sn j j≤n)
                ; tz = z≤n , (tz S)            -- need j ≤ k to prove tz
                }

apply : ∀{A} → Predᵒ A → A → Setᵒ
apply P v = record { # = λ j → # P v j
                   ; down = down P v
                   ; tz = tz P v
                   }

infixr 6 _→ᵖ_
_→ᵖ_ : ∀{A} → Predᵒ A → Predᵒ A → Predᵒ A
P →ᵖ Q = record { # = λ v → # (apply P v →ᵒ apply Q v)
                ; down = λ v → down (apply P v →ᵒ apply Q v)
                ; tz = λ v → tz (apply P v →ᵒ apply Q v)
                }

↓ᵖ : ℕ → ∀{A} → Predᵒ A → Predᵒ A
↓ᵖ k P = record { # = λ v → # (↓ᵒ k (apply P v))
                ; down = λ v → down (↓ᵒ k (apply P v))
                ; tz = λ v → z≤n , (tz P v)
                }

iter : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → (A → A)
iter zero    F  =  id
iter (suc n) F  =  F ∘ iter n F


{-----  Reasoning about Equality on Step Indexed Sets  ---------}

infix 4 _≡ₒ_
_≡ₒ_ : Setₒ → Setₒ → Set
S ≡ₒ T = ∀ i → S i ⇔ T i

≡ₒ-refl : ∀{S T : Setₒ}
  → S ≡ T
  → S ≡ₒ T
≡ₒ-refl refl i = (λ x → x) , (λ x → x)

≡ₒ-sym : ∀{S T : Setₒ}
  → S ≡ₒ T
  → T ≡ₒ S
≡ₒ-sym ST i = (proj₂ (ST i)) , (proj₁ (ST i))

≡ₒ-trans : ∀{S T R : Setₒ}
  → S ≡ₒ T
  → T ≡ₒ R
  → S ≡ₒ R
≡ₒ-trans ST TR i = (λ z → proj₁ (TR i) (proj₁ (ST i) z))
                 , (λ z → proj₂ (ST i) (proj₂ (TR i) z))

infixr 2 _≡ₒ⟨_⟩_
infix  3 _QEDₒ
  
_≡ₒ⟨_⟩_ : 
    (P : Setₒ)
   {Q : Setₒ}
  → P ≡ₒ Q
  → {R : Setₒ}
  → Q ≡ₒ R
  → P ≡ₒ R
P ≡ₒ⟨ P≡Q ⟩ Q≡R = ≡ₒ-trans P≡Q Q≡R

_QEDₒ :
    (P : Setₒ)
  → P ≡ₒ P
P QEDₒ = ≡ₒ-refl refl

example : ∀{P Q : Setᵒ} → # (P ×ᵒ Q) ≡ₒ # (Q ×ᵒ P)
example {P}{Q} = 
  # (P ×ᵒ Q)          ≡ₒ⟨ (λ i → (λ {(Pi , Qi) → Qi , Pi})
                               , (λ {(Qi , Pi) → Pi , Qi})) ⟩
  # (Q ×ᵒ P)
  QEDₒ


{-----  Reasoning about Equality on Step Indexed Predicates  ---------}

infix 2 _≡ₚ_
_≡ₚ_ : ∀{A} → Predₒ A → Predₒ A → Set
P ≡ₚ Q = ∀ v → P v ≡ₒ Q v

≡ₚ-refl : ∀{A}{P Q : Predₒ A}
  → P ≡ Q
  → P ≡ₚ Q
≡ₚ-refl refl x = ≡ₒ-refl refl

≡ₚ-sym : ∀{A}{P Q : Predₒ A}
  → P ≡ₚ Q
  → Q ≡ₚ P
≡ₚ-sym PQ x = ≡ₒ-sym (PQ x)
  
≡ₚ-trans : ∀{A : Set}{P Q R : Predₒ A}
  → P ≡ₚ Q
  → Q ≡ₚ R
  → P ≡ₚ R
≡ₚ-trans{R} PQ QR x = ≡ₒ-trans (PQ x) (QR x)

infixr 2 _≡ₚ⟨_⟩_
infix  3 _QEDᵖ
  
_≡ₚ⟨_⟩_ : ∀{A}
  → (P : Predₒ A)
  → ∀{Q} → P ≡ₚ Q
  → ∀{R} → Q ≡ₚ R
  → P ≡ₚ R
P ≡ₚ⟨ P≡Q ⟩ Q≡R = ≡ₚ-trans P≡Q Q≡R

_QEDᵖ : ∀{A}
  → (P : Predₒ A)
  → P ≡ₚ P
P QEDᵖ = ≡ₚ-refl refl

cong-→ᵖ : ∀{A}{P P′ Q Q′ : Predₒ A}
   → P ≡ₚ P′
   → Q ≡ₚ Q′
   → (P →ₚ Q)  ≡ₚ  (P′ →ₚ Q′)
cong-→ᵖ PP′ QQ′ v k = (λ P→Q j j<k P′vj → let Pvj = proj₂ (PP′ v j) P′vj in
                                          let Qvj = P→Q j j<k Pvj in
                                          let Q′vj = proj₁ (QQ′ v j) Qvj in
                                          Q′vj)
                   , (λ P′→Q′ j j<k Pvj → let P′vj = proj₁ (PP′ v j) Pvj in
                                          let Q′vj = P′→Q′ j j<k P′vj in
                                          let Qvj = proj₂ (QQ′ v j) Q′vj in
                                          Qvj)

{------------ Continuous and Wellfounded Functions on Step Indexed Predicates -}



{------------ Functions on Step Indexed Predicates -----}

congᵖ : ∀{A}{B} (F : Predᵒ A → Predᵒ B) → Set₁
congᵖ F = ∀ P Q → # P ≡ₚ # Q → #(F P) ≡ₚ #(F Q)

continuous : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
continuous F = ∀ P k → #(↓ᵖ k (F P)) ≡ₚ #(↓ᵖ k (F (↓ᵖ k P)))

wellfounded : ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
wellfounded F = ∀ P k → #(↓ᵖ (suc k) (F P)) ≡ₚ #(↓ᵖ (suc k) (F (↓ᵖ k P)))

cong-↓ : ∀{A}
    (k : ℕ)
  → congᵖ{A}{A} (↓ᵖ k)
cong-↓ k P Q PQ x i = (λ { (i≤k , Pxi) → i≤k , proj₁ (PQ x i) Pxi})
                   , (λ { (i≤k , Qxi) → i≤k , proj₂ (PQ x i) Qxi})
                
lemma17 : ∀{A}
     (P : Predᵒ A)
   → (k : ℕ)
   → #(↓ᵖ k (↓ᵖ (suc k) P)) ≡ₚ #(↓ᵖ k P)
lemma17{A} P k x i =
    (λ { (fst , snd) → fst , proj₂ snd})
    , λ { (fst , snd) → fst , ((≤-trans fst (n≤1+n k)) , snd)}


↓-zero : ∀{A}
   → (P : Predᵒ A)
   → (Q : Predᵒ A)
   → #(↓ᵖ 0 P) ≡ₚ #(↓ᵖ 0 Q)
↓-zero P Q v i =
     (λ {(z≤n , Pvi) → z≤n , (tz Q v)})
   , λ {(z≤n , Qvi) → z≤n , (tz P v)}

wellfounded⇒continuous : ∀{A}{B}
   → (F : Predᵒ A → Predᵒ B)
   → wellfounded F
   → congᵖ F
   → continuous F
wellfounded⇒continuous F wfF congF P zero = ↓-zero (F P) (F (↓ᵖ zero P))
wellfounded⇒continuous F wfF congF P (suc k) =
    #(↓ᵖ (suc k) (F P))                       ≡ₚ⟨ wfF _ k ⟩
    #(↓ᵖ (suc k) (F (↓ᵖ k P)))
             ≡ₚ⟨ cong-↓ (suc k) (F (↓ᵖ k P)) (F (↓ᵖ k (↓ᵖ (suc k) P)))
                 (congF ((↓ᵖ k P)) ((↓ᵖ k (↓ᵖ (suc k) P))) (≡ₚ-sym (lemma17 P k))) ⟩
    #(↓ᵖ (suc k) (F (↓ᵖ k (↓ᵖ (suc k) P))))   ≡ₚ⟨ ≡ₚ-sym (wfF _ k) ⟩
    #(↓ᵖ (suc k) (F (↓ᵖ (suc k) P)))
    QEDᵖ

data Kind : Set where
  Continuous : Kind
  Wellfounded : Kind

choose : Kind → Kind → Kind
choose Continuous Continuous = Continuous
choose Continuous Wellfounded = Continuous
choose Wellfounded Continuous = Continuous
choose Wellfounded Wellfounded = Wellfounded

goodness : Kind → ∀{A}{B} → (Predᵒ A → Predᵒ B) → Set₁
goodness Continuous F = continuous F
goodness Wellfounded F = wellfounded F

record Fun (A B : Set) (κ : Kind)
       : Set₁ where
  field
    fun : Predᵒ A → Predᵒ B
    good : goodness κ fun
    congr : congᵖ fun
open Fun public


down-fun : ∀{A} (P Q : Predᵒ A){k}
   → #(↓ᵖ k (P →ᵖ Q)) ≡ₚ #(↓ᵖ k ((↓ᵖ k P) →ᵖ (↓ᵖ k Q)))
down-fun {A} P Q {k} x i =
    (λ {(i≤k , PQxi) → i≤k , (λ {j j≤i (j≤k , Pxj) → j≤k , (PQxi j j≤i Pxj)})})
  , (λ {(i≤k , P→Q) →
      i≤k , (λ j j≤i Pxj →
                 let ↓kQ = P→Q j j≤i ((≤-trans j≤i i≤k) , Pxj) in
                  proj₂ ↓kQ)})

continuous-→ : ∀{A}{B}(F G : Predᵒ A → Predᵒ B)
   → continuous F
   → continuous G
   → continuous (λ P → F P →ᵖ G P)
continuous-→ {A}{B} F G neF neG P k =
    #(↓ᵖ k (F P →ᵖ G P))                              ≡ₚ⟨ down-fun (F P) (G P) ⟩
    #(↓ᵖ k (↓ᵖ k (F P) →ᵖ ↓ᵖ k (G P)))
                           ≡ₚ⟨ cong-↓ k (↓ᵖ k (F P) →ᵖ ↓ᵖ k (G P))
                                       (↓ᵖ k (F (↓ᵖ k P)) →ᵖ ↓ᵖ k (G (↓ᵖ k P)))
                                       (cong-→ᵖ (neF _ k) (neG _ k)) ⟩
    #(↓ᵖ k (↓ᵖ k (F (↓ᵖ k P)) →ᵖ ↓ᵖ k (G (↓ᵖ k P))))
                               ≡ₚ⟨ ≡ₚ-sym (down-fun (F (↓ᵖ k P)) (G (↓ᵖ k P))) ⟩
    #(↓ᵖ k (F (↓ᵖ k P) →ᵖ G (↓ᵖ k P)))
    QEDᵖ

wellfounded-→ : ∀{A}{B}(F G : Predᵒ A → Predᵒ B)
   → wellfounded F
   → wellfounded G
   → wellfounded (λ P → F P →ᵖ G P)
wellfounded-→ {A}{B} F G wfF wfG P k =
    #(↓ᵖ (suc k) (F P →ᵖ G P))                        ≡ₚ⟨ down-fun (F P) (G P) ⟩
    #(↓ᵖ (suc k) (↓ᵖ (suc k) (F P) →ᵖ ↓ᵖ (suc k) (G P)))
                ≡ₚ⟨ cong-↓ (suc k)
                          ((↓ᵖ (suc k) (F P) →ᵖ ↓ᵖ (suc k) (G P)))
                          ((↓ᵖ (suc k) (F (↓ᵖ k P)) →ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P))))
                          (cong-→ᵖ (wfF _ k) (wfG _ k)) ⟩
    #(↓ᵖ (suc k) (↓ᵖ (suc k) (F (↓ᵖ k P)) →ᵖ ↓ᵖ (suc k) (G (↓ᵖ k P))))
                               ≡ₚ⟨ ≡ₚ-sym (down-fun (F (↓ᵖ k P)) (G (↓ᵖ k P))) ⟩
    #(↓ᵖ (suc k) (F (↓ᵖ k P) →ᵖ G (↓ᵖ k P)))
    QEDᵖ

cong-→ : ∀{A}{B}
     (F G : Predᵒ A → Predᵒ B)
   → congᵖ F
   → congᵖ G
   → congᵖ (λ P → F P →ᵖ G P)
cong-→ F G congF congG P Q PQ b i =
    (λ FP→GP j j≤i FQbj →
       let FP≡FQ = congF P Q PQ b j in
       let GP≡GQ = congG P Q PQ b j in
       let GPbj = FP→GP j j≤i (proj₂ FP≡FQ FQbj) in
       let GQbj = proj₁ GP≡GQ GPbj in
       GQbj)
  , (λ FQ→GQ j j≤i FPbj →
      let FP≡FQ = congF P Q PQ b j in
      let GP≡GQ = congG P Q PQ b j in
      let GQbj = FQ→GQ j j≤i (proj₁ FP≡FQ FPbj) in
      let GPbj = proj₂ GP≡GQ GQbj in
      GPbj)

infixr 6 _→ᶠ_
_→ᶠ_ : ∀{A B}{kF kG}
   → Fun A B kF
   → Fun A B kG
   → Fun A B (choose kF kG)
_→ᶠ_ {A}{B}{kF}{kG} F G =
         record { fun = λ P → fun F P →ᵖ fun G P
                ; good = goodness-→ kF kG (fun F) (fun G) (good F) (congr F)
                               (good G) (congr G)
                ; congr = cong-→ (fun F) (fun G) (congr F) (congr G) }
    where
    goodness-→ : ∀ (kf kg : Kind) {A}{B}(F G : Predᵒ A → Predᵒ B)
       → goodness kf F
       → congᵖ F
       → goodness kg G
       → congᵖ G
       → goodness (choose kf kg) (λ P → F P →ᵖ G P)
    goodness-→ Continuous Continuous F G gf congF gg congG  =
        continuous-→ F G gf gg
    goodness-→ Continuous Wellfounded F G gf congF gg congG =
        continuous-→ F G gf (wellfounded⇒continuous G gg congG)
    goodness-→ Wellfounded Continuous F G gf congF gg congG =
        continuous-→ F G (wellfounded⇒continuous F gf congF) gg
    goodness-→ Wellfounded Wellfounded F G gf congF gg congG =
        wellfounded-→ F G gf gg
                

-- μᵖ : ∀ {A} → Fun A A → Predᵒ A
-- μᵖ = ?
