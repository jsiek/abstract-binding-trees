{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}
{-
   Cast Calculus partly based on a version 
   by Jeremy, Phil Wadler, and Peter Thiemann.
-}

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var

module rewriting.examples.Cast where

{- Base types -}

data Base : Set where
  ′ℕ : Base
  ′𝔹 : Base

_≡$?_ : (ι : Base) → (ι′ : Base) → Dec (ι ≡ ι′)
′ℕ  ≡$? ′ℕ  =  yes refl
′ℕ  ≡$? ′𝔹  =  no (λ ())
′𝔹  ≡$? ′ℕ  =  no (λ ())
′𝔹  ≡$? ′𝔹  =  yes refl

{- Interpretation of base types into Agda types. -}

rep : Base → Set 
rep ′ℕ  =  ℕ
rep ′𝔹  =  𝔹

{- Types -}

infixr 7 _⇒_
infix  8 $ₜ_

data Type : Set where
  ★ : Type
  $ₜ_ : (ι : Base) → Type
  _⇒_ : (A : Type) → (B : Type) → Type

size : Type → ℕ
size ★ = 0
size ($ₜ ι) = 0
size (A ⇒ B) = suc (size A ⊔ size B)

{- Ground types -}

infix  8 $ᵍ_

data Ground : Type → Set where
  $ᵍ_  :
       (ι : Base) 
       ------------
     → Ground ($ₜ ι)

  ★⇒★ :
       --------------
       Ground (★ ⇒ ★)

_≡ᵍ_ : ∀{G H} (g : Ground G) (h : Ground H) → Dec (G ≡ H)
($ᵍ ι) ≡ᵍ ($ᵍ ι′)
    with ι ≡$? ι′
... | yes refl = yes refl
... | no neq = no λ { refl → ⊥-elim (neq refl)}
($ᵍ ι) ≡ᵍ ★⇒★ = no λ ()
★⇒★ ≡ᵍ ($ᵍ ι) = no λ ()
★⇒★ ≡ᵍ ★⇒★ = yes refl

data GroundOf : Type → Type → Set where
  gnd-base : ∀{ι} → GroundOf ($ₜ ι) ($ₜ ι)
  gnd-fun : ∀{A B} → GroundOf (A ⇒ B) (★ ⇒ ★)

{- Terms -}

data Op : Set where
  op-lam : Op
  op-app : Op
  op-lit : ∀{ι : Base} → rep ι → Op
  op-inject : {A : Type} → Ground A → Op
  op-project : {A : Type} → Ground A → Op
  op-blame : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit n) = []
sig (op-inject g) = ■ ∷ []
sig (op-project h) = ■ ∷ []
sig (op-blame) = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $ k = (op-lit k) ⦅ nil ⦆
pattern _⟨_!⟩ M g = (op-inject g) ⦅ cons (ast M) nil ⦆
pattern _⟨_?⟩ M g = (op-project g) ⦅ cons (ast M) nil ⦆
pattern blame = (op-blame) ⦅ nil ⦆

data Value : Term → Set where
  ƛ̬_ : (N : Term) → Value (ƛ N)
  $̬_ : ∀{ι} → (k : rep ι) → Value ($ k)
  _〈_〉 : ∀{V G} → Value V → (g : Ground G) → Value (V ⟨ g !⟩)

value : ∀ {V : Term}
  → (v : Value V)
    -------------
  → Term
value {V = V} v  =  V  

open Renaming

rename-val : ∀ {V : Term}
  → (ρ : Rename)
  → Value V
    ------------------
  → Value (rename ρ V)
rename-val ρ (ƛ̬ N)    =  ƛ̬ (rename (extr ρ) N)
rename-val ρ ($̬ k)    =  $̬ k
rename-val ρ (V 〈 g 〉)  =  (rename-val ρ V) 〈 g 〉

sub-val : ∀ {V}
  → (σ : Subst)
  → Value V
  → Value (⟪ σ ⟫ V)
sub-val σ (ƛ̬ N) = ƛ̬ ⟪ ext σ ⟫ N
sub-val σ ($̬ k) = $̬ k
sub-val σ (V 〈 g 〉)  =  (sub-val σ V) 〈 g 〉

{----------------- Type System ------------------------}

{- Consistency -}
data _∼_ : Type → Type → Set where
  ★∼ : ∀{A}
       -----
     → ★ ∼ A

  ∼★ : ∀{A}
       -----
     → A ∼ ★

  ∼-base : ∀{ι}
       --------------
     → ($ₜ ι) ∼ ($ₜ ι)

  ∼-fun : ∀{A B A′ B′}
     → A ∼ A′
     → B ∼ B′
       -------------------
     → (A ⇒ B) ∼ (A′ ⇒ B′)


infix 3 _⊢_⦂_

data _⊢_⦂_ : List Type → Term → Type → Set

data _⊢_⦂_ where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  ⊢$ : ∀ {Γ} (ι : Base) {k : rep ι}
      -----------------
    → Γ ⊢ $ k ⦂ ($ₜ ι)

  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ (A ⇒ B)
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢ƛ : ∀ {Γ N A B}
    → (A ∷ Γ) ⊢ N ⦂ B
      -----------------
    → Γ ⊢ ƛ N ⦂ (A ⇒ B)

  ⊢⟨!⟩ : ∀{Γ M G}
    → Γ ⊢ M ⦂ G
    → (g : Ground G)
      --------------------
    → Γ ⊢ M ⟨ g !⟩ ⦂ ★

  ⊢⟨?⟩ : ∀{Γ M H}
    → Γ ⊢ M ⦂ ★
    → (h : Ground H)
      --------------------
    → Γ ⊢ M ⟨ h ?⟩ ⦂ H

  ⊢blame : ∀{Γ A}
      ---------------
    → Γ ⊢ blame ⦂ A

infix  6 □·_
infix  6 _·□
infix  6 □⟨_!⟩
infix  6 □⟨_?⟩

data Frame : Set where

  □·_ : 
      (M : Term)
      ----------
    → Frame

  _·□ : ∀ {V : Term}
    → (v : Value V)
      -------------
    → Frame

  □⟨_!⟩ : 
      {G : Type}
    → (g : Ground G)
      -----
    → Frame

  □⟨_?⟩ : 
      {H : Type}
    → (h : Ground H)
      -----
    → Frame

{- The plug function inserts an expression into the hole of a frame. -}

_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
(□⟨ g !⟩) ⟦ M ⟧  =  M ⟨ g !⟩
(□⟨ h ?⟩) ⟦ M ⟧  =  M ⟨ h ?⟩

{- Reduction -}

infix 2 _—→_
data _—→_ : Term → Term → Set where

  ξξ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ M ⟧
    → N′ ≡ F ⟦ N ⟧
    → M —→ N
      --------
    → M′ —→ N′

  ξξ-blame : ∀ {M′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ blame ⟧
      ------------------
    → M′ —→ blame

  β : ∀ {N : Term} {W : Term}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  collapse : ∀{G} {M V : Term}
    → Value V
    → (g h : Ground G)
    → M ≡ V ⟨ g !⟩
      ---------------------------
    → M ⟨ h ?⟩ —→ V

  collide  : ∀{G H} {M V : Term}
    → Value V
    → (g : Ground G)
    → (h : Ground H)
    → G ≢ H
    → M ≡ V ⟨ g !⟩
      ---------------------------------
    → M ⟨ h ?⟩ —→ blame

pattern ξ F M—→N = ξξ F refl refl M—→N
pattern ξ-blame F = ξξ-blame F refl

{- Reflexive and transitive closure of reduction -}

infixr 1 _++_
--infix  1 begin_
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_
infix  3 _END

data _—↠_ : Term → Term → Set where
  _END : (M : Term)
      ---------
    → M —↠ M

  _—→⟨_⟩_ : (L : Term) {M N : Term}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

--begin_ : ∀ {M N : Term} → (M —↠ N) → (M —↠ N)
--begin M—↠N = M—↠N

{- Convenience function to build a sequence of length one. -}

unit : ∀ {M N : Term} → (M —→ N) → (M —↠ N)
unit {M = M} {N = N} M—→N  =  M —→⟨ M—→N ⟩ (N END)


{- Apply ξ to each element of a sequence -}

ξ* : ∀ {M N : Term} → (F : Frame) → M —↠ N → F ⟦ M ⟧ —↠ F ⟦ N ⟧
ξ* F (M END) = F ⟦ M ⟧ END
ξ* F (L —→⟨ L—→M ⟩ M—↠N) = (F ⟦ L ⟧ —→⟨ ξ F L—→M ⟩ ξ* F M—↠N)

{- Concatenate two sequences. -}

_++_ : ∀ {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
(M END) ++ M—↠N                =  M—↠N
(L —→⟨ L—→M ⟩ M—↠N) ++ N—↠P  =  L —→⟨ L—→M ⟩ (M—↠N ++ N—↠P)

{- Alternative notation for sequence concatenation. -}

_—↠⟨_⟩_ : (L : Term) {M N : Term}
  → L —↠ M
  → M —↠ N
    ---------
  → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N  =  L—↠M ++ M—↠N

len : ∀{M N : Term} → (M→N : M —↠ N) → ℕ
len (_ END) = 0
len (_ —→⟨ x ⟩ red) = suc (len red)

blame-not-value : ∀{V} → Value V → V ≡ blame → ⊥
blame-not-value {.blame} () refl

value-irreducible : ∀ {V M : Term} → Value V → ¬ (V —→ M)
value-irreducible v V—→M = nope V—→M v
   where
   nope : ∀ {V M : Term} → V —→ M → Value V → ⊥
   nope (ξξ (□· M) () x₁ V→M) (ƛ̬ N)
   nope (ξξ (v ·□) () x₁ V→M) (ƛ̬ N)
   nope (ξξ □⟨ g !⟩ () x₁ V→M) (ƛ̬ N)
   nope (ξξ □⟨ h ?⟩ () x₁ V→M) (ƛ̬ N)
   nope (ξξ-blame (□· M) ()) (ƛ̬ N)
   nope (ξξ-blame (v ·□) ()) (ƛ̬ N)
   nope (ξξ-blame □⟨ g !⟩ ()) (ƛ̬ N)
   nope (ξξ-blame □⟨ h ?⟩ ()) (ƛ̬ N)
   nope (ξξ (□· M) () x₁ V→M) ($̬ k)
   nope (ξξ (v ·□) () x₁ V→M) ($̬ k)
   nope (ξξ □⟨ g !⟩ () x₁ V→M) ($̬ k)
   nope (ξξ □⟨ h ?⟩ () x₁ V→M) ($̬ k)
   nope (ξξ-blame (□· M) ()) ($̬ k)
   nope (ξξ-blame (v ·□) ()) ($̬ k)
   nope (ξξ-blame □⟨ g !⟩ ()) ($̬ k)
   nope (ξξ-blame □⟨ h ?⟩ ()) ($̬ k)
   nope (ξ □⟨ g !⟩ V→M) (v 〈 g 〉) = nope V→M v
   nope (ξ-blame □⟨ _ !⟩) (() 〈 g 〉)

value—↠ : ∀{V N : Term}
    → Value V
    → V —↠ N
    → N ≡ V
value—↠ v (_ END) = refl
value—↠ v (_ —→⟨ V—→M ⟩ M—↠N) = ⊥-elim (value-irreducible v V—→M)

blame—↠ : ∀{N}
   → blame —↠ N
   → N ≡ blame
blame—↠ {.blame} (.blame END) = refl
blame—↠ {N} (.blame —→⟨ ξξ (□· M) () x₁ x₂ ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ (v ·□) () x₁ x₂ ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ □⟨ g !⟩ () x₁ x₂ ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ □⟨ h ?⟩ () x₁ x₂ ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ-blame (□· M) () ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ-blame (v ·□) () ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ-blame □⟨ g !⟩ () ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ-blame □⟨ h ?⟩ () ⟩ red)

app-multi-inv : ∀{L M N}
  → (r1 : L · M —↠ N)
  → (∃[ L′ ] (Σ[ r2 ∈ (L —↠ L′) ] (N ≡ L′ · M × len r1 ≡ len r2)))
    ⊎ (∃[ V ] ∃[ M′ ] Σ[ r2 ∈ (L —↠ V) ] (Value V × Σ[ r3 ∈ (M —↠ M′) ]
        (N ≡ V · M′ × len r1 ≡ len r2 + len r3)))
    ⊎ (∃[ V ] ∃[ W ] Σ[ r2 ∈ (L —↠ V) ] (Value V × Σ[ r3 ∈ (M —↠ W) ]
        (Value W × Σ[ r4 ∈ (V · W —↠ N) ] len r1 ≡ len r2 + len r3 + len r4)))
app-multi-inv = {!!}

inject-multi-inv : ∀{M N}{G}{g : Ground G}
  → (red : M ⟨ g !⟩ —↠ N)
  → (∃[ M′ ] Σ[ r1 ∈ M —↠ M′ ] (N ≡ M′ ⟨ g !⟩ × len r1 ≡ len red))
    ⊎ (∃[ V ] Σ[ r1 ∈ M —↠ V ] Value V × Σ[ r2 ∈ V ⟨ g !⟩ —↠ N ] len red ≡ len r1 + len r2)
    ⊎ N ≡ blame
inject-multi-inv {M}{g = g} (.(_ ⟨ _ !⟩) END) = inj₁ (M , (_ END) , refl , refl)
inject-multi-inv (.(_ ⟨ _ !⟩) —→⟨ ξξ □⟨ g !⟩ refl refl r1 ⟩ r2)
    with inject-multi-inv r2
... | inj₁ (M′ , →M′ , eq , eqlen) = inj₁ (_ , (_ —→⟨ r1 ⟩ →M′) , eq , cong suc eqlen)
... | inj₂ (inj₁ (V , →V , v , →N , eqlen)) = inj₂ (inj₁ (_ , (_ —→⟨ r1 ⟩ →V) , v , →N , cong suc eqlen))
... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
inject-multi-inv (.(_ ⟨ _ !⟩) —→⟨ ξξ-blame □⟨ g !⟩ x ⟩ red)
    with blame—↠ red
... | refl = inj₂ (inj₂ refl)

project-multi-inv : ∀{M N}{G}{g : Ground G}
  → (red : M ⟨ g ?⟩ —↠ N)
  → (∃[ M′ ] (M —↠ M′) × N ≡ M′ ⟨ g ?⟩)
    ⊎ (∃[ V ] (M —↠ V) × Value V × (V ⟨ g ?⟩ —↠ N))
    ⊎ N ≡ blame
project-multi-inv red = {!!}

project-multi-inv2 : ∀{M N}{G}{g : Ground G}
  → (red : M ⟨ g ?⟩ —↠ N)
  → (∃[ M′ ] Σ[ r1 ∈ M —↠ M′ ] (N ≡ M′ ⟨ g ?⟩ × len r1 ≡ len red))
    ⊎ (∃[ V ] Σ[ r1 ∈ M —↠ V ] Value V × Σ[ r2 ∈ V ⟨ g ?⟩ —↠ N ] len red ≡ len r1 + len r2)
    ⊎ N ≡ blame
project-multi-inv2 red = {!!}

