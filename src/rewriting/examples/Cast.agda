{-# OPTIONS --rewriting #-}
{-
   A simple blame calculus partly based on a version 
   by Jeremy, Phil Wadler, and Peter Thiemann.
-}

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List using (map)
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
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
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

{- Types -}

infixr 7 _⇒_
infix  8 $ₜ_

data Type : Set where
  ★ : Type
  $ₜ_ : (ι : Base) → Type
  _⇒_ : (A : Type) → (B : Type) → Type

{- Ground types -}

infix  8 $ᵍ_

data Ground : Set where
  $ᵍ_  :
       (ι : Base) 
       ----------
     → Ground

  ★⇒★ :
       ------
       Ground

gnd⇒ty : Ground → Type
gnd⇒ty ($ᵍ ι) = $ₜ ι
gnd⇒ty ★⇒★ = ★ ⇒ ★

_≡ᵍ_ : ∀ (G : Ground) (H : Ground) → Dec (G ≡ H)
($ᵍ ι) ≡ᵍ ($ᵍ ι′)
    with ι ≡$? ι′
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
($ᵍ ι) ≡ᵍ ★⇒★ = no λ ()
★⇒★ ≡ᵍ ($ᵍ ι) = no λ ()
★⇒★ ≡ᵍ ★⇒★ = yes refl

{----------------------- Type Precision ------------------------}

infixr 6 _⊑_
data _⊑_ : Type → Type → Set where

  unk⊑ : ∀{B} → ★ ⊑ B
  
  base⊑ : ∀{ι} → $ₜ ι ⊑ $ₜ ι

  fun⊑ : ∀{A B C D}
     → A ⊑ C
     → B ⊑ D
     → A ⇒ B ⊑ C ⇒ D

Refl⊑ : ∀{A} → A ⊑ A
Refl⊑ {★} = unk⊑
Refl⊑ {$ₜ ι} = base⊑
Refl⊑ {A ⇒ B} = fun⊑ Refl⊑ Refl⊑

Trans⊑ : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
Trans⊑ unk⊑ b = unk⊑
Trans⊑ base⊑ b = b
Trans⊑ (fun⊑ a a₁) (fun⊑ b b₁) = fun⊑ (Trans⊑ a b) (Trans⊑ a₁ b₁)

AntiSym⊑ : ∀ {A B} → A ⊑ B → B ⊑ A → A ≡ B
AntiSym⊑ unk⊑ unk⊑ = refl
AntiSym⊑ base⊑ base⊑ = refl
AntiSym⊑ {A ⇒ B}{A' ⇒ B'} (fun⊑ a a₁) (fun⊑ b b₁) =
  cong₂ (_⇒_) (AntiSym⊑ a b) (AntiSym⊑ a₁ b₁)

{------------------------ Terms --------------------------------}

data Lit : Set where
  Num : ℕ → Lit
  Bool : 𝔹 → Lit

typeof : Lit → Base
typeof (Num n) = ′ℕ
typeof (Bool b) = ′𝔹

data Op : Set where
  op-lam : Op
  op-app : Op
  op-lit : Lit → Op
  op-inject : Ground → Op
  op-project : Ground → Op
  op-blame : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit c) = []
sig (op-inject G) = ■ ∷ []
sig (op-project H) = ■ ∷ []
sig (op-blame) = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $ c = (op-lit c) ⦅ nil ⦆
pattern _⟨_!⟩ M G = (op-inject G) ⦅ cons (ast M) nil ⦆
pattern _⟨_?⟩ M H = (op-project H) ⦅ cons (ast M) nil ⦆
pattern blame = op-blame ⦅ nil ⦆

data Blame : Term → Set where
  isBlame : Blame blame

{--------------------- Values -----------------------------}

data Value : Term → Set where
  ƛ̬_ : (N : Term) → Value (ƛ N)
  $̬ : (c : Lit) → Value ($ c)
  _〈_〉 : ∀{V} → Value V → (G : Ground) → Value (V ⟨ G !⟩)

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
rename-val ρ ($̬ c)    =  $̬ c
rename-val ρ (V 〈 g 〉)  =  (rename-val ρ V) 〈 g 〉

sub-val : ∀ {V}
  → (σ : Subst)
  → Value V
  → Value (⟪ σ ⟫ V)
sub-val σ (ƛ̬ N) = ƛ̬ ⟪ ext σ ⟫ N
sub-val σ ($̬ c) = $̬ c
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

  ⊢$ : ∀ {Γ} (c : Lit)
      -------------------------
    → Γ ⊢ $ c ⦂ ($ₜ (typeof c))

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
    → Γ ⊢ M ⦂ gnd⇒ty G
      --------------------
    → Γ ⊢ M ⟨ G !⟩ ⦂ ★

  ⊢⟨?⟩ : ∀{Γ M}
    → Γ ⊢ M ⦂ ★
    → (H : Ground)
      -----------------------
    → Γ ⊢ M ⟨ H ?⟩ ⦂ gnd⇒ty H

  ⊢blame : ∀{Γ A}
      ---------------
    → Γ ⊢ blame ⦂ A


{----------------------- Term Precision ------------------------}

infix 3 _⊩_⊑_⦂_

Prec : Set
Prec = (∃[ A ] ∃[ B ] A ⊑ B)

data _⊩_⊑_⦂_ : List Prec → Term → Term → ∀{A B : Type} → A ⊑ B → Set 

data _⊩_⊑_⦂_ where

  ⊑-var : ∀ {Γ x A⊑B}
     → Γ ∋ x ⦂ A⊑B
       -------------------------------------
     → Γ ⊩ (` x) ⊑ (` x) ⦂ proj₂ (proj₂ A⊑B)

  ⊑-lit : ∀ {Γ c}
       -----------------------------------
     → Γ ⊩ ($ c) ⊑ ($ c) ⦂ base⊑{typeof c}

  ⊑-app : ∀{Γ L M L′ M′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → Γ ⊩ L ⊑ L′ ⦂ fun⊑ c d
     → Γ ⊩ M ⊑ M′ ⦂ c
       -----------------------
     → Γ ⊩ L · M ⊑ L′ · M′ ⦂ d

  ⊑-lam : ∀{Γ N N′ A B C D}{c : A ⊑ C}{d : B ⊑ D}
     → (A , C , c) ∷ Γ ⊩ N ⊑ N′ ⦂ d
       ----------------------------
     → Γ ⊩ ƛ N ⊑ ƛ N′ ⦂ fun⊑ c d

  ⊑-inj-L : ∀{Γ M M′}{G B}{c : (gnd⇒ty G) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ c
       ---------------------------
     → Γ ⊩ M ⟨ G !⟩ ⊑ M′ ⦂ unk⊑{B}

  ⊑-inj-R : ∀{Γ M M′}{A G}{c : A ⊑ (gnd⇒ty G)}
     → Γ ⊩ M ⊑ M′ ⦂ c
       ---------------------------
     → Γ ⊩ M ⊑ M′ ⟨ G !⟩ ⦂ unk⊑{★}

  ⊑-proj-L : ∀{Γ M M′ H B}{c : (gnd⇒ty H) ⊑ B}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑{B}
       ---------------------
     → Γ ⊩ M ⟨ H ?⟩ ⊑ M′ ⦂ c

  ⊑-proj-R : ∀{Γ M M′ A H}{c : A ⊑ (gnd⇒ty H)}
     → Γ ⊩ M ⊑ M′ ⦂ unk⊑{★}
       ---------------------
     → Γ ⊩ M ⊑ M′ ⟨ H ?⟩  ⦂ c

  ⊑-blame : ∀{Γ M A}
     → map proj₁ Γ ⊢ M ⦂ A
       ------------------------
     → Γ ⊩ M ⊑ blame ⦂ Refl⊑{A}

{----------------------- Frames ------------------------}


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
      (G : Ground)
      -----
    → Frame

  □⟨_?⟩ : 
      (H : Ground)
      -----
    → Frame

{- The plug function inserts an expression into the hole of a frame. -}

_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
(□⟨ G !⟩) ⟦ M ⟧  =  M ⟨ G !⟩
(□⟨ H ?⟩) ⟦ M ⟧  =  M ⟨ H ?⟩

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
    → M ≡ V ⟨ G !⟩
      ---------------------------
    → M ⟨ G ?⟩ —→ V

  collide  : ∀{G H} {M V : Term}
    → Value V
    → G ≢ H
    → M ≡ V ⟨ G !⟩
      ---------------------------------
    → M ⟨ H ?⟩ —→ blame

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

reducible : (M : Term) → Set
reducible M = ∃[ N ] (M —→ N)

irred : (M : Term) → Set
irred M = ¬ reducible M

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
   nope (ξξ □⟨ G !⟩ () x₁ V→M) (ƛ̬ N)
   nope (ξξ □⟨ H ?⟩ () x₁ V→M) (ƛ̬ N)
   nope (ξξ-blame (□· M) ()) (ƛ̬ N)
   nope (ξξ-blame (v ·□) ()) (ƛ̬ N)
   nope (ξξ-blame □⟨ G !⟩ ()) (ƛ̬ N)
   nope (ξξ-blame □⟨ H ?⟩ ()) (ƛ̬ N)
   nope (ξξ (□· M) () x₁ V→M) ($̬ c)
   nope (ξξ (v ·□) () x₁ V→M) ($̬ c)
   nope (ξξ □⟨ G !⟩ () x₁ V→M) ($̬ c)
   nope (ξξ □⟨ H ?⟩ () x₁ V→M) ($̬ c)
   nope (ξξ-blame (□· M) ()) ($̬ c)
   nope (ξξ-blame (v ·□) ()) ($̬ c)
   nope (ξξ-blame □⟨ G !⟩ ()) ($̬ c)
   nope (ξξ-blame □⟨ H ?⟩ ()) ($̬ c)
   nope (ξ □⟨ G !⟩ V→M) (v 〈 g 〉) = nope V→M v
   nope (ξ-blame □⟨ _ !⟩) (() 〈 g 〉)

value-irred : ∀{V : Term} → Value V → irred V
value-irred {V} v (N , V→N) = value-irreducible v V→N

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
blame—↠ {N} (.blame —→⟨ ξξ □⟨ G !⟩ () x₁ x₂ ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ □⟨ H ?⟩ () x₁ x₂ ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ-blame (□· M) () ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ-blame (v ·□) () ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ-blame □⟨ G !⟩ () ⟩ red)
blame—↠ {N} (.blame —→⟨ ξξ-blame □⟨ H ?⟩ () ⟩ red)

blame-irreducible : ∀{M} → ¬ (blame —→ M)
blame-irreducible {M} (ξξ (□· M₁) () x₁ blame→M)
blame-irreducible {M} (ξξ (v ·□) () x₁ blame→M)
blame-irreducible {M} (ξξ □⟨ G !⟩ () x₁ blame→M)
blame-irreducible {M} (ξξ □⟨ H ?⟩ () x₁ blame→M)
blame-irreducible {.blame} (ξξ-blame (□· M) ())
blame-irreducible {.blame} (ξξ-blame (v ·□) ())
blame-irreducible {.blame} (ξξ-blame □⟨ G !⟩ ())
blame-irreducible {.blame} (ξξ-blame □⟨ H ?⟩ ())

app-multi-inv : ∀{L M N}
  → (r1 : L · M —↠ N)
  → (∃[ L′ ] (Σ[ r2 ∈ (L —↠ L′) ] (N ≡ L′ · M × len r1 ≡ len r2)))
    ⊎ (∃[ V ] ∃[ M′ ] Σ[ r2 ∈ (L —↠ V) ] (Value V × Σ[ r3 ∈ (M —↠ M′) ]
        (N ≡ V · M′ × len r1 ≡ len r2 + len r3)))
    ⊎ (∃[ V ] ∃[ W ] Σ[ r2 ∈ (L —↠ V) ] (Value V × Σ[ r3 ∈ (M —↠ W) ]
        (Value W × Σ[ r4 ∈ (V · W —↠ N) ] len r1 ≡ len r2 + len r3 + len r4)))
    ⊎ N ≡ blame
app-multi-inv {L}{M}{N} ((L · M) END) = inj₁ (L , (_ END) , refl , refl)
app-multi-inv {L} {M} {N} (.(L · M) —→⟨ ξξ {L}{L′} (□· _) refl refl L—→L′ ⟩ rs)
    with app-multi-inv rs
... | inj₁ (L″ , L′→L″ , refl , eq) = inj₁ (L″ , (L —→⟨ L—→L′ ⟩ L′→L″) , refl , cong suc eq)
... | inj₂ (inj₁ (V , M′ , L′→V , v , M→M′ , refl , eq)) =
      inj₂ (inj₁ (V , M′ , (L —→⟨ L—→L′ ⟩ L′→V) , v , M→M′ , refl , cong suc eq))
... | inj₂ (inj₂ (inj₁ (V , W , L′→V , v , M→W , w , →N , eq))) =
      inj₂ (inj₂ (inj₁ (V , W , (L —→⟨ L—→L′ ⟩ L′→V) , v , M→W , w , →N , cong suc eq)))
... | inj₂ (inj₂ (inj₂ refl)) = inj₂ (inj₂ (inj₂ refl))
app-multi-inv {V} {M} {N} (.(V · M) —→⟨ ξξ {N = M′} (v ·□) refl refl M—→M′ ⟩ V·M′—↠N)
    with app-multi-inv V·M′—↠N
... | inj₁ (L′ , V→L′ , refl , eq)
    with value—↠ v V→L′
... | refl =
    inj₂ (inj₁ (V , M′ , V→L′ , v , (M —→⟨ M—→M′ ⟩ M′ END) , refl , EQ))
    where EQ : suc (len V·M′—↠N) ≡ len V→L′ + 1
          EQ = trans (cong suc eq) (sym (trans (+-suc _ _) (+-identityʳ _)))
app-multi-inv {V} {M} {N} (.(V · M) —→⟨ ξξ (v ·□) refl refl M—→M′ ⟩ V·M′—↠N)
    | inj₂ (inj₁ (V′ , M″ , V→V′ , v′ , M′→M″ , refl , eq)) =
      inj₂ (inj₁ (V′ , M″ , V→V′ , v′ , (M —→⟨ M—→M′ ⟩ M′→M″) , refl , EQ))
    where EQ : suc (len V·M′—↠N) ≡ len V→V′ + suc (len M′→M″)
          EQ rewrite eq = sym (+-suc _ _)
app-multi-inv {V} {M} {N} (.(V · M) —→⟨ ξξ (v ·□) refl refl M—→M′ ⟩ V·M′—↠N)
    | inj₂ (inj₂ (inj₁ (V′ , W , V→V′ , v′ , M′→W , w , V′·W→N , eq ))) =
      inj₂ (inj₂ (inj₁ (V′ , W , V→V′ , v′ , (M —→⟨ M—→M′ ⟩ M′→W) , w , V′·W→N , EQ)))
    where EQ : suc (len V·M′—↠N) ≡ len V→V′ + suc (len M′→W) + len V′·W→N
          EQ = trans (cong suc eq) (sym (cong (λ X → X + len V′·W→N)
                                       (+-suc (len V→V′) (len M′→W))))
app-multi-inv {V} {M} {N} (.(V · M) —→⟨ ξξ (v ·□) refl refl M—→M′ ⟩ V·M′—↠N)
    | inj₂ (inj₂ (inj₂ refl)) = inj₂ (inj₂ (inj₂ refl))
app-multi-inv {L} {M} {N} (.(L · M) —→⟨ ξξ-blame (□· _) refl ⟩ rs)
    with blame—↠ rs
... | refl = inj₂ (inj₂ (inj₂ refl))
app-multi-inv {L} {M} {N} (.(L · M) —→⟨ ξξ-blame (v ·□) refl ⟩ rs)
    with blame—↠ rs
... | refl = inj₂ (inj₂ (inj₂ refl))
app-multi-inv {.(ƛ _)} {M} {N} (.(ƛ _ · M) —→⟨ β v ⟩ M′—↠N) =
  inj₂ (inj₂ (inj₁ (ƛ _ , M , (_ END) , ƛ̬ _ , (M END) , v , (_ —→⟨ β v ⟩ M′—↠N) , refl)))

inject-multi-inv : ∀{M N}{G}
  → (red : M ⟨ G !⟩ —↠ N)
  → (∃[ M′ ] Σ[ r1 ∈ M —↠ M′ ] (N ≡ M′ ⟨ G !⟩ × len r1 ≡ len red))
    ⊎ (∃[ V ] Σ[ r1 ∈ M —↠ V ] Value V × Σ[ r2 ∈ V ⟨ G !⟩ —↠ N ] len red ≡ len r1 + len r2)
    ⊎ N ≡ blame
inject-multi-inv {M} (.(_ ⟨ _ !⟩) END) = inj₁ (M , (_ END) , refl , refl)
inject-multi-inv (.(_ ⟨ _ !⟩) —→⟨ ξξ □⟨ G !⟩ refl refl r1 ⟩ r2)
    with inject-multi-inv r2
... | inj₁ (M′ , →M′ , eq , eqlen) = inj₁ (_ , (_ —→⟨ r1 ⟩ →M′) , eq , cong suc eqlen)
... | inj₂ (inj₁ (V , →V , v , →N , eqlen)) = inj₂ (inj₁ (_ , (_ —→⟨ r1 ⟩ →V) , v , →N , cong suc eqlen))
... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
inject-multi-inv (.(_ ⟨ _ !⟩) —→⟨ ξξ-blame □⟨ G !⟩ x ⟩ red)
    with blame—↠ red
... | refl = inj₂ (inj₂ refl)

project-multi-inv2 : ∀{M N}{G}
  → (red : M ⟨ G ?⟩ —↠ N)
  → (∃[ M′ ] Σ[ r1 ∈ M —↠ M′ ] (N ≡ M′ ⟨ G ?⟩ × len r1 ≡ len red))
    ⊎ (∃[ V ] Σ[ r1 ∈ M —↠ V ] Value V × Σ[ r2 ∈ V ⟨ G ?⟩ —↠ N ] len red ≡ len r1 + len r2)
    ⊎ N ≡ blame
project-multi-inv2 (.(_ ⟨ _ ?⟩) END) = inj₁ (_ , (_ END) , refl , refl)
project-multi-inv2 (.(_ ⟨ _ ?⟩) —→⟨ ξξ □⟨ H ?⟩ refl refl r ⟩ rs)
    with project-multi-inv2 rs
... | inj₁ (M′ , M→M′ , refl , eq) = inj₁ (M′ , (_ —→⟨ r ⟩ M→M′) , refl , cong suc eq)
... | inj₂ (inj₁ (V , M→V , v , Vg→N , eq)) = inj₂ (inj₁ (V , (_ —→⟨ r ⟩ M→V ) , v , Vg→N , cong suc eq))
... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
project-multi-inv2 (.(_ ⟨ _ ?⟩) —→⟨ ξξ-blame □⟨ H ?⟩ refl ⟩ rs)
    with blame—↠ rs
... | refl = inj₂ (inj₂ refl)
project-multi-inv2 (.(_ ⟨ _ ?⟩) —→⟨ collapse v refl ⟩ rs) =
    inj₂ (inj₁ ((_ ⟨ _ !⟩) , (_ END) , (v 〈 _ 〉) , (_ —→⟨ collapse v refl ⟩ rs) , refl))
project-multi-inv2 (.(_ ⟨ _ ?⟩) —→⟨ collide v neq refl ⟩ rs) =
    inj₂ (inj₁ ((_ ⟨ _ !⟩) , (_ END) , (v 〈 _ 〉) , (_ —→⟨ collide v neq refl ⟩ rs) , refl))

app-inv-left : ∀{L M N}
  → (r1 : L · M —↠ N)
  → irred N
    --------------------------
  → (∃[ L′ ] Σ[ r2 ∈ (L —↠ L′) ] irred L′
        × Σ[ r3 ∈ (L′ · M —↠ N) ] len r1 ≡ len r2 + len r3)
    ⊎ N ≡ blame
app-inv-left {L} {M} {.(L · M)} (.(L · M) END) irredN =
    inj₁ (L , (_ END) , IL , (_ END) , refl)
    where IL : irred L
          IL (L′ , L→L′) = ⊥-elim (irredN (_ , (ξ (□· M) L→L′)))
app-inv-left {L} {M} {N} (.(L · M) —→⟨ ξ (□· M₁) r1 ⟩ r2) irredN
    with app-inv-left r2 irredN
... | inj₁ (L′ , L→L′ , IL′ , r3 , eq) =
      inj₁ (L′ , (L —→⟨ r1 ⟩ L→L′) , IL′ , r3 , cong suc eq)
... | inj₂ refl = inj₂ refl
app-inv-left {L} {M} {N} (.(L · M) —→⟨ ξ (v ·□) r1 ⟩ r2) irredN =
    inj₁ (value v , (_ END) , value-irred v ,
          ((value v · M) —→⟨ ξ (v ·□) r1 ⟩ r2) , refl)
app-inv-left {L} {M} {N} (.(L · M) —→⟨ ξ-blame (□· M₁) ⟩ r2) irredN
    with blame—↠ r2
... | refl = inj₂ refl
app-inv-left {L} {M} {N} (.(L · M) —→⟨ ξ-blame (v ·□) ⟩ r2) irredN
    with blame—↠ r2
... | refl = inj₂ refl
app-inv-left {.(ƛ _)} {M} {N} (.(ƛ _ · M) —→⟨ β v ⟩ r2) irredN =
    inj₁ (_ , (_ END) , value-irred (ƛ̬ _) , (_ —→⟨ β v ⟩ r2) , refl)

app-inv-right : ∀{V M N}
  → (r1 : V · M —↠ N)
  → Value V
  → irred N
  → (∃[ M′ ] Σ[ r2 ∈ (M —↠ M′) ] irred M′
       × Σ[ r3 ∈ (V · M′ —↠ N) ] len r1 ≡ len r2 + len r3)
    ⊎ N ≡ blame
app-inv-right {V}{M}{N} (.(_ · _) END) v irredN =
    inj₁ (M , (_ END) , irredM , (_ END) , refl)
    where irredM : irred M
          irredM (M′ , M→M′) = irredN ((V · M′) , (ξ (v ·□) M→M′))
app-inv-right {V} {M} {N} (.(V · M) —→⟨ ξ (□· M) r1 ⟩ r2) v irredN =
    ⊥-elim (value-irreducible v r1)
app-inv-right {V} {M} {N} (.(V · M) —→⟨ ξ (v′ ·□) r1 ⟩ r2) v irredN
    with app-inv-right r2 v′ irredN
... | inj₁ (M′ , M→M′ , iM′ , →N , eq) =
      inj₁ (M′ , (M —→⟨ r1 ⟩ M→M′) , iM′ , →N , cong suc eq)
... | inj₂ refl = inj₂ refl
app-inv-right {.blame} {M} {N} (.(blame · M) —→⟨ ξ-blame (□· M) ⟩ r2) () irredN
app-inv-right {V} {M} {N} (.(V · M) —→⟨ ξ-blame (v₁ ·□) ⟩ r2) v irredN
    with blame—↠ r2
... | refl = inj₂ refl
app-inv-right {.(ƛ _)} {M} {N} (.(ƛ _ · M) —→⟨ β w ⟩ r2) v irredN =
    inj₁ (M , (_ END) , value-irred w , (_ —→⟨ β w ⟩ r2) , refl)

frame-inv : ∀{F M N}
  → (r1 : F ⟦ M ⟧ —↠ N)
  → irred N
  → (∃[ M′ ] Σ[ r2 ∈ (M —↠ M′) ] irred M′
        × Σ[ r3 ∈ (F ⟦ M′ ⟧ —↠ N) ] len r1 ≡ len r2 + len r3)
    ⊎ N ≡ blame
frame-inv {□· M} {L} {N} r1 irN = app-inv-left r1 irN 
frame-inv {v ·□} {M} {N} r1 irN = app-inv-right r1 v irN
frame-inv {□⟨ G !⟩} {M} (_ END) irN = inj₁ (_ , (_ END) , irM , (_ END) , refl)
    where irM : irred M
          irM (M′ , M→M′) = irN (_ , (ξ □⟨ G !⟩ M→M′))
frame-inv {□⟨ G !⟩} {M} {N} (.(□⟨ G !⟩ ⟦ M ⟧) —→⟨ ξ □⟨ _ !⟩ r1 ⟩ r2) irN
    with frame-inv{□⟨ G !⟩} r2 irN
... | inj₁ (M′ , r3 , irM′ , r4 , eq) = inj₁ (_ , (_ —→⟨ r1 ⟩ r3) , irM′ , r4 , cong suc eq)
... | inj₂ refl = inj₂ refl
frame-inv {□⟨ G !⟩} {M} {N} (.(□⟨ G !⟩ ⟦ M ⟧) —→⟨ ξ-blame □⟨ _ !⟩ ⟩ r2) irN
    with blame—↠ r2
... | refl = inj₂ refl
frame-inv {□⟨ H ?⟩} {M} (_ END) irN = inj₁ (_ , (_ END) , irM , (_ END) , refl)
    where irM : irred M
          irM (M′ , M→M′) = irN (_ , (ξ □⟨ H ?⟩ M→M′))
frame-inv {□⟨ H ?⟩} {M} {N} (.(□⟨ H ?⟩ ⟦ M ⟧) —→⟨ ξ □⟨ _ ?⟩ r1 ⟩ r2) irN
    with frame-inv{□⟨ H ?⟩} r2 irN
... | inj₁ (M′ , r3 , irM′ , r4 , eq) = inj₁ (_ , (_ —→⟨ r1 ⟩ r3) , irM′ , r4 , cong suc eq)
... | inj₂ refl = inj₂ refl
frame-inv {□⟨ H ?⟩} {M} {N} (.(□⟨ H ?⟩ ⟦ M ⟧) —→⟨ ξ-blame □⟨ _ ?⟩ ⟩ r2) irN
    with blame—↠ r2
... | refl = inj₂ refl
frame-inv {□⟨ H ?⟩} {M} {N} (.(□⟨ H ?⟩ ⟦ M ⟧) —→⟨ collapse v refl ⟩ r2) irN =
  inj₁ (M , (_ END) , value-irred (v 〈 _ 〉) , (_ —→⟨ collapse v refl ⟩ r2) , refl)
frame-inv {□⟨ H ?⟩} {M} {N} (.(□⟨ H ?⟩ ⟦ M ⟧) —→⟨ collide v eq refl ⟩ r2) irN =
  inj₁ (M , (_ END) , value-irred (v 〈 _ 〉) , (_ —→⟨ collide v eq refl ⟩ r2) , refl)

frame-blame : ∀{F}{M}{N}
   → M —↠ N
   → M ≡ F ⟦ blame ⟧
   → irred N
   → N ≡ blame
frame-blame {F} {N} (.N END) refl irN = ⊥-elim (irN (_ , (ξ-blame F)))
frame-blame {□· M} {.((□· M) ⟦ blame ⟧)} (.((□· M) ⟦ blame ⟧) —→⟨ ξξ (□· M₁) refl x₁ r ⟩ M→N) refl irN =
  ⊥-elim (blame-irreducible r)
frame-blame {□· M} {.((□· M) ⟦ blame ⟧)} (.((□· M) ⟦ blame ⟧) —→⟨ ξξ (() ·□) refl x₁ r ⟩ M→N) refl irN
frame-blame {□· M} {.((□· M) ⟦ blame ⟧)} (.((□· M) ⟦ blame ⟧) —→⟨ ξξ-blame F x ⟩ M→N) refl irN
    with blame—↠ M→N
... | refl = refl
frame-blame {v ·□} {.((v ·□) ⟦ blame ⟧)} (.((v ·□) ⟦ blame ⟧) —→⟨ ξξ (□· M) refl refl r ⟩ M→N) refl irN =
    ⊥-elim (value-irreducible v r)
frame-blame {v ·□} {.((v ·□) ⟦ blame ⟧)} (.((v ·□) ⟦ blame ⟧) —→⟨ ξξ (v₁ ·□) refl refl r ⟩ M→N) refl irN =
    ⊥-elim (blame-irreducible r)
frame-blame {v ·□} {.((v ·□) ⟦ blame ⟧)} (.((v ·□) ⟦ blame ⟧) —→⟨ ξξ-blame F x ⟩ M→N) refl irN 
    with blame—↠ M→N
... | refl = refl
frame-blame {□⟨ G !⟩} {.(□⟨ G !⟩ ⟦ blame ⟧)} (.(□⟨ G !⟩ ⟦ blame ⟧) —→⟨ ξξ □⟨ _ !⟩ refl refl r ⟩ M→N) refl irN =
  ⊥-elim (blame-irreducible r)
frame-blame {□⟨ G !⟩} {.(□⟨ G !⟩ ⟦ blame ⟧)} (.(□⟨ G !⟩ ⟦ blame ⟧) —→⟨ ξξ-blame F x ⟩ M→N) refl irN
    with blame—↠ M→N
... | refl = refl
frame-blame {□⟨ H ?⟩} {.(□⟨ H ?⟩ ⟦ blame ⟧)} (.(□⟨ H ?⟩ ⟦ blame ⟧) —→⟨ ξξ □⟨ _ ?⟩ refl refl r ⟩ M→N) refl irN = 
  ⊥-elim (blame-irreducible r)
frame-blame {□⟨ H ?⟩} {.(□⟨ H ?⟩ ⟦ blame ⟧)} (.(□⟨ H ?⟩ ⟦ blame ⟧) —→⟨ ξξ-blame □⟨ _ ?⟩ x ⟩ M→N) refl irN
    with blame—↠ M→N
... | refl = refl

app-invL : ∀{L M N : Term}
   → reducible L
   → L · M  —→ N
   → ∃[ L′ ] ((L —→ L′) × (N ≡ L′ · M))
app-invL rl (ξ (□· M) L→L′) = _ , (L→L′ , refl)
app-invL (L′ , L→L′) (ξ (v ·□) M→M′) = ⊥-elim (value-irreducible v L→L′)
app-invL (L′ , L→L′) (ξ-blame (□· M)) = ⊥-elim (blame-irreducible L→L′)
app-invL (L′ , L→L′) (ξ-blame (v ·□)) = ⊥-elim (value-irreducible v L→L′)
app-invL (L′ , L→L′) (β v) = ⊥-elim (value-irreducible (ƛ̬ _) L→L′)

blame-frame : ∀{F}{N}
   → (F ⟦ blame ⟧) —→ N
   → N ≡ blame
blame-frame {□· M} {.((□· M₁) ⟦ _ ⟧)} (ξξ (□· M₁) refl refl Fb→N) =
    ⊥-elim (blame-irreducible Fb→N)
blame-frame {□· M} (ξξ (() ·□) refl refl Fb→N)
blame-frame {□· M} {.blame} (ξξ-blame (□· M₁) refl) = refl
blame-frame {□· M} {.blame} (ξξ-blame (() ·□) refl)
blame-frame {v ·□} {N} (ξξ (□· M) refl refl Fb→N) =
    ⊥-elim (value-irreducible v Fb→N)
blame-frame {v ·□} {N} (ξξ (v₁ ·□) refl refl Fb→N) =
    ⊥-elim (blame-irreducible Fb→N)
blame-frame {v ·□} {.blame} (ξξ-blame F x) = refl
blame-frame {□⟨ G !⟩} {_} (ξξ □⟨ _ !⟩ refl refl Fb→N) =
    ⊥-elim (blame-irreducible Fb→N)
blame-frame {□⟨ G !⟩} {.blame} (ξξ-blame F x) = refl
blame-frame {□⟨ H ?⟩} {N} (ξξ □⟨ _ ?⟩ refl refl Fb→N) =
    ⊥-elim (blame-irreducible Fb→N)
blame-frame {□⟨ H ?⟩} {.blame} (ξξ-blame □⟨ _ ?⟩ x) = refl


