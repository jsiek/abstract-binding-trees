{-# OPTIONS --without-K --rewriting #-}
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
  using (×-Lex; ×-wellFounded)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var

module rewriting.examples.Cast where

{- Base types -}

data Base : Set where
  ′ℕ : Base
  ′𝔹 : Base

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

data GroundOf : Type → Type → Set where
  gnd-base : ∀{ι} → GroundOf ($ₜ ι) ($ₜ ι)
  gnd-fun : ∀{A B} → GroundOf (A ⇒ B) (★ ⇒ ★)

{- Terms -}

data Op : Set where
  op-lam : Op
  op-app : Op
  op-lit : ∀{ι : Base} → rep ι → Op
  op-cast : Type → Type → Op
  op-blame : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit n) = []
sig (op-cast A B) = ■ ∷ []
sig (op-blame) = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term)

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $ k = (op-lit k) ⦅ nil ⦆
pattern _⟨_⇒_⟩ M A B = (op-cast A B) ⦅ cons (ast M) nil ⦆
pattern blame = (op-blame) ⦅ nil ⦆

data Value : Term → Set where
  ƛ̬_ : (N : Term) → Value (ƛ N)
  $̬_ : ∀{ι} → (k : rep ι) → Value ($ k)
  _〈_〉 : ∀{V G} → Value V → (g : Ground G) → Value (V ⟨ G ⇒ ★ ⟩)

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

  ⊢⟨⇒⟩ : ∀{Γ M A B}
    → Γ ⊢ M ⦂ A
    → A ∼ B
      --------------------
    → Γ ⊢ M ⟨ A ⇒ B ⟩ ⦂ B

  ⊢blame : ∀{Γ A}
      ---------------
    → Γ ⊢ blame ⦂ A

infix  6 □·_
infix  6 _·□
infix  6 □⟨_⇒_⟩

data Frame : Set where

  □·_ : 
      (M : Term)
      ----------
    → Frame

  _·□ : ∀ {V : Term}
    → (v : Value V)
      -------------
    → Frame

  □⟨_⇒_⟩ : 
      Type
    → Type
      -----
    → Frame

{- The plug function inserts an expression into the hole of a frame. -}

_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
(□⟨ A ⇒ B ⟩) ⟦ M ⟧  =  M ⟨ A ⇒ B ⟩

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

  id-ι : ∀ {ι}{V : Term}
    → Value V
      ------------------------
    → (V ⟨ $ₜ ι ⇒ $ₜ ι ⟩) —→ V

  id-★ : ∀ {V}
    → Value V
      ----------------------------
    → (V ⟨ ★ ⇒ ★ ⟩) —→ V

  wrap : ∀{A A′ B B′} {V : Term}
    → Value V
      -----------------------------------------------------------
    → (V ⟨ (A ⇒ B) ⇒ (A′ ⇒ B′) ⟩)
       —→ ƛ (((rename suc V) · ((` 0) ⟨ A′ ⇒ A ⟩)) ⟨ B ⇒ B′ ⟩)

  expand : ∀ {V : Term}{A G}
    → Value V
    → GroundOf A G
    → ¬ Ground A
      -----------------------------------------
    → (V ⟨ A ⇒ ★ ⟩) —→ (V ⟨ A ⇒ G ⟩) ⟨ G ⇒ ★ ⟩ 

  collapse : ∀{G B} {M V : Term}
    → Value V
    → (g : Ground G)
    → GroundOf B G
    → M ≡ V ⟨ G ⇒ ★ ⟩
      ---------------------------
    → M ⟨ ★ ⇒ B ⟩ —→ V ⟨ G ⇒ B ⟩

  collide  : ∀{G H B} {M V : Term}
    → Value V
    → (g : Ground G)
    → (h : Ground H)
    → GroundOf B H
    → G ≢ H
    → M ≡ V ⟨ G ⇒ ★ ⟩
      ---------------------------------
    → M ⟨ ★ ⇒ B ⟩ —→ blame

pattern ξ F M—→N = ξξ F refl refl M—→N
pattern ξ-blame F = ξξ-blame F refl

{- Reflexive and transitive closure of reduction -}

infixr 1 _++_
infix  1 begin_
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : (M : Term)
      ---------
    → M —↠ M

  _—→⟨_⟩_ : (L : Term) {M N : Term}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N : Term} → (M —↠ N) → (M —↠ N)
begin M—↠N = M—↠N

{- Convenience function to build a sequence of length one. -}

unit : ∀ {M N : Term} → (M —→ N) → (M —↠ N)
unit {M = M} {N = N} M—→N  =  M —→⟨ M—→N ⟩ N ∎


{- Apply ξ to each element of a sequence -}

ξ* : ∀ {M N : Term} → (F : Frame) → M —↠ N → F ⟦ M ⟧ —↠ F ⟦ N ⟧
ξ* F (M ∎) = F ⟦ M ⟧ ∎
ξ* F (L —→⟨ L—→M ⟩ M—↠N) = (F ⟦ L ⟧ —→⟨ ξ F L—→M ⟩ ξ* F M—↠N)

{- Concatenate two sequences. -}

_++_ : ∀ {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
(M ∎) ++ M—↠N                =  M—↠N
(L —→⟨ L—→M ⟩ M—↠N) ++ N—↠P  =  L —→⟨ L—→M ⟩ (M—↠N ++ N—↠P)

{- Alternative notation for sequence concatenation. -}

_—↠⟨_⟩_ : (L : Term) {M N : Term}
  → L —↠ M
  → M —↠ N
    ---------
  → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N  =  L—↠M ++ M—↠N

len : ∀{M N : Term} → (M→N : M —↠ N) → ℕ
len (_ ∎) = 0
len (_ —→⟨ x ⟩ red) = suc (len red)

value-irreducible : ∀ {V M : Term} → Value V → ¬ (V —→ M)
value-irreducible v V—→M = nope V—→M v
   where
   nope : ∀ {V M : Term} → V —→ M → Value V → ⊥
   nope (ξξ (□· M) () x₁ V→M) (ƛ̬ N)
   nope (ξξ (v ·□) () x₁ V→M) (ƛ̬ N)
   nope (ξξ □⟨ x₂ ⇒ x₃ ⟩ () x₁ V→M) (ƛ̬ N)
   nope (ξξ-blame (□· M) ()) (ƛ̬ N)
   nope (ξξ-blame (v ·□) ()) (ƛ̬ N)
   nope (ξξ-blame □⟨ x₁ ⇒ x₂ ⟩ ()) (ƛ̬ N)
   nope (ξξ (□· M) () x₁ V→M) ($̬ k)
   nope (ξξ (v ·□) () x₁ V→M) ($̬ k)
   nope (ξξ □⟨ x₂ ⇒ x₃ ⟩ () x₁ V→M) ($̬ k)
   nope (ξξ-blame (□· M) ()) ($̬ k)
   nope (ξξ-blame (v ·□) ()) ($̬ k)
   nope (ξξ-blame □⟨ x₁ ⇒ x₂ ⟩ ()) ($̬ k)
   nope (ξ □⟨ x₂ ⇒ .★ ⟩ V→M) (v 〈 g 〉) = nope V→M v
   nope (ξ-blame □⟨ x₁ ⇒ .★ ⟩) (() 〈 g 〉)
   nope (expand v′ AG ngA) (v 〈 g 〉) = ⊥-elim (ngA g)

value—↠ : ∀{V N : Term}
    → Value V
    → V —↠ N
    → N ≡ V
value—↠ v (_ ∎) = refl
value—↠ v (_ —→⟨ V—→M ⟩ M—↠N) = ⊥-elim (value-irreducible v V—→M)

app-multi-inv : ∀{L M N}
  → (r1 : L · M —↠ N)
  → (∃[ L′ ] (Σ[ r2 ∈ (L —↠ L′) ] (N ≡ L′ · M × len r1 ≡ len r2)))
    ⊎ (∃[ V ] ∃[ M′ ] Σ[ r2 ∈ (L —↠ V) ] (Value V × Σ[ r3 ∈ (M —↠ M′) ]
        (N ≡ V · M′ × len r1 ≡ len r2 + len r3)))
    ⊎ (∃[ V ] ∃[ W ] Σ[ r2 ∈ (L —↠ V) ] (Value V × Σ[ r3 ∈ (M —↠ W) ]
        (Value W × Σ[ r4 ∈ (V · W —↠ N) ] len r1 ≡ len r2 + len r3 + len r4)))
app-multi-inv = {!!}

{- Lexicographic Recursion/Induction -}

_<₂_ : Rel (ℕ × ℕ) lzero
_<₂_ = ×-Lex _≡_ _<_ _<_

less-eq-less : ∀ {x y x′ y′} → x ≤ x′ → y < y′ → (x , y) <₂ (x′ , y′)
less-eq-less {x}{y}{x′}{y′} lt1 lt2
    with x ≟ x′
... | yes refl = inj₂ (refl , lt2)
... | no neq = inj₁ (≤∧≢⇒< lt1 neq)

<₂-Rec : ∀{ℓ} → RecStruct (ℕ × ℕ) ℓ ℓ
<₂-Rec = WfRec _<₂_

<₂-wellFounded : WellFounded _<₂_
<₂-wellFounded = ×-wellFounded <-wellFounded <-wellFounded

open WF.All <₂-wellFounded renaming (wfRec to <₂-rec)


{- Logical Relation for Type Safety -}

ValPred : Set₁
ValPred = {V : Term} → Value V → Set

ExpPred : Set₁
ExpPred = Term → Set

SafePred : ℕ × ℕ → Set₁
SafePred (k , s) = (A : Type) → (s ≡ size A) → ValPred × ExpPred

𝕍 : (k : ℕ) → (s : ℕ) → <₂-Rec SafePred (k , s)
   → (A : Type) → (s ≡ size A) → ValPred
   
𝕍 k .(size ★) rec ★ refl (ƛ̬ N) = ⊥
𝕍 k .(size ★) rec ★ refl ($̬ c) = ⊥
𝕍 zero .(size ★) rec ★ refl (v 〈 g 〉) = ⊤
𝕍 (suc k) .(size ★) rec ★ refl {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) =
    proj₁ (rec (k , size G) (inj₁ ≤-refl) G refl) v

𝕍 k .(size ($ₜ ι)) rec ($ₜ ι) refl (ƛ̬ N) = ⊥
𝕍 k .(size ($ₜ ι)) rec ($ₜ ι) refl ($̬_ {ι′} c) = ι ≡ ι′
𝕍 k .(size ($ₜ ι)) rec ($ₜ ι) refl (v 〈 g 〉) = ⊥

𝕍 k .(size (A ⇒ B)) rec (A ⇒ B) refl (ƛ̬ N) =
   ∀ {V} (v : Value V) (j : ℕ) → (lt : j ≤ k)
    → proj₁ (rec (j , size A) (less-eq-less lt (s≤s (m≤m⊔n (size A) (size B)))) A refl) v
    → proj₂ (rec (j , size B) (less-eq-less lt (s≤s (m≤n⊔m (size A) (size B)))) B refl) (N [ V ])
𝕍 k .(size (A ⇒ B)) rec (A ⇒ B) refl ($̬ c) = ⊥
𝕍 k .(size (A ⇒ B)) rec (A ⇒ B) refl (v 〈 g 〉) = ⊥

𝔼 : (k : ℕ) → (s : ℕ) → <₂-Rec SafePred (k , s)
   → (A : Type) → (s ≡ size A) → ExpPred
𝔼 k s rec A refl M = ∀ N → (M→N : M —↠ N) → (len M→N < k)
                     → (Σ[ v ∈ Value N ] 𝕍 k (size A) rec A refl v)
                       ⊎ (∃[ N′ ] (N —→ N′))
                       ⊎ N ≡ blame

Safe-step : (p : ℕ × ℕ) → (<₂-Rec SafePred p) → SafePred p
Safe-step (k , s) rec A refl = 𝕍 k s rec A refl , 𝔼 k s rec A refl

abstract
  {- Safe is abstract to hide the complexity of the
     well-founded recursion, which is needed to
     make it possible to use the below unfold-Safe
     lemma to perform rewriting. -}
  Safe : (p : ℕ × ℕ) → SafePred p
  Safe = <₂-rec _ (λ i → SafePred i) Safe-step

𝓥⟦_⟧ : (A : Type) → {V : Term} → Value V → ℕ → Set
𝓥⟦ A ⟧ v k = proj₁ (Safe (k , size A) A refl) v

𝓔⟦_⟧ : Type → Term → ℕ → Set
𝓔⟦ A ⟧ M k = proj₂ (Safe (k , size A) A refl) M

postulate
  Safe-step-ext : (x : ℕ × ℕ) → ∀ {IH IH′}
      → (∀{y} (y<x : y <₂ x) → IH y y<x ≡ IH′ y y<x)
      → Safe-step x IH ≡ Safe-step x IH′

abstract
  unfold-Safe : ∀ n → Safe n ≡ Safe-step n (λ n′ _ → Safe n′)
  unfold-Safe n = FixPoint.unfold-wfRec <₂-wellFounded (λ i → SafePred i)
                     Safe-step Safe-step-ext {n}

{- Equations for the Logical Relattion -}

V-base : ∀{n}{ι}{ι′}{c : rep ι′} → 𝓥⟦ $ₜ ι ⟧ ($̬ c) n ≡ (ι ≡ ι′)
V-base {n} rewrite unfold-Safe (n , 0) = refl

V-dyn-zero : ∀{G}{V}{v : Value V}{g}
   → 𝓥⟦ ★ ⟧ {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) 0 ≡ ⊤
V-dyn-zero rewrite unfold-Safe (0 , size ★) = refl

V-dyn : ∀{n}{G}{V}{v : Value V}{g}
     → 𝓥⟦ ★ ⟧ {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) (suc n) ≡ 𝓥⟦ G ⟧ v n
V-dyn {n}{G} rewrite unfold-Safe (suc n , size ★)
                   | sym (unfold-Safe (n , size G))
    = refl

V-dyn-inv : ∀{V}{v : Value V}{n}
     → 𝓥⟦ ★ ⟧ {V} v (suc n)
     → ∃[ V′ ] ∃[ G ] (V ≡ V′ ⟨ G ⇒ ★ ⟩) × Value V′ × Ground G 
V-dyn-inv {.(ƛ N)} {ƛ̬ N} {n} Vv rewrite unfold-Safe (suc n , size ★) = ⊥-elim Vv
V-dyn-inv {.($ k)} {$̬ k} {n} Vv rewrite unfold-Safe (suc n , size ★) = ⊥-elim Vv
V-dyn-inv {(V′ ⟨ G ⇒ ★ ⟩)} {v 〈 g 〉} {n} Vv rewrite unfold-Safe (suc n , size ★) =
    V′ , G , refl , v , g 

V-fun : ∀{n}{A B}{N}
  → 𝓥⟦ A ⇒ B ⟧ (ƛ̬ N) n ≡ ∀ {V} (v : Value V) (j : ℕ) → (lt : j ≤ n)
                          → 𝓥⟦ A ⟧ v j → 𝓔⟦ B ⟧ (N [ V ]) j
V-fun {n}{A}{B} rewrite unfold-Safe (n , size (A ⇒ B)) = refl

E-def : (A : Type) → (M : Term) → (k : ℕ)
   → 𝓔⟦ A ⟧ M k ≡
       ∀ N → (M→N : M —↠ N) → (len M→N < k)
             → (Σ[ v ∈ Value N ] 𝓥⟦ A ⟧ v k)
               ⊎ (∃[ N′ ] (N —→ N′))
               ⊎ N ≡ blame               
E-def A M k rewrite unfold-Safe (k , size A) = refl


{- Type Safety -}

{- A substitution whose terms are all values. -}
ValSubst : Set
ValSubst = Σ[ σ ∈ Subst ] (∀ x → Value (σ x))

inc : ValSubst → ValSubst
inc σ = (λ x → proj₁ σ (suc x)) , (λ x → proj₂ σ (suc x))

𝓖⟦_⟧ : (Γ : List Type) → ValSubst → ℕ → Set
𝓖⟦ [] ⟧ σ k = ⊤
𝓖⟦ A ∷ Γ ⟧ σ k = 𝓖⟦ Γ ⟧ (inc σ) k × 𝓥⟦ A ⟧ (proj₂ σ 0) k

lemma-𝓖 : (Γ : List Type) → (γ : ValSubst) → (k : ℕ) → 𝓖⟦ Γ ⟧ γ k
  → ∀ {A}{y} → (∋y : Γ ∋ y ⦂ A)
  → 𝓥⟦ A ⟧ (proj₂ γ y) k
lemma-𝓖 [] γ k 𝓖γ ()
lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {zero} refl = 𝓥γ0
lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {suc y} ∋y =
  lemma-𝓖 Γ (inc γ) k 𝓖γ ∋y

_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ k (γ : ValSubst) → 𝓖⟦ Γ ⟧ γ k → 𝓔⟦ A ⟧ (⟪ proj₁ γ ⟫ M) k

_⊨ⱽ_⦂_ : List Type → {V : Term} → Value V → Type → Set
Γ ⊨ⱽ v ⦂ A = ∀ k (γ : ValSubst) → 𝓖⟦ Γ ⟧ γ k → 𝓥⟦ A ⟧ (sub-val (proj₁ γ) v) k

Val⇒Exp : ∀{A}{V : Term}{v : Value V} (k : ℕ)
   → 𝓥⟦ A ⟧ v k
   → 𝓔⟦ A ⟧ V k
Val⇒Exp Vv = {!!}

dyn? : (A : Type) → A ≡ ★ ⊎ A ≢ ★
dyn? ★ = inj₁ refl
dyn? ($ₜ ι) = inj₂ (λ ())
dyn? (A ⇒ B) = inj₂ (λ ())

ground-or-★ : (A : Type) → A ≡ ★ ⊎ Ground A ⊎ (∃[ G ] GroundOf A G × ¬ Ground A)
ground-or-★ ★ = inj₁ refl
ground-or-★ ($ₜ ι) = inj₂ (inj₁ ($ᵍ ι))
ground-or-★ (A ⇒ B)
    with dyn? A | dyn? B
... | inj₁ refl | inj₁ refl = inj₂ (inj₁ ★⇒★)
... | inj₁ refl | inj₂ neq = inj₂ (inj₂ ((★ ⇒ ★) , gnd-fun ,
                                         λ { ★⇒★ → neq refl}))
... | inj₂ neq | _ = inj₂ (inj₂ (★ ⇒ ★ , gnd-fun , λ { ★⇒★ → neq refl}))

mono-𝓥 : ∀ j k A {V} (v : Value V)
   → j ≤′ k
   → 𝓥⟦ A ⟧ v k
   → 𝓥⟦ A ⟧ v j
mono-𝓥 j≤k Vvk = {!!}

{-# REWRITE sub-var #-}

fundamental : ∀ {Γ A} → (M : Term)
  → (Γ ⊢ M ⦂ A)
    -----------
  → (Γ ⊨ M ⦂ A)
  
fundamental {Γ}{A} (` x) (⊢` ∋x) k γ 𝓖Γγk =
  let Vγx = lemma-𝓖 Γ γ k 𝓖Γγk ∋x in
  Val⇒Exp {A}{⟪ proj₁ γ ⟫ (` x)} k Vγx
  
fundamental ($ c) (⊢$ ι) k γ 𝓖Γγk =
    Val⇒Exp {v = $̬ c} k G
    where G : 𝓥⟦ $ₜ ι ⟧ ($̬ c) k
          G rewrite V-base{k}{ι}{ι}{c} = refl

fundamental (L · M) (⊢· ⊢L ⊢M) = {!!}

fundamental (ƛ N) (⊢ƛ ⊢N) = {!!}

fundamental {Γ} (M ⟨ A ⇒ B ⟩) (⊢⟨⇒⟩ ⊢M A∼B) k γ 𝓖Γγk
    rewrite E-def B (⟪ proj₁ γ ⟫ M ⟨ A ⇒ B ⟩) k = G k 𝓖Γγk A∼B
    where
      G : (k : ℕ) → 𝓖⟦ Γ ⟧ γ k → A ∼ B
         → (N : Term)
         → (M→N : ⟪ proj₁ γ ⟫ M ⟨ A ⇒ B ⟩ —↠ N )
         → (suc (len M→N) ≤ k)
         → (Σ[ v ∈ Value N ] (𝓥⟦ B ⟧ v k)) ⊎ (∃[ N′ ] (N —→ N′)) ⊎ N ≡ blame
      G (suc k′) 𝓖Γγk A∼B .(⟪ proj₁ γ ⟫ M ⟨ A ⇒ B ⟩) (_ ∎) (s≤s ≤k′)
          with fundamental M ⊢M (suc k′) γ 𝓖Γγk 
      ... | 𝓔⟦A⟧γMk rewrite E-def A (⟪ proj₁ γ ⟫ M) (suc k′)
          with 𝓔⟦A⟧γMk (⟪ proj₁ γ ⟫ M) (_ ∎) (s≤s ≤k′)
      ... | inj₂ (inj₁ (M′ , M→M′)) = inj₂ (inj₁ (_ , (ξ □⟨ A ⇒ B ⟩ M→M′)))
      ... | inj₂ (inj₂ eq) rewrite eq = inj₂ (inj₁ (_ , (ξ-blame □⟨ A ⇒ B ⟩)))
      ... | inj₁ (v , Vv)
          with A∼B
      ... | ∼★ = {!!}
      ... | ∼-base = {!!}
      ... | ∼-fun dom cod = {!!}
      ... | ★∼ with V-dyn-inv Vv
      ... | V′ , G , eq , v′ , g rewrite eq = {!!}

      G (suc k′) 𝓖Γγk A∼B N (.(⟪ proj₁ γ ⟫ M ⟨ A ⇒ B ⟩) —→⟨ γM→ ⟩ →N) (s≤s ≤k′) = {!!}


      
--       G k 𝓖Γγk A∼B N →N ≤k
--           with fundamental M ⊢M k γ 𝓖Γγk 
--       ... | 𝓔⟦A⟧γMk rewrite E-def A (⟪ proj₁ γ ⟫ M) k
--           with →N
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _ ∎
--           with 𝓔⟦A⟧γMk (⟪ proj₁ γ ⟫ M) (_ ∎) {!!}
--       ... | inj₂ (M′ , M→M′) = inj₂ (_ , (ξ □⟨ A ⇒ B ⟩ M→M′))
--       ... | inj₁ (v , Vv)
--           with A∼B
--       ... | ★∼ = {!!}
--       --       with v
--       -- ... | ƛ̬ N′ = {!!}
--       -- ... | $̬ c = ?
--       -- ... | V 〈 g 〉 = ?
--             -- Need k > 0?
--             -- inj₂ ({!!} , {!!})
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _ ∎ | inj₁ (v , Vv) | ∼★
--           with ground-or-★ A
--       ... | inj₁ refl = inj₂ (_ , (id-★ v))
--       ... | inj₂ (inj₂ (G , AG , ngA)) = inj₂ (_ , (expand v AG ngA))
--       ... | inj₂ (inj₁ gA)
--           with k
--       ... | 0 =
--             let eq_top = V-dyn-zero {v = v}{gA} in
--             inj₁ ((v 〈 gA 〉) , subst (λ X → X) (sym eq_top) tt)
--       ... | suc k′ =
--             let eq = V-dyn {k′}{v = v}{gA} in
--             inj₁ ((v 〈 gA 〉) , subst (λ X → X) (sym eq)
--                                     (mono-𝓥 _ _ A v (≤′-step ≤′-refl) Vv))
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _ ∎ | inj₁ (v , Vv)  | ∼-base =
--           inj₂ (_ , (id-ι v))
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _ ∎ | inj₁ (v , Vv)  | ∼-fun A∼A′ B∼B′ =
--           inj₂ (_ , (wrap v))
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _—→⟨_⟩_ _ {M′} M⟨⟩→M′ M′↠N
--           with M⟨⟩→M′
--       ... | ξ (□⟨ A ⇒ B ⟩) M→M″ = {!!}
--       ... | ξξ-blame (□⟨ A ⇒ B ⟩) eq = {!!}
--       ... | id-ι v
--           with 𝓔⟦A⟧γMk N M′↠N {!!}
--       ... | inj₁ (v′ , Vv′) = inj₁ (v′ , Vv′)
--       ... | inj₂ (N′ , N→N′) rewrite value—↠ v M′↠N =
--             ⊥-elim (value-irreducible v N→N′)
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _—→⟨_⟩_ _ {M′} M⟨⟩→M′ M′↠N | id-★ v = {!!}
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _—→⟨_⟩_ _ {M′} M⟨⟩→M′ M′↠N | wrap v = {!!}
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _—→⟨_⟩_ _ {M′} M⟨⟩→M′ M′↠N | expand v AG ngA = {!!}
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _—→⟨_⟩_ _ {M′} M⟨⟩→M′ M′↠N | collapse v g BG eq = {!!}
--       G k 𝓖Γγk A∼B N →N ≤k | 𝓔⟦A⟧γMk | _—→⟨_⟩_ _ {M′} M⟨⟩→M′ M′↠N | collide v g h BH GH eq = {!!}
      
-- --          let xx = 𝓔⟦A⟧γMk {!!} {!!} in
-- --        {!!}

fundamental .blame ⊢blame = {!!}


-- 𝕍 : (k : ℕ) → (s : ℕ) → Acc _<₂_ (k , s) → (A : Type) → (s ≡ size A) → ValPred
-- 𝔼 : (k : ℕ) → (s : ℕ) → Acc _<₂_ (k , s) → (A : Type) → (s ≡ size A) → ExpPred

-- 𝕍 k s rec ★ seq {.(ƛ N)} (ƛ̬ N) = ⊥
-- 𝕍 k s rec ★ seq {.($ c)} ($̬ c) = ⊥
-- 𝕍 0 s (acc rec) ★ seq {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) = ⊤
-- 𝕍 (suc k) s (acc rec) ★ seq {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) =
--     𝕍 k (size G) (rec (k , size G) (inj₁ ≤-refl)) G refl {V} v

-- 𝕍 k s rec ($ₜ ι) seq {.(ƛ N)} (ƛ̬ N) = ⊥
-- 𝕍 k s rec ($ₜ ι) seq {.($ c)} ($̬_ {ι′} c) = ι ≡ ι′
-- 𝕍 k s rec ($ₜ ι) seq {.(_ ⟨ _ ⇒ ★ ⟩)} (v 〈 g 〉) = ⊥

-- 𝕍 k (suc s) (acc rec) (A ⇒ B) refl {.(ƛ N)} (ƛ̬ N) =
--     ∀ {V} (v : Value V) (j : ℕ) → (lt : j ≤ k)
--       → 𝕍 j (size A) (rec (j , size A) (less-eq-less lt M1)) A refl v
--       → 𝔼 j (size B) (rec (j , size B) (less-eq-less lt M2)) B refl (N [ V ])
--     where M1 = s≤s (m≤m⊔n (size A) (size B))
--           M2 = s≤s (m≤n⊔m (size A) (size B))
-- 𝕍 k s rec (A ⇒ B) seq {.($ c)} ($̬ c) = ⊥
-- 𝕍 k s rec (A ⇒ B) seq {.(_ ⟨ _ ⇒ ★ ⟩)} (v 〈 g 〉) = ⊥

-- {- Probably need to change the following to count steps -}
-- 𝔼 k s rec A seq M = ∀ N → (M→N : M —↠ N)
--                      → (Σ[ v ∈ Value N ] 𝕍 k s rec A seq v)
--                        ⊎ (∃[ N′ ] (N —→ N′))

-- 𝓥⟦_⟧ : (A : Type) → {V : Term} → Value V → ℕ → Set
-- 𝓥⟦ A ⟧ v k = 𝕍 k (size A) (<₂-wellFounded (k , size A)) A refl v

-- 𝓔⟦_⟧ : Type → Term → ℕ → Set
-- 𝓔⟦ A ⟧ M k = 𝔼 k (size A) (<₂-wellFounded (k , size A)) A refl M

-- postulate
--   𝕍-ext : (k : ℕ) → (s : ℕ) → ∀ {IH IH′}
--       -- → (∀{q} (q<p : q <₂ p) → IH q q<p ≡ IH′ q q<p)
--       → 𝕍 k s IH ≡ 𝕍 k s IH′

-- V-base : ∀{n}{ι}{ι′}{k : rep ι′} → 𝓥⟦ $ₜ ι ⟧ ($̬ k) n ≡ (ι ≡ ι′)
-- V-base {n} = refl

-- V-fun : ∀{n}{A B}{N}
--   → 𝓥⟦ A ⇒ B ⟧ (ƛ̬ N) n ≡ ∀ {V} (v : Value V) (j : ℕ) → (lt : j ≤ n)
--                           → 𝓥⟦ A ⟧ v j → 𝓔⟦ B ⟧ (N [ V ]) j
-- V-fun {n} = {!refl!}


-- SafePred : ℕ → Set₁
-- SafePred s = (A : Type) → (s ≡ size A) → ValPred × ExpPred



-- 𝕍 : (n : ℕ) → <-Rec (λ i → SafePred) n → Type → ValPred
-- 𝔼 : (n : ℕ) → <-Rec (λ i → SafePred) n → Type → ExpPred


-- 𝕍 : (n : ℕ) → <-Rec (λ i → SafePred) n → Type → ValPred
-- 𝔼 : (n : ℕ) → <-Rec (λ i → SafePred) n → Type → ExpPred

-- 𝕍 n rec ★ (ƛ̬ N) = ⊥
-- 𝕍 n rec ★ ($̬ k) = ⊥
-- 𝕍 0 rec ★ {(V ⟨ G ⇒ ★ ⟩)} (v 〈 g 〉) = ⊤
-- 𝕍 (suc n) rec ★ {(V ⟨ G ⇒ ★ ⟩)} (v 〈 g 〉) = (proj₁ (rec n (n<1+n n) G)) v

-- 𝕍 n rec ($ₜ ι) (ƛ̬ N) = ⊥
-- 𝕍 n rec ($ₜ ι) ($̬_ {ι′} k) = ι ≡ ι′
-- 𝕍 n rec ($ₜ ι) (v 〈 g 〉) = ⊥

-- 𝕍 0 rec (A ⇒ B) {.(ƛ N)} (ƛ̬ N) = ⊤
-- 𝕍 (suc n) rec (A ⇒ B) {.(ƛ N)} (ƛ̬ N) =
--    ∀ {V} (v : Value V) (j : ℕ) → (lt : j ≤ n)
--      → (proj₁ (rec j (s≤s lt) A)) v
--      → (proj₂ (rec j (s≤s lt) B)) (N [ V ])
-- 𝕍 n rec (A ⇒ B) ($̬ k) = ⊥
-- 𝕍 n rec (A ⇒ B) (v 〈 g 〉) = ⊥

-- {- the following is an experiment in that it does not relate the step
--    index n to the number of reduction steps -}
-- 𝔼 0 rec A M = ⊤
-- -- 𝔼 (suc n) rec A M = ∀ N → (M→N : M —↠ N)
-- --            → (Σ[ v ∈ Value N ] (proj₁ (rec n (s≤s ≤-refl) A)) v)
-- --              ⊎ (∃[ N′ ] (N —→ N′))
-- 𝔼 (suc n) rec A M = ∀ N → (M→N : M —↠ N)
--            → (Σ[ v ∈ Value N ] 𝕍 (suc n) rec A v)
--              ⊎ (∃[ N′ ] (N —→ N′))

-- Safe-step : (n : ℕ) → <-Rec (λ i → SafePred) n → SafePred
-- Safe-step n rec A = 𝕍 n rec A , 𝔼 n rec A

-- abstract
--   Safe : ℕ → SafePred
--   Safe = <-rec (λ i → SafePred) Safe-step

-- 𝓥⟦_⟧ : (A : Type) → {V : Term} → Value V → ℕ → Set
-- 𝓥⟦ A ⟧ v k = proj₁ (Safe k A) v

-- 𝓔⟦_⟧ : Type → Term → ℕ → Set
-- 𝓔⟦ A ⟧ M k = proj₂ (Safe k A) M

-- postulate
--   Safe-step-ext : (x : ℕ) → ∀ {IH IH′}
--       → (∀{y} (y<x : y < x) → IH y y<x ≡ IH′ y y<x)
--       → Safe-step x IH ≡ Safe-step x IH′

-- abstract
--   unfold-Safe : ∀ n → Safe n ≡ Safe-step n (λ n′ _ → Safe n′)
--   unfold-Safe n = FixPoint.unfold-wfRec <-wellFounded (λ i → SafePred)
--                      Safe-step Safe-step-ext {n}

-- {- Equations of the logical relation -}

-- {-
-- V-zero : ∀{A}{V} (v : Value V) → 𝓥⟦ A ⟧ v 0 ≡ ⊤
-- V-zero v rewrite unfold-Safe 0 = refl
-- -}

-- V-base : ∀{n}{ι}{ι′}{k : rep ι′} → 𝓥⟦ $ₜ ι ⟧ ($̬ k) n ≡ (ι ≡ ι′)
-- V-base {n} rewrite unfold-Safe n = refl

-- V-dyn-zero : ∀{G}{V}{v : Value V}{g}
--  → 𝓥⟦ ★ ⟧ {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) 0 ≡ ⊤
-- V-dyn-zero rewrite unfold-Safe 0 = refl 

-- V-dyn : ∀{n}{G}{V}{v : Value V}{g}
--  → 𝓥⟦ ★ ⟧ {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) (suc n) ≡ 𝓥⟦ G ⟧ v n
-- V-dyn {n} rewrite unfold-Safe (suc n) | sym (unfold-Safe n) = refl

-- V-fun-zero : ∀{A B}{N}
--   → 𝓥⟦ A ⇒ B ⟧ (ƛ̬ N) 0 ≡ ⊤
-- V-fun-zero {n} rewrite unfold-Safe 0 = refl

-- V-fun : ∀{n}{A B}{N}
--   → 𝓥⟦ A ⇒ B ⟧ (ƛ̬ N) (suc n) ≡ ∀ {V} (v : Value V) (j : ℕ) → (lt : j ≤ n)
--                                 → 𝓥⟦ A ⟧ v j → 𝓔⟦ B ⟧ (N [ V ]) j
-- V-fun {n} rewrite unfold-Safe (suc n) | sym (unfold-Safe n) = refl

-- E-zero : (A : Type)
--    → (M : Term)
--    → 𝓔⟦ A ⟧ M 0 ≡ ⊤
-- E-zero A M rewrite unfold-Safe 0 = refl

-- E-suc : (A : Type)
--    → (M : Term)
--    → (k : ℕ)
--    → 𝓔⟦ A ⟧ M (suc k) ≡
--        ∀ N → (M→N : M —↠ N)
--              → (Σ[ v ∈ Value N ] 𝓥⟦ A ⟧ v (suc k))
--                ⊎ (∃[ N′ ] (N —→ N′))   
-- E-suc A M k rewrite unfold-Safe (suc k) = refl

-- data Fun : Term → Set where
--   λᶠ : (N : Term) → Fun (ƛ N)

-- V-fun-inv : ∀{n}{A}{B}{V} (v : Value V) → 𝓥⟦ A ⇒ B ⟧ v n →  Fun V
-- V-fun-inv {zero} {A} {B} {.(ƛ N)} (ƛ̬ N) vV = λᶠ N
-- V-fun-inv {suc n} {A} {B} {.(ƛ N)} (ƛ̬ N) vV = λᶠ N
-- V-fun-inv {zero} {A} {B} {.($ k)} ($̬ k) vV rewrite unfold-Safe 0 = ⊥-elim vV
-- V-fun-inv {suc n} {A} {B} {.($ k)} ($̬ k) vV rewrite unfold-Safe (suc n) =
--     ⊥-elim vV
-- V-fun-inv {zero} {A} {B} {.(_ ⟨ _ ⇒ ★ ⟩)} (v 〈 g 〉) vV rewrite unfold-Safe 0 =
--     ⊥-elim vV
-- V-fun-inv {suc n} {A} {B} {.(_ ⟨ _ ⇒ ★ ⟩)} (v 〈 g 〉) vV
--     rewrite unfold-Safe (suc n) = ⊥-elim vV

-- data FunVal : ∀{V : Term} → Value V → Set where
--   fun : ∀{N : Term} → FunVal (ƛ̬ N)

-- V-funval-inv : ∀{n}{A}{B}{V} (v : Value V) → 𝓥⟦ A ⇒ B ⟧ v n →  FunVal v
-- V-funval-inv {zero} {A} {B} {.(ƛ N)} (ƛ̬ N) Vv = fun
-- V-funval-inv {zero} {A} {B} {.($ k)} ($̬ k) Vv rewrite unfold-Safe 0 = ⊥-elim Vv
-- V-funval-inv {zero} {A} {B} {.(_ ⟨ _ ⇒ ★ ⟩)} (v 〈 g 〉) Vv rewrite unfold-Safe 0 = ⊥-elim Vv
-- V-funval-inv {suc n} {A} {B} {.(ƛ N)} (ƛ̬ N) Vv = fun
-- V-funval-inv {suc n} {A} {B} {.($ k)} ($̬ k) Vv rewrite unfold-Safe (suc n) = ⊥-elim Vv
-- V-funval-inv {suc n} {A} {B} {.(_ ⟨ _ ⇒ ★ ⟩)} (v 〈 g 〉) Vv rewrite unfold-Safe (suc n) = ⊥-elim Vv

-- {- Type Safety -}

-- ValSubst : Set
-- ValSubst = Σ[ σ ∈ Subst ] (∀ x → Value (σ x))

-- inc : ValSubst → ValSubst
-- inc σ = (λ x → proj₁ σ (suc x)) , (λ x → proj₂ σ (suc x))

-- 𝓖⟦_⟧ : (Γ : List Type) → ValSubst → ℕ → Set
-- 𝓖⟦ [] ⟧ σ k = ⊤
-- 𝓖⟦ A ∷ Γ ⟧ σ k = 𝓖⟦ Γ ⟧ (inc σ) k × 𝓥⟦ A ⟧ (proj₂ σ 0) k

-- lemma-𝓖 : (Γ : List Type) → (γ : ValSubst) → (k : ℕ) → 𝓖⟦ Γ ⟧ γ k
--   → ∀ {A}{y} → (∋y : Γ ∋ y ⦂ A)
--   → 𝓥⟦ A ⟧ (proj₂ γ y) k
-- lemma-𝓖 [] γ k 𝓖γ ()
-- lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {zero} refl = 𝓥γ0
-- lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {suc y} ∋y =
--   lemma-𝓖 Γ (inc γ) k 𝓖γ ∋y

-- _⊨_⦂_ : List Type → Term → Type → Set
-- Γ ⊨ M ⦂ A = ∀ k (γ : ValSubst) → 𝓖⟦ Γ ⟧ γ k → 𝓔⟦ A ⟧ (⟪ proj₁ γ ⟫ M) k

-- _⊨ⱽ_⦂_ : List Type → {V : Term} → Value V → Type → Set
-- Γ ⊨ⱽ v ⦂ A = ∀ k (γ : ValSubst) → 𝓖⟦ Γ ⟧ γ k → 𝓥⟦ A ⟧ (sub-val (proj₁ γ) v) k

-- mono-𝕍 : ∀ j k A {V}
--     (reck : <-Rec (λ i → SafePred) k)
--     (recj : <-Rec (λ i → SafePred) j)
--     (v : Value V)
--    → j ≤′ k
--    → 𝕍 k reck A v
--    → 𝕍 j recj A v
-- mono-𝕍 j k A reck recj v lt Vk = {!!}

-- mono-SafeVal : ∀ j k A {V} (v : Value V)
--    → j ≤′ k
--    → 𝓥⟦ A ⟧ v k
--    → 𝓥⟦ A ⟧ v j
-- mono-SafeVal j .j A v ≤′-refl Vv = Vv
-- mono-SafeVal zero (suc k) A (ƛ̬ N) (≤′-step lt) Vv
--     rewrite unfold-Safe 0 = {!!}
-- mono-SafeVal (suc j) (suc k) ★ (ƛ̬ N) (≤′-step lt) Vv
--     rewrite unfold-Safe (suc k)
--     with Vv
-- ... | ()
-- mono-SafeVal (suc j) (suc k) ($ₜ ι) (ƛ̬ N) (≤′-step lt) Vv
--     rewrite unfold-Safe (suc k)
--     with Vv
-- ... | ()
-- mono-SafeVal (suc j) (suc k) (A ⇒ B) {ƛ N} (ƛ̬ _) (≤′-step lt) Vv
--     rewrite unfold-Safe (suc j) | unfold-Safe (suc k) = {!!}
--     where
--     G : ∀ {V} (v : Value V) (j₁ : ℕ) (lt₁ : suc j₁ ≤ j)
--         → proj₁ (Safe j₁ A) v → proj₂ (Safe j₁ B) (⟪ V • id ⟫ N)
--     G {V} v j′ j′≤j Vvj′ =
--         -- (≤-trans j′≤j (≤-trans (n≤1+n j) (≤′⇒≤ lt)))
--         Vv v j′ {!!} Vvj′ 
-- mono-SafeVal zero (suc k) A ($̬ c) (≤′-step lt) Vv
--     rewrite unfold-Safe 0 = {!!}
-- mono-SafeVal (suc j) (suc k) ★ ($̬ c) (≤′-step lt) Vv 
--     rewrite unfold-Safe (suc k)
--     with Vv
-- ... | ()
-- mono-SafeVal (suc j) (suc k) ($ₜ ι) ($̬ c) (≤′-step lt) Vv
--     rewrite unfold-Safe (suc j) = {!!}
-- mono-SafeVal (suc j) (suc k) (A ⇒ B) ($̬ c) (≤′-step lt) Vv
--     rewrite unfold-Safe (suc k)
--     with Vv
-- ... | ()
-- mono-SafeVal zero (suc k) A (v 〈 g 〉) (≤′-step lt) Vv
--     rewrite unfold-Safe 0 = {!!}
-- mono-SafeVal (suc j) (suc k) ★ {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) (≤′-step lt) Vv
--     rewrite unfold-Safe (suc j) | unfold-Safe (suc k) =
--     mono-SafeVal j k G v (≤′-trans (≤⇒≤′ (n≤1+n j)) lt) Vv
-- mono-SafeVal (suc j) (suc k) ($ₜ ι) (v 〈 g 〉) (≤′-step lt) Vv
--     rewrite unfold-Safe (suc k)
--     with Vv
-- ... | ()
-- mono-SafeVal (suc j) (suc k) (A ⇒ B) (v 〈 g 〉) (≤′-step lt) Vv
--     rewrite unfold-Safe (suc k)
--     with Vv
-- ... | ()

-- mono-SafeExp : ∀ j k A (M : Term)
--    → j ≤′ k
--    → 𝓔⟦ A ⟧ M k
--    → 𝓔⟦ A ⟧ M j
-- mono-SafeExp j .j A M ≤′-refl EM = EM
-- mono-SafeExp zero (suc k) A M (≤′-step j≤k) EM rewrite unfold-Safe 0 = tt
-- mono-SafeExp (suc j) (suc k) A M (≤′-step j≤k) EM
--   rewrite unfold-Safe (suc j) | unfold-Safe (suc k) = G
--   where
--   G : (N : Term) → M —↠ N →
--       Data.Product.Σ (Value N) (𝕍 (suc j) (λ n′ _ → Safe n′) A)
--       ⊎ Data.Product.Σ Term (_—→_ N)
--   G N M→N
--       with EM N M→N  
--   ... | inj₂ (N′ , N—→N′) = inj₂ (N′ , N—→N′)
--   ... | inj₁ (v , Vk) =
--         inj₁ (v , mono-𝕍 (suc j) (suc k) A (λ n′ _ → Safe n′) (λ n′ _ → Safe n′) v (≤′-step j≤k) Vk)

-- mono-SafeEnv : ∀ j k {Γ} (γ : ValSubst)
--    → j ≤′ k
--    → 𝓖⟦ Γ ⟧ γ k
--    → 𝓖⟦ Γ ⟧ γ j
-- mono-SafeEnv = {!!}

-- Val⇒Exp : ∀{A}{V : Term}{v : Value V} (k : ℕ)
--    → 𝓥⟦ A ⟧ v k
--    → 𝓔⟦ A ⟧ V k
-- Val⇒Exp zero Vv rewrite unfold-Safe 0 = tt
-- Val⇒Exp {A}{V}{v} (suc k) Vv rewrite E-suc A V k =  G
--   where G : (N : Term) → V —↠ N →
--                 Data.Product.Σ (Value N) (proj₁ (Safe (suc k) A)) ⊎
--                 Data.Product.Σ Term (_—→_ N)
--         G N V→N rewrite value—↠ v V→N = inj₁ (v , Vv)

-- {-# REWRITE sub-var #-}

-- fundamental : ∀ {Γ A} → (M : Term)
--   → (Γ ⊢ M ⦂ A)
--     -----------
--   → (Γ ⊨ M ⦂ A)
-- fundamentalⱽ : ∀ {Γ W A} → (w : Value W)
--   → (Γ ⊢ W ⦂ A)
--     ------------
--   → (Γ ⊨ⱽ w ⦂ A)

-- fundamental {Γ}{A} (` x) (⊢` ∋x) k γ 𝓖Γγk  =
--   let Vγx = lemma-𝓖 Γ γ k 𝓖Γγk ∋x in
--   Val⇒Exp {A}{⟪ proj₁ γ ⟫ (` x)} k Vγx
-- fundamental ($ c) (⊢$ ι) k γ 𝓖Γγk = Val⇒Exp {v = $̬ c} k (Vc k)
--   where
--   Vc : ∀ k → 𝓥⟦ $ₜ ι ⟧ ($̬ c) k
--   Vc k rewrite V-base {k}{ι}{ι}{c} = refl
-- fundamental (L · M) (⊢· {A = A}{B} ⊢L ⊢M) 0 γ 𝓖Γγk
--     rewrite E-zero B (⟪ proj₁ γ ⟫ (L · M)) = tt
-- fundamental (L · M) (⊢· {A = A}{B} ⊢L ⊢M) (suc k) γ 𝓖Γγk
--   rewrite E-suc B (⟪ proj₁ γ ⟫ (L · M)) k = G
--   where
--   G : (N : Term) → ⟪ proj₁ γ ⟫ L · ⟪ proj₁ γ ⟫ M —↠ N →
--        Data.Product.Σ (Value N) (proj₁ (Safe (suc k) B)) ⊎
--        Data.Product.Σ Term (_—→_ N)
--   G N γLM—↠N
--       with fundamental L ⊢L (suc k) γ 𝓖Γγk
--   ... | 𝓔γL rewrite E-suc (A ⇒ B) (⟪ proj₁ γ ⟫ L) k 
--       with fundamental M ⊢M (suc k) γ 𝓖Γγk
--   ... | 𝓔γM rewrite E-suc A (⟪ proj₁ γ ⟫ M) k
--       with app-multi-inv γLM—↠N
--   {- Case 1: γ L —↠ L′ -}
--   ... | inj₁ (L′ , γL→L′ , refl , eq)
--       with 𝓔γL L′ γL→L′
--   ... | inj₂ (L″ , L′→L″) =            inj₂ (_ , ξ (□· _) L′→L″)
--   ... | inj₁ (vL′ , VvA→B)
--       with 𝓔γM (⟪ proj₁ γ ⟫ M) (_ ∎)
--   ... | inj₂ (M′ , γM→M′) =            inj₂ (_ , ξ (vL′ ·□) γM→M′)
--   ... | inj₁ (vγM , VvγM)
--       with V-fun-inv vL′ VvA→B
--   ... | λᶠ N =                          inj₂ (_ , β vγM)
--   {- Case 2: γ L —↠ V and γ M —↠ M′ -}
--   G N γLM—↠N | 𝓔γL | 𝓔γM
--       | inj₂ (inj₁ (V , M′ , γL→V , v , γM→M′ , refl , eq))
--       with 𝓔γM M′ γM→M′
--   ... | inj₂ (M″ , M′→M″) =            inj₂ (_ , ξ (v ·□) M′→M″)
--   ... | inj₁ (vM′ , VvM′)
--       with 𝓔γL V γL→V
--   ... | inj₂ (V′ , V→V′) =             ⊥-elim (value-irreducible v V→V′)
--   ... | inj₁ (v′ , Vv)
--       with V-fun-inv v′ Vv
--   ... | λᶠ N =                          inj₂ (_ , β vM′)
--   {- Case 3: γ L —↠ V and γ M —↠ W and V · W —↠ N -}
--   G N γLM—↠N | 𝓔γL | 𝓔γM
--       | inj₂ (inj₂ (V , W , γL→V , v , γM→W , w , VW→N , eq))
--       with 𝓔γL V γL→V
--   ... | inj₂ (V′ , V→V′) =             ⊥-elim (value-irreducible v V→V′)
--   ... | inj₁ (v′ , Vv)
--       with V-funval-inv v′ Vv
--   ... | fun{N′} rewrite V-fun {k}{A}{B}{N′} 
--       with 𝓔γM W γM→W
--   ... | inj₂ (W′ , W→W′) =             ⊥-elim (value-irreducible w W→W′)
--   ... | inj₁ (w′ , Vw) = 
--       let 𝓔N′k : 𝓔⟦ B ⟧ (⟪ W • id ⟫ N′) k
--           𝓔N′k = Vv w′ _ ≤-refl (mono-SafeVal k _ A w′ (≤′-step ≤′-refl) Vw) in
--           {- Now we're stuck because k could be zero. -}
--         {!!}

-- fundamental {Γ}{A = A ⇒ B}(ƛ N) (⊢ƛ ⊢N) k γ 𝓖Γγk =
--   Val⇒Exp {V = ⟪ proj₁ γ ⟫ (ƛ N)}{ƛ̬ ⟪ ext (proj₁ γ) ⟫ N} k (G k 𝓖Γγk)
--   where
--     G : ∀ k → 𝓖⟦ Γ ⟧ γ k → 𝓥⟦ A ⇒ B ⟧ (ƛ̬ ⟪ ext (proj₁ γ) ⟫ N) k
--     G zero 𝓖Γγk rewrite V-fun-zero {A}{B}{⟪ ext (proj₁ γ) ⟫ N} = tt
--     G (suc k) 𝓖Γγk rewrite V-fun {k}{A}{B}{⟪ ext (proj₁ γ) ⟫ N} = H
--       where
--       H : ∀ {V} (v : Value V) (j : ℕ) → j ≤ k
--         → 𝓥⟦ A ⟧ v j
--         → 𝓔⟦ B ⟧ ((⟪ ext (proj₁ γ) ⟫ N) [ V ]) j
--       H {V} v j lt Vvj =
--         fundamental N ⊢N j γ′ (mono-SafeEnv j (suc k) _ lt2 𝓖Γγk , Vvj)
--         where γ′ = (V • proj₁ γ , λ { zero → v ; (suc x) → proj₂ γ x})
--               lt2 = (≤⇒≤′ (≤-trans lt (n≤1+n k)))
-- fundamental (M ⟨ A ⇒ B ⟩) (⊢⟨⇒⟩ ⊢M) = {!!}
-- fundamental blame ⊢blame = {!!}

-- fundamentalⱽ w ⊢W = {!!}

