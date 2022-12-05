{-# OPTIONS --without-K --rewriting #-}
{-
  This is based on Peter Thiemann's Agda development for LambdaRec.
-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var

module rewriting.examples.LambdaRec where

data Op : Set where
  op-lam : Op
  op-app : Op
  op-rec : Op
  op-lit : ℕ → Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-rec = (ν ■) ∷ []
sig (op-lit n) = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term)

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern μ N  = op-rec ⦅ cons (bind (ast N)) nil ⦆
pattern $ k = (op-lit k) ⦅ nil ⦆

{-------------      Examples regarding substitution   -------------}

sub-app : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app = λ L M σ → refl

sub-lam : ∀ (N : Term) (σ : Subst) → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ ` 0 • (σ ⨟ ↑) ⟫ N)
sub-lam N σ = refl

_ : ∀ (M L : Term) → (M • L • id) 0 ≡ M
_ = λ M L → refl

_ : ∀ (M L : Term) → (M • L • id) 1 ≡ L
_ = λ M L → refl

_ : ∀ (M L : Term) → (M • L • id) 2 ≡ ` 0
_ = λ M L → refl

_ : ∀ (M L : Term) → (M • L • id) 3 ≡ ` 1
_ = λ M L → refl

{-# REWRITE sub-var #-}

_ : ∀ (M L : Term) → ⟪ M • L • id ⟫ (` 1 · ` 0) ≡ L · M
_ = λ M L → refl

_ : ∀ (M : Term) → ⟪ M • id ⟫ (` 1 · ` 0) ≡ ` 0 · M
_ = λ M → refl

_ : ∀ (N L : Term) → ((` 1 · ` 0) [ N ] ) [ L ] ≡ (L · N [ L ])
_ = λ N L → refl

{-------------      Reduction Semantics    -------------}

data Value : Term → Set where

  V-lit : ∀ {k : ℕ}
      ---------------------------
    → Value ($ k)
    
  V-ƛ : ∀ {N : Term}
      ---------------------------
    → Value (ƛ N)

  V-μ : ∀ {V : Term}
    → Value V
      -----------
    → Value (μ V)

value? : (M : Term) → Dec (Value M)
value? (` x) = no λ ()
value? ($ n) = yes V-lit
value? (ƛ n) = yes V-ƛ
value? (L · M) = no λ ()
value? (μ V)
    with value? V
... | yes v = yes (V-μ v)
... | no ¬v = no λ { (V-μ v) → ¬v v }

infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M : Term}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′ : Term}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {N W : Term}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  β-μ : ∀ {V W}
    → Value V
    → Value W
      ----------------------------
    → (μ V) · W —→ (V [ μ V ]) · W


{---  Reflexive and transitive closure ----}

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

{----------------- Type System ------------------------}

data Type : Set where
  `ℕ   : Type
  _⇒_   : Type → Type → Type

infix  4  _⊢_⦂_

data _⊢_⦂_ : List Type → Term → Type → Set

data _⊢_⦂_ where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  ⊢$ : ∀ {Γ k}
      -------------
    → Γ ⊢ $ k ⦂ `ℕ

  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢ƛ : ∀ {Γ N A B}
    → A ∷ Γ ⊢ N ⦂ B
      ---------------
    → Γ ⊢ ƛ N ⦂ A ⇒ B

  ⊢μ : ∀ {Γ V A B}
    → Value V
    → (A ⇒ B) ∷ Γ ⊢ V ⦂ A ⇒ B
      -----------------------
    → Γ ⊢ μ V ⦂ A ⇒ B

{-------------      Proof of Progress    -------------}

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → [] ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢$)                               =  done V-lit
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢μ v ⊢V)                          =  done (V-μ v)
progress (⊢· ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ
    with progress ⊢M
... | step M—→M′                            =  step (ξ-·₂ V-ƛ M—→M′)
... | done w                                =  step (β-ƛ w)
progress (⊢· ⊢L ⊢M) | done (V-μ v)
    with progress ⊢M
... | step M—→M′                            =  step (ξ-·₂ (V-μ v) M—→M′)
... | done w                                =  step (β-μ v w)

{-------------      Proof of Preservation    -------------}

_⦂_⇒_ : Subst → List Type → List Type → Set
_⦂_⇒_ σ Γ Δ = ∀ {x : Var} {A : Type} → Γ ∋ x ⦂ A  → Δ ⊢ σ x ⦂ A

open Renaming

ext-ren-pres : ∀ {ρ : Rename} {Γ Δ : List Type} {A : Type}
  → ren ρ        ⦂ Γ       ⇒ Δ
  → ext (ren ρ)  ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-ren-pres {ρ}{Γ}{Δ} ρ⦂ {zero} refl = ⊢` refl
ext-ren-pres {ρ}{Γ}{Δ}{A} ρ⦂ {suc x} {B} ∋x = G
    where
    ρx⦂ : Δ ∋ ρ x ⦂ B
    ρx⦂  with ρ⦂ ∋x
    ... | ⊢ρx rewrite ren-def ρ x
        with ⊢ρx
    ... | ⊢` ∋ρx = ∋ρx

    G : (A ∷ Δ) ⊢ (ren ρ ⨟ ↑) x ⦂ B
    G rewrite seq-def (ren ρ) ↑ x | ren-def ρ x | up-var (ρ x) = ⊢` ρx⦂

sub-value : ∀ {σ V}
  → Value V
  → Value (⟪ σ ⟫ V)
sub-value {σ} {.($ _)} V-lit = V-lit
sub-value {σ} {.(ƛ _)} V-ƛ = V-ƛ
sub-value {σ} {.(μ _)} (V-μ v) = V-μ (sub-value{σ = ext σ} v)

ren-preserve : ∀ {Γ Δ A}{ρ} (M : Term)
   → Γ ⊢ M ⦂ A
   → ren ρ ⦂ Γ ⇒ Δ
   → Δ ⊢ ⟪ ren ρ ⟫ M ⦂ A
ren-preserve (` x) (⊢` ∋x) ρ⦂ = ρ⦂ ∋x
ren-preserve ($ n) (⊢$) ρ⦂ = ⊢$
ren-preserve {ρ = ρ} (L · M) (⊢· ⊢L ⊢M) ρ⦂ =
    ⊢· (ren-preserve{ρ = ρ} L ⊢L ρ⦂) (ren-preserve{ρ = ρ} M ⊢M ρ⦂)
ren-preserve {ρ = ρ} (ƛ N) (⊢ƛ ⊢N) ρ⦂ =
  ⊢ƛ (ren-preserve {ρ = extr ρ} N ⊢N (λ{x} → ext-ren-pres{ρ = ρ} ρ⦂ {x}))
ren-preserve {ρ = ρ} (μ V) (⊢μ v ⊢V) ρ⦂ =
  ⊢μ (sub-value{σ = ren (extr ρ) } v)
     (ren-preserve {ρ = extr ρ} V ⊢V (λ{x} → ext-ren-pres{ρ = ρ} ρ⦂ {x}))

ext-sub-pres : ∀ {σ : Subst} {Γ Δ : List Type} {A : Type}
    → σ     ⦂ Γ       ⇒ Δ
    → ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-sub-pres {σ} σ⦂ {zero} refl = ⊢` refl
ext-sub-pres {σ}{Γ}{Δ}{A} σ⦂ {suc x} {B} ∋x rewrite seq-def σ ↑ x | up-def =
    ren-preserve {ρ = suc} (σ x) (σ⦂ ∋x) ren-suc
    where
    ren-suc : ren suc ⦂ Δ ⇒ (A ∷ Δ)
    ren-suc {y}{C} ∋y rewrite ren-def suc y = ⊢` ∋y

sub-preserve : ∀ {Γ Δ A}{σ} (M : Term)
   → Γ ⊢ M ⦂ A
   → σ ⦂ Γ ⇒ Δ
   → Δ ⊢ ⟪ σ ⟫ M ⦂ A
sub-preserve (` x) (⊢` ∋x) σ⦂ = σ⦂ ∋x
sub-preserve ($ n) (⊢$) σ⦂ = ⊢$
sub-preserve {σ = σ} (L · M) (⊢· ⊢L ⊢M) σ⦂ =
    ⊢· (sub-preserve{σ = σ} L ⊢L σ⦂) (sub-preserve{σ = σ} M ⊢M σ⦂)
sub-preserve {σ = σ} (ƛ N) (⊢ƛ ⊢N) σ⦂ =
  ⊢ƛ (sub-preserve {σ = ext σ} N ⊢N (λ{x} → ext-sub-pres{σ = σ} σ⦂ {x}))
sub-preserve {σ = σ} (μ V) (⊢μ v ⊢V) σ⦂ =
  ⊢μ (sub-value{σ = ext σ} v)
     (sub-preserve {σ = ext σ} V ⊢V (λ{x} → ext-sub-pres{σ = σ} σ⦂ {x}))

preserve-substitution : ∀{Γ : List Type}{A B : Type} (N M : Term)
  → (A ∷ Γ) ⊢ N ⦂ B
  → Γ ⊢ M ⦂ A
  → Γ ⊢ N [ M ] ⦂ B
preserve-substitution {Γ}{A} N M ⊢N ⊢M =
    sub-preserve {σ = M • id} N ⊢N
        λ { {0}{A} refl → ⊢M ; {suc x}{A} ∋x → ⊢` ∋x }

preserve : ∀ {Γ M N A}
  → Γ ⊢ M ⦂ A
  → M —→ N
    ----------
  → Γ ⊢ N ⦂ A
preserve (⊢· ⊢L ⊢M) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M 
preserve (⊢· ⊢L ⊢M) (ξ-·₂ v M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) 
preserve (⊢· (⊢ƛ ⊢N) ⊢M) (β-ƛ v) = preserve-substitution _ _ ⊢N ⊢M
preserve (⊢· (⊢μ {V = V} v ⊢V) ⊢M) (β-μ u w) =
  ⊢· (preserve-substitution V (μ V) ⊢V (⊢μ v ⊢V)) ⊢M

{- Auxilliary Definitions -}

len : ∀ {M}{N} → M —↠ N → ℕ
len (_ ∎) = 0
len (_ —→⟨ x ⟩ M—↠N) = suc (len M—↠N)

irred : Term → Set
irred M = ¬ (∃[ N ](M —→ N))

{- Logical Relation for Type Safety -}

𝓥⟦_⟧ : Type → Term → ℕ → Set
𝓔⟦_⟧ : Type → Term → ℕ → Set

𝓥⟦ A ⇒ B ⟧ W@(ƛ N) k = ∀ j → j < k → ∀ V → 𝓥⟦ A ⟧ V j → 𝓔⟦ B ⟧ (N [ V ]) j
𝓥⟦ A ⇒ B ⟧ (` x) k = ⊥
𝓥⟦ A ⇒ B ⟧ ($ n) k = ⊥
𝓥⟦ A ⇒ B ⟧ (L · M) k = ⊥
𝓥⟦ A ⇒ B ⟧ W@(μ W′) zero = Value W′
𝓥⟦ A ⇒ B ⟧ W@(μ W′) (suc k) = Value W′ × 𝓥⟦ A ⇒ B ⟧ (W′ [ W ]) k

𝓥⟦ `ℕ ⟧ (` x) k = ⊥
𝓥⟦ `ℕ ⟧ ($ n) k = ⊤
𝓥⟦ `ℕ ⟧ (ƛ _) k = ⊥
𝓥⟦ `ℕ ⟧ (μ W) k = ⊥
𝓥⟦ `ℕ ⟧ (L · M) k = ⊥

𝓔⟦ A ⟧ M k =
  ∀ j → j < k → ∀ N → (M—↠N : M —↠ N) → len M—↠N ≡ j → 
       𝓥⟦ A ⟧ N (k ∸ j) ⊎ ∃[ N′ ] (N —→ N′)

{- 𝓥 implies value -}

𝓥⇒Value : ∀{A}{k} → (V : Term) → 𝓥⟦ A ⟧ V k → Value V
𝓥⇒Value {`ℕ} {k} (` x) ()
𝓥⇒Value {`ℕ} {k} ($ n) 𝓥V = V-lit
𝓥⇒Value {`ℕ} {k} (ƛ N) ()
𝓥⇒Value {`ℕ} {k} (L · M) ()
𝓥⇒Value {`ℕ} {k} (μ V) ()
𝓥⇒Value {A ⇒ B} {k} (` x) ()
𝓥⇒Value {A ⇒ B} {k} ($ n) ()
𝓥⇒Value {A ⇒ B} {k} (ƛ N) 𝓥V = V-ƛ
𝓥⇒Value {A ⇒ B} {k} (L · M) ()
𝓥⇒Value {A ⇒ B} {0} (μ N) 𝓥V = V-μ 𝓥V
𝓥⇒Value {A ⇒ B} {suc k} (μ N) ⟨ v , 𝓥V ⟩ = V-μ v

{- Semantic Type Safety -}

𝓖⟦_⟧ : (Γ : List Type) → Subst → ℕ → Set
𝓖⟦ [] ⟧ σ k = ⊤
𝓖⟦ A ∷ Γ ⟧ σ k = 𝓖⟦ Γ ⟧ (λ x → (σ (suc x))) k × 𝓥⟦ A ⟧ (σ 0) k

lemma-𝓖 : (Γ : List Type) → (γ : Subst) → (k : ℕ) → 𝓖⟦ Γ ⟧ γ k
  → ∀ {A}{y} → (∋y : Γ ∋ y ⦂ A)
  → 𝓥⟦ A ⟧ (γ y) k
lemma-𝓖 [] γ k 𝓖γ ()
lemma-𝓖 (A ∷ Γ) γ k ⟨ 𝓖γ , 𝓥γ0 ⟩ {B} {zero} refl = 𝓥γ0
lemma-𝓖 (A ∷ Γ) γ k ⟨ 𝓖γ , 𝓥γ0 ⟩ {B} {suc y} ∋y =
  lemma-𝓖 Γ (λ z → γ (suc z)) k 𝓖γ ∋y

_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ k (γ : Subst) → 𝓖⟦ Γ ⟧ γ k → 𝓔⟦ A ⟧ (⟪ γ ⟫ M) k

_⊨ⱽ_⦂_ : List Type → Term → Type → Set
Γ ⊨ⱽ V ⦂ A = ∀ k (γ : Subst) → 𝓖⟦ Γ ⟧ γ k → 𝓥⟦ A ⟧ (⟪ γ ⟫ V) k

safe : Term → Set
safe M = ∀ N → (M —↠ N) → Value N ⊎ ∃[ N′ ]( N —→ N′ )

safety : ∀ M A → [] ⊨ M ⦂ A → safe M
safety M A ⊨M⦂A N M—↠N
   with ⊨M⦂A (suc (len M—↠N)) id tt (len M—↠N) (≤-pred (s≤s (s≤s ≤-refl)))
             N M—↠N refl 
... | inj₁ 𝓥 = inj₁ (𝓥⇒Value N 𝓥)
... | inj₂ ⟨ N′ , red ⟩ = inj₂ ⟨ N′ , red ⟩

