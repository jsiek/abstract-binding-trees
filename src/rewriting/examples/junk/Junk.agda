data Op : Set where
  op-delta : Op
  op-app : Op
  op-lit : ℕ → Op
  op-cons : Op
  op-fst : Op
  op-snd : Op
  op-let : Op

sig : Op → List Sig
sig op-delta = ν ■ ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit k) = []
sig op-cons = ■ ∷ ■ ∷ []
sig op-fst = ■ ∷ []
sig op-snd = ■ ∷ []
sig op-let = ■ ∷ ν ■ ∷ []

open import rewriting.AbstractBindingTree Op sig hiding (`_)
open import rewriting.AbstractBindingTree Op sig
  using (`_) renaming (ABT to Term) public

pattern $ k  = op-lit k ⦅ nil ⦆

pattern δ N  = op-delta ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

infixl 7  ⟨_,_⟩
pattern ⟨_,_⟩ L M = op-cons ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern fst L = op-fst ⦅ (cons (ast L) nil) ⦆

pattern snd L = op-snd ⦅ (cons (ast L) nil) ⦆

infix 7 LET_IN_
pattern LET_IN_ M N = op-let ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆

{-------------      Examples regarding substitution   -------------}

sub-app : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app = λ L M σ → refl

sub-delta : ∀ (N : Term) (σ : Subst) → ⟪ σ ⟫ (δ N) ≡ δ (⟪ ` 0 • (σ ⨟ ↑) ⟫ N)
sub-delta N σ = refl

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

  V-$ : ∀ {k : ℕ}
      ---------------------------
    → Value ($ k)

  V-δ : ∀ {N : Term}
      ---------------------------
    → Value (δ N)

  V-cons : ∀ {M N : Term}
    → Value M
    → Value N
      ---------------------------
    → Value ⟨ M , N ⟩


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

  β-δ : ∀ {N W : Term}
    → Value W
      --------------------
    → (δ N) · W —→ N [ W ]

  ξ-cons₁ : ∀ {L L′ M : Term}
    → L —→ L′
      ---------------
    → ⟨ L , M ⟩ —→ ⟨ L′ , M ⟩

  ξ-cons₂ : ∀ {V M M′ : Term}
    → Value V
    → M —→ M′
      ---------------
    → ⟨ V , M ⟩ —→ ⟨ V , M′ ⟩
    
  ξ-fst : ∀ {L L′ : Term}
    → L —→ L′
      ---------------
    → fst L —→ fst L′

  ξ-snd : ∀ {L L′ : Term}
    → L —→ L′
      ---------------
    → snd L —→ snd L′

  β-fst : ∀ {V W : Term}
    → Value V
    → Value W
      --------------------
    → fst ⟨ V , W ⟩ —→ V

  β-snd : ∀ {V W : Term}
    → Value V
    → Value W
      --------------------
    → snd ⟨ V , W ⟩ —→ W

  ξ-let : ∀ {M M′ N : Term}
    → M —→ M′
      -------------------------
    → LET M IN N —→ LET M′ IN N
    
  β-let : ∀ {V N : Term}
    → Value V
      --------------------
    → LET V IN N —→ N [ V ]

{-------------      Type System    -------------}


data Type : Set where
  Nat   : Type
  _⇒_   : Type → Type → Type
  _`×_  : Type → Type → Type

open import Var

𝑃 : (op : Op) → Vec Type (length (sig op)) → BTypes Type (sig op) → Type → Set
𝑃 op-delta (B ∷̌ []̌) ( ( A , tt ) , tt ) A→B = A→B ≡ A ⇒ B
𝑃 op-app (A→B ∷̌ A ∷̌ []̌) ( tt , ( tt , tt )) B = A→B ≡ A ⇒ B
𝑃 (op-lit k) []̌ tt A = A ≡ Nat
𝑃 op-cons (A ∷̌ B ∷̌ []̌) ( tt , ( tt , tt )) C = C ≡ A `× B
𝑃 op-fst (A×B ∷̌ []̌) ( tt , tt) A = ∃[ B ] (A×B ≡ A `× B)
𝑃 op-snd (A×B ∷̌ []̌) ( tt , tt) B = ∃[ A ] (A×B ≡ A `× B)
𝑃 op-let (A ∷̌ B ∷̌ []̌) ( tt , (( A′ , tt ) , tt)) C = C ≡ B × A ≡ A′

open import rewriting.ABTPredicate Op sig 𝑃

{-------------      Type System Rules    -------------}

pattern ⊢` ∋x = var-p ∋x
pattern ⊢$ k eq = op-p {op = (op-lit k)} nil-p eq
pattern ⊢δ ⊢N eq = op-p {op = op-delta} (cons-p (bind-p (ast-p ⊢N)) nil-p) eq
pattern ⊢· ⊢L ⊢M eq = op-p {op = op-app}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) eq
pattern ⊢cons ⊢L ⊢M eq = op-p {op = op-cons}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) eq
pattern ⊢fst ⊢L eq = op-p {op = op-fst} (cons-p (ast-p ⊢L) nil-p) eq
pattern ⊢snd ⊢L eq = op-p {op = op-snd} (cons-p (ast-p ⊢L) nil-p) eq
pattern ⊢let ⊢M ⊢N eq = op-p {op = op-let} (cons-p (ast-p ⊢M) (cons-p (bind-p (ast-p ⊢N)) nil-p)) eq

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

progress (⊢$ k _)                           =  done V-$

progress (⊢δ ⊢N _)                          =  done V-δ

progress (⊢· ⊢L ⊢M eq)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-δ
    with progress ⊢M
... | step M—→M′                            =  step (ξ-·₂ V-δ M—→M′)
... | done v                                =  step (β-δ v)
progress (⊢· ⊢L ⊢M eq)
    | done (V-cons v w)
    with ⊢L | eq
... | ⊢cons ⊢V ⊢W refl | ()
progress (⊢· ⊢L ⊢M eq)
    | done V-$
    with ⊢L | eq
... | ⊢$ k refl | ()

progress (⊢cons ⊢L ⊢M eq)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-cons₁ L—→L′)
... | done v
    with progress ⊢M
... | step M—→M′                            =  step (ξ-cons₂ v M—→M′)
... | done w                                =  done (V-cons v w)

progress (⊢fst ⊢L eq)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-fst L—→L′)
... | done (V-cons v w)                     =  step (β-fst v w)
progress (⊢fst ⊢L eq)
    | done V-δ
    with ⊢L | eq
... | ⊢δ ⊢N refl | ()
progress (⊢fst ⊢L eq)
    | done V-$
    with ⊢L | eq
... | ⊢$ k refl | ()

progress (⊢snd ⊢L eq)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-snd L—→L′)
... | done (V-cons v w)                     =  step (β-snd v w)
progress (⊢snd ⊢L eq)
    | done V-δ
    with ⊢L | eq
... | ⊢δ ⊢N refl | ()
progress (⊢snd ⊢L eq)
    | done V-$
    with ⊢L | eq
... | ⊢$ k refl | ()

progress (⊢let ⊢M ⊢N eq)
    with progress ⊢M
... | step M—→M′                             =  step (ξ-let M—→M′)
... | done v                                 =  step (β-let v)

{-------------      Proof of Preservation    -------------}

preserve : ∀ {Γ M N A}
  → Γ ⊢ M ⦂ A
  → M —→ N
    ----------
  → Γ ⊢ N ⦂ A
preserve (⊢· ⊢L ⊢M refl) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M refl
preserve (⊢· ⊢L ⊢M refl) (ξ-·₂ v M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) refl
preserve {Γ}{(δ N) · M}{_}{B} (⊢· (⊢δ ⊢N refl) ⊢M refl) (β-δ {N = N} v) =
    preserve-substitution ⊢N ⊢M
preserve {Γ} {.(⟨ _ , _ ⟩)} {_} {B} (⊢cons ⊢M ⊢N refl) (ξ-cons₁ red) =
    ⊢cons (preserve ⊢M red) ⊢N refl
preserve {Γ} {.(⟨ _ , _ ⟩)} {_} {B} (⊢cons ⊢M ⊢N refl) (ξ-cons₂ v red) =
   ⊢cons ⊢M (preserve ⊢N red) refl
preserve {Γ} {.(fst _)} {_} {A} (⊢fst ⊢L (B , refl)) (ξ-fst red) =
    ⊢fst (preserve ⊢L red) (B , refl)
preserve {Γ} {.(snd _)} {_} {B} (⊢snd ⊢L (A , refl)) (ξ-snd red) =
    ⊢snd (preserve ⊢L red) (A , refl)
preserve {Γ} {.(fst ⟨ _ , _ ⟩)} {_} {B} (⊢fst (⊢cons ⊢V ⊢W refl) (_ , refl)) (β-fst v w) = ⊢V
preserve {Γ} {.(snd ⟨ _ , _ ⟩)} {_} {B} (⊢snd (⊢cons ⊢V ⊢W refl) (_ , refl)) (β-snd v w) = ⊢W
preserve (⊢let ⊢V ⊢N (refl , refl)) (β-let v) = preserve-substitution ⊢N ⊢V
preserve (⊢let ⊢M ⊢N (refl , refl)) (ξ-let red) = ⊢let (preserve ⊢M red) ⊢N (refl , refl)

{- TODO: Add confluence proof to show off the substitution lemma. -}

{-------------      Denotational Semantics    -------------}

{- Denotations of Terms -}
⟦_⟧ : Term → (List D) → D
⟦ ` x ⟧ ρ = nth x ρ ⊥′
⟦ $ k ⟧ ρ v = (v ≡ lit k)
⟦ δ N ⟧ ρ = Λ (λ d₀ → Λ (λ d₁ → ⟦ N ⟧ (d₀ ∷ d₁ ∷ [])))
⟦ L · M ⟧ ρ = ⟦ L ⟧ ρ ● ⟦ M ⟧ ρ 
⟦ ⟨ L , M ⟩ ⟧ ρ =  ⦅ ⟦ L ⟧ ρ , ⟦ M ⟧ ρ ⦆
⟦ fst L ⟧ ρ = π₁ (⟦ L ⟧ ρ)
⟦ snd L ⟧ ρ = π₂ (⟦ L ⟧ ρ)
⟦ LET M IN N ⟧ ρ = ⟦ N ⟧ (⟦ M ⟧ ρ ∷ ρ)



{-------------      Type System    -------------}


data Type : Set where
  Bot   : Type
  _⇒_   : Type → Type → Type

open import Var

𝑉 : List Type → Var → Type → Type → Set
𝑉 Γ x A B = A ≡ B

𝑃 : (op : Op) → Vec Type (length (sig op)) → BTypes Type (sig op) → Type → Set
𝑃 op-lam (B ∷̌ []̌) ⟨ ⟨ A , tt ⟩ , tt ⟩ A→B = A→B ≡ A ⇒ B
𝑃 op-app (A→B ∷̌ A ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ B = A→B ≡ A ⇒ B

open import rewriting.ABTPredicate Op sig 𝑉 𝑃

pattern ⊢` ∋x = var-p ∋x refl
pattern ⊢ƛ ⊢N eq = op-p {op = op-lam} (cons-p (bind-p (ast-p ⊢N)) nil-p) eq
pattern ⊢· ⊢L ⊢M eq = op-p {op = op-app}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) eq


{-------------      Proof of Progress    -------------}

data Value : Term → Set where

  V-ƛ : ∀ {N : Term}
      ---------------------------
    → Value (ƛ N)

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
progress (⊢ƛ ⊢N _)                          =  done V-ƛ
progress (⊢· ⊢L ⊢M _)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ                              =  step β-ƛ

{-------------      Proof of Preservation    -------------}

open SubstPreserve (λ x → refl) (λ x → x) (λ x → x) (λ x → x) (λ {refl ⊢M → ⊢M})
  using (preserve-substitution)

preserve : ∀ {Γ M N A}
  → Γ ⊢ M ⦂ A
  → M —→ N
    ----------
  → Γ ⊢ N ⦂ A
preserve (⊢· ⊢L ⊢M refl) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M refl
preserve (⊢· ⊢L ⊢M refl) (ξ-·₂ M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) refl
preserve (⊢ƛ ⊢M refl) (ξ-ƛ M—→N) = ⊢ƛ (preserve ⊢M M—→N) refl
preserve {Γ}{(ƛ N) · M}{_}{B} (⊢· (⊢ƛ ⊢N refl) ⊢M refl) β-ƛ =
    preserve-substitution N M ⊢N ⊢M

