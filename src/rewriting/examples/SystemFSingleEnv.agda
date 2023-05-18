{-# OPTIONS --rewriting #-}
{-
  UNDER CONSTRUCTION
-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; map; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤?_; _∸_; s≤s)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Function using (_∘_)
open import Sig

module rewriting.examples.SystemFSingleEnv where

open import rewriting.examples.SystemF

{-------------      Type System    -------------}

open import Var using (Var)

data Cat : Set where
  trm : Type → Cat
  typ : Cat

TyEnv : Set
TyEnv = List Cat

{-

  Type variables and term variables are independently numbered.
  For example,

  Λα.λ x:α. x
  is
  Λ.λ:0.0

-}

data _∋_⦂_ : TyEnv → Var → Cat → Set where
  trmZ : ∀{Γ}{A} → (trm A ∷ Γ) ∋ zero ⦂ trm A
  trmStrm : ∀{Γ}{A}{B}{x}
     → Γ ∋ x ⦂ trm A
     → (trm B ∷ Γ) ∋ suc x ⦂ trm A
  typtrm : ∀{Γ}{A}{x}
     → Γ ∋ x ⦂ trm A
     → (typ ∷ Γ) ∋ x ⦂ trm (⟪ renᵗ suc ⟫ᵗ A)
  typZ : ∀{Γ} → (typ ∷ Γ) ∋ zero ⦂ typ
  typStyp : ∀{Γ}{x}
     → Γ ∋ x ⦂ typ
     → (typ ∷ Γ) ∋ suc x ⦂ typ
  trmStyp : ∀{Γ}{B}{x}
     → Γ ∋ x ⦂ typ
     → (trm B ∷ Γ) ∋ x ⦂ typ

{- Well-formed Types -}

infix 1 _⊢_ok
data _⊢_ok : TyEnv → Type → Set where

  ⊢-Nat : ∀{Γ}
       ----------
     → Γ ⊢ Nat ok
     
  ⊢-Var : ∀{Γ}{x}
     → Γ ∋ x ⦂ typ
       -----------
     → Γ ⊢ ^ x ok

  ⊢-⇒ : ∀{Γ}{A}{B}
     → Γ ⊢ A ok
     → Γ ⊢ B ok
       ------------
     → Γ ⊢ A ⇒ B ok

  ⊢-∀ :  ∀{Γ}{A}
     → typ ∷ Γ ⊢ A ok
       --------------
     → Γ ⊢ ∀̇ A ok

{- Well-typed Terms -}

infix 1 _⊢_⦂_
data _⊢_⦂_ : TyEnv → Term → Type → Set where

  ⊢-nat : ∀{Γ} → ∀ n
        -----------------
      → Γ ⊢ $ n ⦂ Nat

  ⊢-var : ∀{Γ}{x}{A}
      → Γ ∋ x ⦂ trm A
        ---------------
      → Γ ⊢ ` x ⦂ A

  ⊢-lam : ∀{Γ}{N}{A}{B}
     → Γ ⊢ A ok
     → trm A ∷ Γ ⊢ N ⦂ B
       -------------------
     → Γ ⊢ ƛ N ⦂ A ⇒ B
     
  ⊢-app : ∀{Γ}{L}{M}{A}{B}
     → Γ ⊢ L ⦂ A ⇒ B
     → Γ ⊢ M ⦂ A
       -----------------
     → Γ ⊢ L · M ⦂ B

  ⊢-tyabs : ∀{Γ}{N}{A}
     → typ ∷ Γ ⊢ N ⦂ A
       ------------------------------------
     → Γ ⊢ Λ N ⦂ ∀̇ A

  ⊢-tyapp : ∀{Γ}{L}{A}{B}
     → Γ ⊢ L ⦂ ∀̇ A
     → Γ ⊢ B ok
       -----------------------
     → Γ ⊢ L [·] ⦂ A ⦗ B ⦘


{-------------      Proof of Preservation    -------------}

okren : Renameᵗ → TyEnv → TyEnv → Set
okren ρ Γ Γ′ = ∀ x → Γ ∋ x ⦂ typ → Γ′ ∋ ρ x ⦂ typ

ext-okren : ∀{ρ}{Γ}{Γ′}
   → okren ρ Γ Γ′
   → okren (extrᵗ ρ) (typ ∷ Γ) (typ ∷ Γ′)
ext-okren {ρ} {Γ} {Γ′} ⊢ρ .zero typZ = typZ
ext-okren {ρ} {Γ} {Γ′} ⊢ρ (suc x) (typStyp ∋x) = typStyp (⊢ρ x ∋x)

ren-pres-ok : ∀{Γ}{Γ′}{ρ}{A}
  → Γ ⊢ A ok
  → okren ρ Γ Γ′
  → Γ′ ⊢ ⟪ renᵗ ρ ⟫ᵗ A ok
ren-pres-ok {Γ} {Γ′} {ρ} {.Nat} ⊢-Nat ⊢ρ = ⊢-Nat
ren-pres-ok {Γ} {Γ′} {ρ} {^ x} (⊢-Var ∋x) ⊢ρ
  rewrite sub-varᵗ (renᵗ ρ) x | ren-defᵗ ρ x = ⊢-Var (⊢ρ x ∋x)
ren-pres-ok {Γ} {Γ′} {ρ} {.(_ ⇒ _)} (⊢-⇒ ⊢A ⊢B) ⊢ρ =
    ⊢-⇒ (ren-pres-ok{ρ = ρ} ⊢A ⊢ρ) (ren-pres-ok{ρ = ρ} ⊢B ⊢ρ) 
ren-pres-ok {Γ} {Γ′} {ρ} {.(∀̇ _)} (⊢-∀ ⊢A) ⊢ρ =
    ⊢-∀ (ren-pres-ok{ρ = extrᵗ ρ} ⊢A (ext-okren{ρ = ρ} ⊢ρ))

wtsub : Subst → TyEnv → TyEnv → Set
wtsub σ Γ Δ = ∀ {B} x → Γ ∋ x ⦂ trm B → Δ ⊢ σ x ⦂ B

sub-pres-type : ∀{Γ}{Δ}{A}{M}{σ}
  → Γ ⊢ M ⦂ A
  → wtsub σ Γ Δ
  → Δ ⊢ ⟪ σ ⟫ M ⦂ A
sub-pres-type {Γ}{Δ}{A}{M}{σ} ⊢M ⊢σ = {!!}


data SubInst : Substᵗ → TyEnv → TyEnv → Set where
  si-base : ∀{Γ}
     → (A : Type)
     → Γ ⊢ A ok
     → SubInst (A •ᵗ idᵗ) (typ ∷ Γ) Γ
  si-trm : ∀{σ}{Γ}{Γ′}{A}
     → SubInst σ Γ Γ′
     → SubInst σ (trm A ∷ Γ) (trm (⟪ σ ⟫ᵗ A) ∷ Γ′)
  si-typ : ∀{σ}{Γ}{Γ′}
     → SubInst σ Γ Γ′
     → SubInst (extᵗ σ) (typ ∷ Γ) (typ ∷ Γ′)
  
data Weaken : TyEnv → TyEnv → Set where
  wtrm : ∀{Γ}{B} → Weaken Γ (trm B ∷ Γ)
  wtyp : ∀{Γ}{Γ′} → Weaken Γ Γ′ → Weaken (typ ∷ Γ) (typ ∷ Γ′)

Weaken-typ : ∀{Γ}{Γ′}{x}
   → Γ ∋ x ⦂ typ
   → Weaken Γ Γ′
   → Γ′ ∋ x ⦂ typ
Weaken-typ {.(typ ∷ _)} {.(trm _ ∷ typ ∷ _)} {.zero} typZ wtrm =
    trmStyp typZ
Weaken-typ {.(typ ∷ _)} {.(trm _ ∷ typ ∷ _)} {.(suc _)} (typStyp ∋x) wtrm =
    trmStyp (typStyp ∋x)
Weaken-typ {.(trm _ ∷ _)} {.(trm _ ∷ trm _ ∷ _)} {x} (trmStyp ∋x) wtrm =
    trmStyp (trmStyp ∋x)
Weaken-typ {.(typ ∷ _)} {.(typ ∷ _)} {.zero} typZ (wtyp wkΓΓ′) =
    typZ
Weaken-typ {.(typ ∷ _)} {.(typ ∷ _)} {.(suc _)} (typStyp ∋x) (wtyp wkΓΓ′) =
    typStyp (Weaken-typ ∋x wkΓΓ′)

data WeakenTyp : TyEnv → TyEnv → ℕ → Set where
  wkty : ∀{Γ} → WeakenTyp Γ (typ ∷ Γ) (suc zero)

Weaken-trm : ∀{Γ}{Γ′}{x}{A}{k}
   → WeakenTyp Γ Γ′ k
   → Γ ∋ x ⦂ trm A
   → Γ′ ∋ x ⦂ trm (⟪ renᵗ (λ x → k + x) ⟫ᵗ A)
Weaken-trm {.(trm A ∷ _)} {.(typ ∷ trm A ∷ _)} {.zero} {A} {.1} wkty trmZ =
    typtrm trmZ
Weaken-trm {.(trm _ ∷ _)} {.(typ ∷ trm _ ∷ _)} {.(suc _)} wkty (trmStrm ∋x) =
    typtrm (trmStrm ∋x)
Weaken-trm {.(typ ∷ _)} {.(typ ∷ typ ∷ _)} {x} {_} {.1} wkty (typtrm ∋x) =
    typtrm (typtrm ∋x)

weaken-trm₂ : ∀{Γ}{x}{A}
   → Γ ∋ x ⦂ trm A
   → (typ ∷ Γ) ∋ x ⦂ trm (⟪ renᵗ suc ⟫ᵗ A)
weaken-trm₂ {Γ}{x}{A} ∋x = Weaken-trm wkty ∋x

weaken-trm : ∀{Γ}{x}{A}{σ}
   → Γ ∋ x ⦂ trm (⟪ σ ⟫ᵗ A)
   → (typ ∷ Γ) ∋ x ⦂ trm (⟪ extᵗ σ ⟫ᵗ (⟪ renᵗ suc ⟫ᵗ A))
weaken-trm {Γ}{x}{A}{σ} ∋x =
   subst (λ X → (typ ∷ Γ) ∋ x ⦂ trm (⟪ X ⟫ᵗ A)) EQ (weaken-trm₂ ∋x)
   where
   EQ : (renᵗ suc ⨟ᵗ extᵗ σ) ≡ (σ ⨟ᵗ renᵗ suc)
   EQ = refl

si-lookup : ∀{σ}{Γ}{Γ′}{A}{x}
   → SubInst σ Γ Γ′
   → Γ ∋ x ⦂ trm A
   → Γ′ ∋ x ⦂ trm (⟪ σ ⟫ᵗ A)
si-lookup {.(A₁ •ᵗ idᵗ)} {.(typ ∷ Γ′)} {Γ′} {_} {_}
    (si-base A₁ x₁) (typtrm ∋x) = ∋x
si-lookup {σ} {.(trm A ∷ _)} {_} {A} {.zero} (si-trm si) trmZ = trmZ
si-lookup {σ} {.(trm _ ∷ _)} {_} {A} {.(suc _)} (si-trm si) (trmStrm ∋x) =
    trmStrm (si-lookup si ∋x)
si-lookup {σ}{typ ∷ Γ}{typ ∷ Γ′}{A} (si-typ{σ′} si) (typtrm{A = A′}{x = x} ∋x)=
   let IH = si-lookup si ∋x in
   weaken-trm{Γ′}{x}{A′}{σ′} IH

weaken-ok : ∀{Γ}{Γ′}{A} → Γ ⊢ A ok → Weaken Γ Γ′ → Γ′ ⊢ A ok
weaken-ok {Γ}{Γ′} {.Nat} ⊢-Nat wkΓΓ′ = ⊢-Nat
weaken-ok {Γ}{Γ′} {^ x} (⊢-Var ∋x) wkΓΓ′ = ⊢-Var (Weaken-typ ∋x wkΓΓ′)
weaken-ok {Γ}{Γ′} {.(_ ⇒ _)} (⊢-⇒ Aok Cok) wkΓΓ′ =
    ⊢-⇒ (weaken-ok Aok wkΓΓ′) (weaken-ok Cok wkΓΓ′)
weaken-ok {Γ}{Γ′} {.(∀̇ _)} (⊢-∀ Aok) wkΓΓ′ = ⊢-∀ (weaken-ok Aok (wtyp wkΓΓ′))

si-apply : ∀{σ}{Γ}{Γ′}{x}
   → SubInst σ Γ Γ′
   → Γ ∋ x ⦂ typ
   → Γ′ ⊢ σ x ok
si-apply (si-base A Aok) typZ = Aok
si-apply (si-base A Aok) (typStyp ∋x) = ⊢-Var ∋x
si-apply {σ} {.(trm _ ∷ _)} {_} {_} (si-trm si) (trmStyp ∋x) =
    weaken-ok (si-apply si ∋x) wtrm
si-apply (si-typ si) typZ = ⊢-Var typZ
si-apply (si-typ{σ}{Γ}{Γ′} si) (typStyp{x = x} ∋x) =
  let IH = si-apply si ∋x in
  let xx = ren-pres-ok{Γ′}{typ ∷ Γ′}{suc} IH λ {y ∋y → typStyp ∋y} in
  subst (λ X → typ ∷ Γ′ ⊢ X ok) (sym EQ) xx
  where
  EQ : extᵗ σ (suc x) ≡ ⟪ renᵗ suc ⟫ᵗ (σ x)
  EQ rewrite seq-defᵗ σ ↑ᵗ x = refl

subᵗ-inst : ∀{σ}{Γ}{Γ′}{A}
   → SubInst σ Γ Γ′
   → Γ ⊢ A ok
   → Γ′ ⊢ ⟪ σ ⟫ᵗ A ok
subᵗ-inst {σ} {Γ} {Γ′} {.Nat} siσ ⊢-Nat = ⊢-Nat
subᵗ-inst {σ} {Γ} {Γ′} {^ x} siσ (⊢-Var ∋x)
    rewrite sub-varᵗ σ x = si-apply siσ ∋x
subᵗ-inst {σ} {Γ} {Γ′} {B ⇒ C} siσ (⊢-⇒ ⊢B ⊢C) =
    ⊢-⇒ (subᵗ-inst siσ ⊢B) (subᵗ-inst siσ ⊢C)
subᵗ-inst {σ} {Γ} {Γ′} {∀̇ B} siσ (⊢-∀ ⊢B) =
    ⊢-∀ (subᵗ-inst {extᵗ σ} (si-typ siσ) ⊢B)

sub-inst : ∀{Γ}{Γ′}{N}{A}
   → (σ : Substᵗ)
   → Γ ⊢ N ⦂ A
   → SubInst σ Γ Γ′
   → Γ′ ⊢ N ⦂ ⟪ σ ⟫ᵗ A
sub-inst {Γ} {Γ′} {.($ n)} {.Nat} σ (⊢-nat n) ⊢σ = ⊢-nat n 
sub-inst {Γ} {Γ′} {` x} {A} σ (⊢-var ∋x) ⊢σ = ⊢-var (si-lookup ⊢σ ∋x)
sub-inst {Γ} {Γ′} {.(ƛ _)} {A ⇒ B} σ (⊢-lam ⊢A ⊢N) ⊢σ =
    let IH = sub-inst{Γ′ = trm (⟪ σ ⟫ᵗ A) ∷ Γ′} σ ⊢N (si-trm ⊢σ) in
    ⊢-lam (subᵗ-inst ⊢σ ⊢A) IH
sub-inst {Γ} {Γ′} {.(_ · _)} {A} σ (⊢-app ⊢L ⊢M) ⊢σ =
    ⊢-app (sub-inst σ ⊢L ⊢σ) (sub-inst σ ⊢M ⊢σ)
sub-inst {Γ} {Γ′} {.(Λ _)} {.(∀̇ _)} σ (⊢-tyabs ⊢N) ⊢σ =
    ⊢-tyabs (sub-inst (extᵗ σ) ⊢N (si-typ ⊢σ))
sub-inst {Γ} {Γ′} {L [·]} σ (⊢-tyapp{A = A} ⊢L ⊢B) ⊢σ =
    let ⊢L⦂∀σA : Γ′ ⊢ L ⦂ ∀̇ (⟪ extᵗ σ ⟫ᵗ A)
        ⊢L⦂∀σA = sub-inst σ ⊢L ⊢σ in
    let ⊢σB = subᵗ-inst ⊢σ ⊢B in
    ⊢-tyapp ⊢L⦂∀σA ⊢σB

inst : ∀{Γ}{N}{A}{B}
   → typ ∷ Γ ⊢ N ⦂ A
   → Γ ⊢ B ok
   → Γ ⊢ N ⦂ (A ⦗ B ⦘)
inst {Γ}{N}{A}{B} ⊢N ⊢B = sub-inst (B •ᵗ idᵗ) ⊢N (si-base B ⊢B)

preservation : ∀{Γ}{M}{N}{A}
  → Γ ⊢ M ⦂ A
  → M —→ N
  → Γ ⊢ N ⦂ A
preservation ⊢M (ξ (□· M) L→L′)
    with ⊢M
... | ⊢-app ⊢L ⊢M = ⊢-app (preservation ⊢L L→L′) ⊢M
preservation ⊢M (ξ (v ·□) M→M′)
    with ⊢M
... | ⊢-app ⊢L ⊢M = ⊢-app ⊢L (preservation ⊢M M→M′)
preservation ⊢M (ξ (□[·]) M→M′) = {!!}
preservation ⊢M (ξ (ƛ□) M→M′) = {!!}
preservation (⊢-app{M = W} (⊢-lam ⊢A ⊢N) ⊢W) β-ƛ =
  sub-pres-type{σ = W • id} ⊢N λ { zero trmZ → ⊢W
                                 ; (suc x) (trmStrm ∋x) → ⊢-var ∋x}
preservation (⊢-tyapp (⊢-tyabs ⊢N) ⊢B) β-Λ = inst ⊢N ⊢B
