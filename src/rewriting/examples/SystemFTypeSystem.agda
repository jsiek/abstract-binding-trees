{-# OPTIONS --rewriting #-}
{-
  UNDER CONSTRUCTION
-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; map; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤?_)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Function using (_∘_)
open import Sig

module rewriting.examples.SystemFTypeSystem where

{-------------      Type System    -------------}

open import Var

TyVarEnv : Set
TyVarEnv = List ⊤

TyEnv : Set
TyEnv = List Type

{- Well-formed Types -}

infix 1 _⊢_ok
data _⊢_ok : TyVarEnv → Type → Set where

  ⊢-Nat : ∀{Σ}
       ----------
     → Σ ⊢ Nat ok
     
  ⊢-Var : ∀{Σ}{x}
     → Σ ∋ x ⦂ tt
       -----------
     → Σ ⊢ ^ x ok

  ⊢-⇒ : ∀{Σ}{A}{B}
     → Σ ⊢ A ok
     → Σ ⊢ B ok
       ------------
     → Σ ⊢ A ⇒ B ok

  ⊢-∀ :  ∀{Σ}{A}
     → tt ∷ Σ ⊢ A ok
       --------------
     → Σ ⊢ ∀̇ A ok

{- Well-typed Terms -}

infix 1 _∣_⊢_⦂_
data _∣_⊢_⦂_ : TyVarEnv → TyEnv → Term → Type → Set where

  ⊢-nat : ∀{Σ}{Γ} → ∀ n
        -----------------
      → Σ ∣ Γ ⊢ $ n ⦂ Nat

  ⊢-var : ∀{Σ}{Γ}{x}{A}
      → Γ ∋ x ⦂ A
        ---------------
      → Σ ∣ Γ ⊢ ` x ⦂ A

  ⊢-lam : ∀{Σ}{Γ}{N}{A}{B}
     → Σ ⊢ A ok
     → Σ ∣ A ∷ Γ ⊢ N ⦂ B
       -------------------
     → Σ ∣ Γ ⊢ ƛ N ⦂ A ⇒ B
     
  ⊢-app : ∀{Σ}{Γ}{L}{M}{A}{B}
     → Σ ∣ Γ ⊢ L ⦂ A ⇒ B
     → Σ ∣ Γ ⊢ M ⦂ A
       -----------------
     → Σ ∣ Γ ⊢ L · M ⦂ B

  ⊢-tyabs : ∀{Σ}{Γ}{N}{A}
     → tt ∷ Σ ∣ map ⟪ renᵗ suc ⟫ᵗ Γ ⊢ N ⦂ A
       ------------------------------------
     → Σ ∣ Γ ⊢ Λ N ⦂ ∀̇ A

  ⊢-tyapp : ∀{Σ}{Γ}{L}{A}{B}
     → Σ ∣ Γ ⊢ L ⦂ ∀̇ A
     → Σ ⊢ B ok
       -----------------------
     → Σ ∣ Γ ⊢ L [·] ⦂ A ⦗ B ⦘

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M


nat-not-fun : ∀{Σ Γ n A B} → Σ ∣ Γ ⊢ $ n ⦂ A ⇒ B → ⊥
nat-not-fun ()

Λ-not-fun : ∀{Σ Γ N A B} → Σ ∣ Γ ⊢ Λ N ⦂ A ⇒ B → ⊥
Λ-not-fun ()

ƛ-not-all : ∀{Σ Γ N A} → Σ ∣ Γ ⊢ ƛ N ⦂ ∀̇ A → ⊥
ƛ-not-all ()

nat-not-all : ∀{Σ Γ n A} → Σ ∣ Γ ⊢ $ n ⦂ ∀̇ A → ⊥
nat-not-all ()

progress : ∀ {Σ M A}
  → Σ ∣ [] ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢-var ())
progress (⊢-nat n)                  = done V-nat
progress (⊢-lam ⊢A ⊢N)              =  done V-ƛ
progress (⊢-app ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                    =  step (ξ (□· _) L—→L′)
... | done V-ƛ                      =  step β-ƛ
... | done V-nat                    = ⊥-elim (nat-not-fun ⊢L)
... | done V-Λ                      = ⊥-elim (Λ-not-fun ⊢L)
progress (⊢-tyabs ⊢N)               =  done V-Λ
progress (⊢-tyapp ⊢L B)
    with progress ⊢L
... | step L—→L′                    = step (ξ □[·] L—→L′)
... | done V-ƛ                      = ⊥-elim (ƛ-not-all ⊢L)
... | done V-nat                    = ⊥-elim (nat-not-all ⊢L)
... | done V-Λ                      = step β-Λ

{- renaming preserves well-formedness -}

wtrenᵗ : Renameᵗ → TyVarEnv → TyVarEnv → Set
wtrenᵗ ρ Σ Σ′ = ∀ x → Σ ∋ x ⦂ tt → Σ′ ∋ ρ x ⦂ tt

ext-renᵗ : ∀{Σ}{Σ′}{ρ}{B}
  → wtrenᵗ ρ Σ Σ′
  → wtrenᵗ (extrᵗ ρ) (B ∷ Σ) (B ∷ Σ′)
ext-renᵗ {Σ} {Σ′} {ρ} {B} ⊢ρ zero ∋x = ∋x
ext-renᵗ {Σ} {Σ′} {ρ} {B} ⊢ρ (suc x) ∋x = ⊢ρ x ∋x

ren-pres-wf : ∀{Σ}{Σ′}{A}{ρ}
  → Σ ⊢ A ok
  → wtrenᵗ ρ Σ Σ′
  → Σ′ ⊢ ⟪ renᵗ ρ ⟫ᵗ A ok
ren-pres-wf {Σ} {Σ′} {.Nat} {ρ} ⊢-Nat ⊢ρ = ⊢-Nat
ren-pres-wf {Σ} {Σ′} {^ x} {ρ} (⊢-Var ∋x) ⊢ρ
    rewrite sub-varᵗ (renᵗ ρ) x | ren-defᵗ ρ x = ⊢-Var (⊢ρ x ∋x)
ren-pres-wf {Σ} {Σ′} {A ⇒ B} {ρ} (⊢-⇒ ⊢A ⊢B) ⊢ρ =
    ⊢-⇒ (ren-pres-wf ⊢A ⊢ρ) (ren-pres-wf ⊢B ⊢ρ)
ren-pres-wf {Σ} {Σ′} {∀̇ A} {ρ} (⊢-∀ ⊢A) ⊢ρ =
    ⊢-∀ (ren-pres-wf{ρ = extrᵗ ρ} ⊢A (ext-renᵗ{Σ′ = Σ′}{ρ} ⊢ρ))

{- substitution preserves well-formedness -}

wtsubᵗ : Substᵗ → TyVarEnv → TyVarEnv → Set
wtsubᵗ σ Σ Σ′ = ∀ x → Σ ∋ x ⦂ tt → Σ′ ⊢ σ x ok

ext-subᵗ : ∀{Σ}{Σ′}{σ}{B}
  → wtsubᵗ σ Σ Σ′
  → wtsubᵗ (extᵗ σ) (B ∷ Σ) (B ∷ Σ′)
ext-subᵗ {Σ} {Σ′} {σ} {B} ⊢σ zero refl = ⊢-Var refl
ext-subᵗ {Σ} {Σ′} {σ} {B} ⊢σ (suc x) ∋x rewrite seq-defᵗ σ ↑ᵗ x =
  ren-pres-wf{ρ = suc} (⊢σ x ∋x) λ x₁ x₂ → x₂

sub-pres-wf : ∀{Σ}{Σ′}{A}{σ}
  → Σ ⊢ A ok
  → wtsubᵗ σ Σ Σ′
  → Σ′ ⊢ ⟪ σ ⟫ᵗ A ok
sub-pres-wf {Σ} {Σ′} {.Nat} {σ} ⊢-Nat ⊢σ = ⊢-Nat
sub-pres-wf {Σ} {Σ′} {^ x} {σ} (⊢-Var ∋x) ⊢σ
    rewrite sub-varᵗ σ x = ⊢σ x ∋x
sub-pres-wf {Σ} {Σ′} {.(_ ⇒ _)} {σ} (⊢-⇒ ⊢A ⊢B) ⊢σ =
    ⊢-⇒ (sub-pres-wf ⊢A ⊢σ) (sub-pres-wf ⊢B ⊢σ)
sub-pres-wf {Σ} {Σ′} {.(∀̇ _)} {σ} (⊢-∀ ⊢A) ⊢σ =
   ⊢-∀ (sub-pres-wf{σ = extᵗ σ} ⊢A (ext-subᵗ ⊢σ))

{- weaken Σ -}

map-∋ : ∀{Γ}{x}{A}{σ}
  → Γ ∋ x ⦂ A
  → map ⟪ σ ⟫ᵗ Γ ∋ x ⦂ ⟪ σ ⟫ᵗ A
map-∋ {B ∷ Γ} {zero} {A} refl = refl
map-∋ {B ∷ Γ} {suc x} {A}{σ} ∋x = map-∋{Γ}{x}{A}{σ} ∋x

wt-suc : ∀ Σ → wtrenᵗ suc Σ (tt ∷ Σ)
wt-suc (x ∷ Σ) zero refl = refl
wt-suc (x₁ ∷ Σ) (suc x) ∋x = ∋x

map-fusion : ∀ {A B C : Set} (ls : List A) (f : A → B) (g : B → C)
   → map g (map f ls) ≡ map (g ∘ f) ls
map-fusion [] f g = refl
map-fusion (a ∷ ls) f g = cong₂ _∷_ refl (map-fusion ls f g)

map-commute-suc-ext : ∀ Γ σ
  → map ⟪ renᵗ suc ⟫ᵗ (map ⟪ σ ⟫ᵗ Γ)
    ≡ map ⟪ extᵗ σ ⟫ᵗ (map ⟪ renᵗ suc ⟫ᵗ Γ)
map-commute-suc-ext Γ σ =
  let xx : map ⟪ renᵗ suc ⟫ᵗ (map ⟪ σ ⟫ᵗ Γ)
           ≡ map (⟪ renᵗ suc ⟫ᵗ ∘ ⟪ σ ⟫ᵗ) Γ 
      xx = map-fusion Γ ⟪ σ ⟫ᵗ  ⟪ renᵗ suc ⟫ᵗ in
  let yy : (⟪ renᵗ suc ⟫ᵗ ∘ ⟪ σ ⟫ᵗ) ≡ (⟪ extᵗ σ ⟫ᵗ ∘ ⟪ renᵗ suc ⟫ᵗ)
      yy = refl in
  let zz = sym (map-fusion Γ ⟪ renᵗ suc ⟫ᵗ ⟪ extᵗ σ ⟫ᵗ) in
  trans xx (trans (cong (λ X → map X Γ) yy) zz)

{-
tysub-reflect-type : ∀{Σ}{Σ′}{Γ}{M}{A}{σ : Substᵗ}
   → Σ′ ∣ map ⟪ σ ⟫ᵗ Γ ⊢ M ⦂ ⟪ σ ⟫ᵗ A
   → wtsubᵗ σ Σ Σ′
   → Σ ∣ Γ ⊢ M ⦂ A
tysub-reflect-type {Σ}{Σ′}{Γ}{M}{A}{σ} ⊢M ⊢σ = {!!}
-}

tysub-pres-type : ∀{Σ}{Σ′}{Γ}{M}{A}{σ : Substᵗ}
   → Σ ∣ Γ ⊢ M ⦂ A
   → wtsubᵗ σ Σ Σ′
   → Σ′ ∣ map ⟪ σ ⟫ᵗ Γ ⊢ M ⦂ ⟪ σ ⟫ᵗ A
tysub-pres-type {Σ}{Σ′} {Γ} {.($ n)} {.Nat} (⊢-nat n) ⊢σ = ⊢-nat n
tysub-pres-type {Σ}{Σ′} {Γ} {` x} {A}{σ} (⊢-var ∋x) ⊢σ =
    ⊢-var (map-∋{Γ}{x}{A}{σ} ∋x)
tysub-pres-type {Σ}{Σ′} {Γ} {.(ƛ _)} {.(_ ⇒ _)} (⊢-lam ⊢A ⊢M) ⊢σ =
    ⊢-lam (sub-pres-wf ⊢A ⊢σ) (tysub-pres-type ⊢M ⊢σ)
tysub-pres-type {Σ}{Σ′} {Γ} {.(_ · _)} {A} (⊢-app ⊢L ⊢M) ⊢σ =
   ⊢-app (tysub-pres-type ⊢L ⊢σ) (tysub-pres-type ⊢M ⊢σ)
tysub-pres-type {Σ}{Σ′} {Γ} {Λ N} {∀̇ A}{σ} (⊢-tyabs ⊢N) ⊢σ =
   let N⦂₁ : tt ∷ Σ′ ∣ map ⟪ extᵗ σ ⟫ᵗ (map ⟪ renᵗ suc ⟫ᵗ Γ)
             ⊢ N ⦂ ⟪ extᵗ σ ⟫ᵗ A
       N⦂₁ = tysub-pres-type{tt ∷ Σ}{tt ∷ Σ′}{map ⟪ renᵗ suc ⟫ᵗ Γ}{N}{A}
                     {extᵗ σ} ⊢N (ext-subᵗ ⊢σ) in
   let N⦂ : tt ∷ Σ′ ∣ map ⟪ renᵗ suc ⟫ᵗ (map ⟪ σ ⟫ᵗ Γ) ⊢ N ⦂ ⟪ extᵗ σ ⟫ᵗ A
       N⦂ = subst (λ X → tt ∷ Σ′ ∣ X ⊢ N ⦂ ⟪ extᵗ σ ⟫ᵗ A)
                  (sym (map-commute-suc-ext Γ σ)) N⦂₁ in
   ⊢-tyabs N⦂
tysub-pres-type {Σ}{Σ′} {Γ} {L [·]} {_} (⊢-tyapp{A = A}{B} ⊢L ⊢B) ⊢σ =
    ⊢-tyapp (tysub-pres-type ⊢L ⊢σ) (sub-pres-wf ⊢B ⊢σ)

{- renaming preserves types -}

wtren : Rename → TyEnv → TyEnv → Set
wtren ρ Γ Δ = ∀ {B} x → Γ ∋ x ⦂ B → Δ ∋ ρ x ⦂ B

ext-ren : ∀{Γ}{Δ}{ρ}{B}
  → wtren ρ Γ Δ
  → wtren (extr ρ) (B ∷ Γ) (B ∷ Δ)
ext-ren {Γ} {Δ} {ρ} {B} ⊢ρ zero ∋x = ∋x
ext-ren {Γ} {Δ} {ρ} {B} ⊢ρ (suc x) ∋x = ⊢ρ x ∋x

map-∋-inv : ∀{Γ}{f : Type → Type}{x}{B}
   → map f Γ ∋ x ⦂ B
   → ∃[ A ] Γ ∋ x ⦂ A × f A ≡ B
map-∋-inv {C ∷ Γ} {f} {zero} refl = ⟨ C , ⟨ refl , refl ⟩ ⟩
map-∋-inv {C ∷ Γ} {f} {suc x} map∋x = map-∋-inv{Γ}{f}{x} map∋x

wtren-map : ∀ ρ Γ Δ {σ}
   → wtren ρ Γ Δ
   → wtren ρ (map ⟪ σ ⟫ᵗ Γ) (map ⟪ σ ⟫ᵗ Δ)
wtren-map ρ Γ Δ {σ} ⊢ρ {B} x ∋x
    with map-∋-inv {Γ}{⟪ σ ⟫ᵗ}{x}{B} ∋x
... | ⟨ A , ⟨ Γ∋x , refl ⟩ ⟩ =
  let Δ∋ρx⦂A = ⊢ρ x Γ∋x in
  map-∋{Δ}{ρ x}{A}{σ} Δ∋ρx⦂A

ren-pres-type : ∀{Σ}{Γ}{Δ}{A}{M}{ρ}
  → Σ ∣ Γ ⊢ M ⦂ A
  → wtren ρ Γ Δ
  → Σ ∣ Δ ⊢ ⟪ ren ρ ⟫ M ⦂ A
ren-pres-type {Σ}{Γ}{Δ} {A} {.(` _)}{ρ} (⊢-var{x = x} ∋x) ⊢ρ 
  rewrite sub-var (ren ρ) x | ren-def ρ x = ⊢-var (⊢ρ x ∋x)
ren-pres-type {Σ}{Γ}{Δ} {_} {.($ c)} (⊢-nat c) ⊢ρ = ⊢-nat c
ren-pres-type {Σ}{Γ}{Δ} {A} {.(_ · _)} (⊢-app ⊢L ⊢M) ⊢ρ =
  ⊢-app (ren-pres-type ⊢L ⊢ρ) (ren-pres-type ⊢M ⊢ρ)
ren-pres-type {Σ}{Γ}{Δ} {.(_ ⇒ _)} {.(ƛ _)}{ρ = ρ} (⊢-lam ⊢A ⊢M) ⊢ρ =
  ⊢-lam ⊢A (ren-pres-type{ρ = extr ρ} ⊢M (ext-ren{Δ = Δ}{ρ} ⊢ρ))
ren-pres-type {Σ}{Γ}{Δ} {A} {(Λ N)}{ρ} (⊢-tyabs ⊢N) ⊢ρ =
  let ⊢ρmap = wtren-map ρ Γ Δ {renᵗ suc} ⊢ρ in
  let IH = ren-pres-type{ρ = ρ} ⊢N ⊢ρmap in
  ⊢-tyabs IH
ren-pres-type {Σ}{Γ}{Δ} {A} {L [·]}{ρ} (⊢-tyapp ⊢L B) ⊢ρ =
  ⊢-tyapp (ren-pres-type ⊢L ⊢ρ) B

{- substitution preserves types -}

wtsub : Subst → TyVarEnv → TyEnv → TyEnv → Set
wtsub σ Σ Γ Δ = ∀ {B} x → Γ ∋ x ⦂ B → Σ ∣ Δ ⊢ σ x ⦂ B

ext-sub : ∀{Σ}{Γ}{Δ}{σ}{B}
  → wtsub σ Σ Γ Δ
  → wtsub (ext σ) Σ (B ∷ Γ) (B ∷ Δ)
ext-sub {Σ}{Γ} {Δ} {σ} {B} ⊢σ zero refl = ⊢-var refl
ext-sub {Σ}{Γ} {Δ} {σ} {B} ⊢σ {A} (suc x) ∋x rewrite seq-def σ ↑ x =
  ren-pres-type{ρ = suc} (⊢σ x ∋x) λ x₁ x₂ → x₂

{-
extᵗ-sub : ∀{Σ}{Γ}{Δ}{σ}
  → wtsub σ Σ Γ Δ
  → wtsub σ (tt ∷ Σ) Γ Δ
extᵗ-sub {Σ} {A ∷ Γ} {Δ} {σ} ⊢σ zero refl =
  let xx = ⊢σ zero refl in
  {!!}
extᵗ-sub {Σ} {Γ} {Δ} {σ} ⊢σ (suc x) ∋x = {!!}
-}

wtsub-map : ∀ (σ : Subst) Σ Σ′ Γ Δ {ρ}
   → wtrenᵗ ρ Σ Σ′
   → wtsub σ Σ Γ Δ
   → wtsub σ Σ′ (map ⟪ renᵗ ρ ⟫ᵗ Γ) (map ⟪ renᵗ ρ ⟫ᵗ Δ)
wtsub-map σ Σ Σ′ Γ Δ {ρ} ⊢ρ ⊢σ {B} x ∋x
    with map-∋-inv {Γ}{⟪ renᵗ ρ ⟫ᵗ}{x}{B} ∋x
... | ⟨ A , ⟨ Γ∋x , refl ⟩ ⟩ =
  let ΣΔ⊢σx⦂A = ⊢σ x Γ∋x in
  tysub-pres-type{σ = renᵗ ρ} ΣΔ⊢σx⦂A λ y Σ∋y → 
    subst (λ X → Σ′ ⊢ X ok) (sym (ren-defᵗ ρ y)) (⊢-Var (⊢ρ y Σ∋y))

sub-pres-type : ∀{Σ}{Γ}{Δ}{A}{M}{σ}
  → Σ ∣ Γ ⊢ M ⦂ A
  → wtsub σ Σ Γ Δ
  → Σ ∣ Δ ⊢ ⟪ σ ⟫ M ⦂ A
sub-pres-type {Σ}{Γ} {Δ} {A} {_} {σ} (⊢-var{x = x} ∋x) ⊢σ
  rewrite sub-var σ x = ⊢σ x ∋x
sub-pres-type {Σ}{Γ} {Δ} {_} {.($ c)} {σ} (⊢-nat c) ⊢σ = ⊢-nat c
sub-pres-type {Σ}{Γ} {Δ} {A} {.(_ · _)} {σ} (⊢-app ⊢L ⊢M) ⊢σ =
  ⊢-app (sub-pres-type ⊢L ⊢σ) (sub-pres-type ⊢M ⊢σ)
sub-pres-type {Σ}{Γ} {Δ} {.(_ ⇒ _)} {.(ƛ _)} {σ} (⊢-lam ⊢A ⊢M) ⊢σ =
  ⊢-lam ⊢A (sub-pres-type{σ = ext σ} ⊢M (ext-sub ⊢σ))
sub-pres-type {Σ}{Γ}{Δ} {A} {(Λ N)}{σ} (⊢-tyabs ⊢N) ⊢σ =
  let ⊢σ′ = wtsub-map σ Σ (tt ∷ Σ) Γ Δ {suc} (wt-suc Σ) ⊢σ in
  ⊢-tyabs (sub-pres-type{σ = σ} ⊢N ⊢σ′)
sub-pres-type {Σ}{Γ}{Δ} {A} {L [·]}{σ} (⊢-tyapp ⊢L B) ⊢σ =
  ⊢-tyapp (sub-pres-type ⊢L ⊢σ) B

{- Type Substitution -}

--wtsubᵗ : Subst → TyEnv → TyEnv → Set
--wtsubᵗ σ Γ Δ = ∀ x → Γ ∋ x ⦂ typ


inst : ∀{Σ}{Σ′}{Γ}{N}{A}{σ}
   → Σ ++ Σ′ ∣ map ⟪ renᵗ (λ x → length Σ + x) ⟫ᵗ Γ ⊢ N ⦂ A
   → wtsubᵗ σ (Σ ++ Σ′) Σ′
   → (∀ x → length Σ ≤ x → σ x ≡ ^ (x ∸ length Σ))
   → Σ′ ∣ Γ ⊢ N ⦂ ⟪ σ ⟫ᵗ A
inst {Σ} {Σ′} {Γ} {.($ n)} {.Nat} {σ} (⊢-nat n) ⊢σ σid = {!!}
inst {Σ} {Σ′} {Γ} {` x} {A} {σ} (⊢-var ∋x) ⊢σ σid =

    ⊢-var {!!}
    {-
    with map-∋-inv{Γ}{⟪ renᵗ (_+_ (length Σ)) ⟫ᵗ}{x}{A} ∋x
... | ⟨ B , ⟨ Γ∋x , eq ⟩ ⟩ =    
    let xx = ⊢σ x {!!} in
    
    Goal: Γ ∋ x ⦂ ⟪ σ ⟫ᵗ A

    Γ∋x : Γ ∋ x ⦂ B
    eq  : ⟪ renᵗ (_+_ (length Σ)) ⟫ᵗ B ≡ A

    -}
inst {Σ} {Σ′} {Γ} {.(ƛ _)} {.(_ ⇒ _)} {σ} (⊢-lam x ⊢N) ⊢σ σid  = {!!}
inst {Σ} {Σ′} {Γ} {.(_ · _)} {A} {σ} (⊢-app ⊢L ⊢M) ⊢σ σid = {!!}
inst {Σ} {Σ′} {Γ} {.(Λ _)} {.(∀̇ _)} {σ} (⊢-tyabs ⊢L) ⊢σ σid = {!!}
inst {Σ} {Σ′} {Γ} {.(_ [·])} {.(_ ⦗ _ ⦘)} {σ} (⊢-tyapp ⊢M ⊢B) ⊢σ σid = {!!}

type-subst : ∀{Σ}{Γ}{N}{A}{B}
   → tt ∷ Σ ∣ map ⟪ renᵗ suc ⟫ᵗ Γ ⊢ N ⦂ A
   → Σ ⊢ B ok
   → Σ ∣ Γ ⊢ N ⦂ ⟪ B •ᵗ idᵗ ⟫ᵗ A -- A ⦗ B ⦘ 
type-subst {Σ}{Γ}{N}{A}{B} ⊢N ⊢B =
    let G : tt ∷ Σ ∣ map ⟪ renᵗ suc ⟫ᵗ Γ ⊢ N ⦂ ⟪ renᵗ suc ⟫ᵗ (⟪ B •ᵗ idᵗ ⟫ᵗ A)
        G = subst (λ X → tt ∷ Σ ∣ map ⟪ renᵗ suc ⟫ᵗ Γ ⊢ N ⦂ X) {!!} ⊢N in
    {!!}        
{-
let xx = tysub-reflect-type{Σ}{tt ∷ Σ}{σ = renᵗ suc} G {!!} in
    xx
-}


{-------------      Proof of Preservation    -------------}

preservation : ∀{Σ}{Γ}{M}{N}{A}
  → Σ ∣ Γ ⊢ M ⦂ A
  → M —→ N
  → Σ ∣ Γ ⊢ N ⦂ A
preservation ⊢M (ξ (□· M) L→L′)
    with ⊢M
... | ⊢-app ⊢L ⊢M = ⊢-app (preservation ⊢L L→L′) ⊢M
preservation ⊢M (ξ (v ·□) M→M′)
    with ⊢M
... | ⊢-app ⊢L ⊢M = ⊢-app ⊢L (preservation ⊢M M→M′)
preservation ⊢M (ξ (□[·]) M→M′) = {!!}

preservation ⊢M (ξ (ƛ□) M→M′) = {!!}

preservation (⊢-app{M = W} (⊢-lam ⊢A ⊢N) ⊢W) β-ƛ =
  sub-pres-type{σ = W • id} ⊢N λ { zero refl → ⊢W ; (suc x) ∋x → ⊢-var ∋x}
preservation (⊢-tyapp (⊢-tyabs ⊢N) ⊢B) β-Λ = type-subst ⊢N ⊢B



{-

data 𝑃 : (op : Op) → Vec Cat (length (sig op)) → BTypes Cat (sig op) → Cat → Set where
  𝑃-nat : ∀{n} → 𝑃 (op-nat n) []̌ tt (trm Nat)
{-
   Γ, trm A ⊢ N : trm B
   ---------------------
   Γ ⊢ ƛ N ⦂ trm (A ⇒ B)
-}
  𝑃-lam : ∀{A B} → 𝑃 op-lam (trm B ∷̌ []̌) ⟨ ⟨ trm A , tt ⟩ , tt ⟩ (trm (A ⇒ B))
{-
   Γ ⊢ L : trm (A → B)
   Γ ⊢ M : trm A
   -----------------
   Γ ⊢ L · M ⦂ trm B
-}
  𝑃-app : ∀{A B} → 𝑃 op-app (trm (A ⇒ B) ∷̌ trm A ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ (trm B)
{-
   Γ, typ ⊢ N : trm A
   ----------------
   Γ ⊢ Λ N ⦂ trm (Π A)
-}
  𝑃-tyabs : ∀{A B} → 𝑃 op-tyabs (trm A ∷̌ []̌) ⟨ ⟨ typ B , tt ⟩ , tt ⟩ (trm (Π A))
{-
   Γ ⊢ L : trm (Π A)
   Γ ⊢ B : typ B
   -----------------
   Γ ⊢ L ․ B ⦂ trm A [ B ]
-}
  𝑃-tyapp : ∀{A B}
     → 𝑃 op-tyapp (trm (Π A) ∷̌ typ B ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ (trm (A [ B ]))
{-
   Γ , typ ⊢ N : trm A
   Γ ⊢ B : typ B
   -----------------
   Γ ⊢ nu B N ⦂ trm A [ B ]
-}
  𝑃-nu : ∀{A B}
     → 𝑃 op-nu (trm (Π A) ∷̌ typ B ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ (trm (A [ B ]))
{-
  Γ ⊢ A ⦂ typ A
  Γ ⊢ B ⦂ typ B
  -----------------------
  Γ ⊢ A ⇒ B ⦂ typ (A ⇒ B)
-}
  𝑃-fun : ∀{A B} → 𝑃 op-fun  (typ A ∷̌ typ B ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ (typ (A ⇒ B))
{-
  Γ, typ B ⊢ A ⦂ typ A
  ---------------------
  Γ ⊢ Π A ⦂ typ (Π A)
-}
  𝑃-all : ∀{A B} → 𝑃 op-all (typ A ∷̌ []̌) ⟨ ⟨ typ B , tt ⟩ , tt ⟩ (typ (Π A))
{-
  -----------------
  Γ ⊢ Nat ⦂ typ Nat
-}
  𝑃-nat-ty : 𝑃 op-nat-ty []̌ tt (typ Nat)

open import rewriting.ABTPredicate Op sig 𝑃

{-------------      Type System Rules    -------------}

pattern ⊢` ∋x = var-p ∋x
pattern ⊢$ n = op-p {op = op-nat n} nil-p 𝑃-nat
pattern ⊢ƛ ⊢N = op-p {op = op-lam} (cons-p (bind-p (ast-p ⊢N)) nil-p)  𝑃-lam
pattern ⊢· ⊢L ⊢M = op-p {op = op-app}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) 𝑃-app
pattern ⊢Λ ⊢N = op-p {op = op-tyabs} (cons-p (bind-p (ast-p ⊢N)) nil-p) 𝑃-tyabs
pattern ⊢․ ⊢L ⊢A = op-p {op = op-tyapp}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢A) nil-p)) 𝑃-tyapp
pattern ⊢ℕ = op-p {op = op-nat-ty} nil-p 𝑃-nat-ty
pattern ⊢⇒ ⊢A ⊢B = op-p {op = op-fun}
                           (cons-p (ast-p ⊢A) (cons-p (ast-p ⊢B) nil-p)) 𝑃-fun
pattern ⊢Π ⊢A = op-p {op = op-all} (cons-p (bind-p (ast-p ⊢A)) nil-p) 𝑃-all

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


nat-not-fun : ∀{Γ n A B} → Γ ⊢ $ n ⦂ trm (A ⇒ B) → ⊥
nat-not-fun (op-p _ ())

Λ-not-fun : ∀{Γ N A B} → Γ ⊢ Λ N ⦂ trm (A ⇒ B) → ⊥
Λ-not-fun (op-p _ ())

ƛ-not-all : ∀{Γ N A} → Γ ⊢ ƛ N ⦂ trm (Π A) → ⊥
ƛ-not-all (op-p _ ())

nat-not-all : ∀{Γ n A} → Γ ⊢ $ n ⦂ trm (Π A) → ⊥
nat-not-all (op-p _ ())

progress : ∀ {M A}
  → [] ⊢ M ⦂ trm A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢$ n)                      = done V-nat
progress (⊢ƛ ⊢N)                     =  done V-ƛ
progress (⊢· ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                    =  step (ξ-·₁ L—→L′)
... | done V-ƛ                      =  step β-ƛ
... | done V-nat                    = ⊥-elim (nat-not-fun ⊢L)
... | done V-Λ                      = ⊥-elim (Λ-not-fun ⊢L)
progress (⊢Λ ⊢N)                    =  done V-Λ
progress (⊢․ ⊢L ⊢A)
    with progress ⊢L
... | step L—→L′                    = step (ξ-․ L—→L′)
... | done V-ƛ                      = ⊥-elim (ƛ-not-all ⊢L)
... | done V-nat                    = ⊥-elim (nat-not-all ⊢L)
... | done V-Λ                      = step β-Λ

{-------------      Proof of Preservation    -------------}

preserve : ∀ {Γ M N A}
  → Γ ⊢ M ⦂ A
  → M —→ N
    ----------
  → Γ ⊢ N ⦂ A
preserve (⊢· ⊢L ⊢M) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M
preserve (⊢· ⊢L ⊢M) (ξ-·₂ x M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) 
preserve (⊢ƛ ⊢M) (ξ-ƛ M—→N) = ⊢ƛ (preserve ⊢M M—→N)
preserve (⊢· (⊢ƛ ⊢N) ⊢M) β-ƛ = preserve-substitution _ _ ⊢N ⊢M
preserve (⊢․ ⊢L ⊢A) (ξ-․ L—→L′) = ⊢․ (preserve ⊢L L—→L′) ⊢A
preserve (⊢․ (⊢Λ ⊢N) ⊢A) β-Λ = {!!}
  
{-
preserve (⊢· ⊢L ⊢M) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M 
preserve (⊢· ⊢L ⊢M) (ξ-·₂ vL M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) 
preserve (⊢ƛ ⊢M) (ξ-ƛ M—→N) = ⊢ƛ (preserve ⊢M M—→N) 
preserve {Γ}{(ƛ N) · M}{_}{B} ⊢λN·M β-ƛ = {!!}
preserve-substitution N M ⊢N ⊢M
-}
-}
