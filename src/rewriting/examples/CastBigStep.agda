{-# OPTIONS --rewriting #-}
module rewriting.examples.CastBigStep where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Maybe
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import rewriting.examples.Cast

infixr 6 _⇓_
data _⇓_ : Term → Term → Set where
  lit⇓ : ∀{c} → $ c ⇓ $ c
  lam⇓ : ∀{N} → ƛ N ⇓ ƛ N
  app⇓ : ∀{L M N W V} → L ⇓ ƛ N → M ⇓ W → Value W → N [ W ] ⇓ V → L · M ⇓ V
  app⇓-blame-L : ∀{L M} → L ⇓ blame → L · M ⇓ blame
  app⇓-blame-R : ∀{L M N} → L ⇓ ƛ N → M ⇓ blame → L · M ⇓ blame
  inj⇓ : ∀{M V G} → M ⇓ V → Value V → M ⟨ G !⟩ ⇓ V ⟨ G !⟩
  inj⇓-blame : ∀{M G} → M ⇓ blame → M ⟨ G !⟩ ⇓ blame
  proj⇓-blame : ∀{M H} → M ⇓ blame → M ⟨ H ?⟩ ⇓ blame
  collapse⇓ : ∀{M V G} → M ⇓ V ⟨ G !⟩ → M ⟨ G ?⟩ ⇓ V
  collide⇓ : ∀{M V G H} → M ⇓ V ⟨ G !⟩ → G ≢ H → M ⟨ H ?⟩ ⇓ blame
  blame⇓ : blame ⇓ blame

infixr 6 _⇑_
data _⇑_ : Term → ℕ → Set where
  ⇑zero : ∀{M} → M ⇑ zero
  app⇑ : ∀{L M N W k}
     → L ⇓ ƛ N
     → M ⇓ W → Value W
     → N [ W ] ⇑ k
     → L · M ⇑ (suc k)
  app⇑-L : ∀{L M k} → L ⇑ k → L · M ⇑ (suc k)
  app⇑-R : ∀{L M N k} → L ⇓ ƛ N → M ⇑ k → L · M ⇑ (suc k)
  inj⇑ : ∀{M G k} → M ⇑ k → M ⟨ G !⟩ ⇑ (suc k)
  proj⇑ : ∀{M H k} → M ⇑ k → M ⟨ H ?⟩ ⇑ (suc k)

_⇑ : Term → Set
M ⇑ = ∀ k → M ⇑ k

⇓-value : ∀ V → Value V → V ⇓ V
⇓-value .(ƛ N) (ƛ̬ N) = lam⇓
⇓-value .($ c) ($̬ c) = lit⇓
⇓-value (V ⟨ G !⟩) (v 〈 G 〉) = inj⇓ (⇓-value V v) v

⇓-determ : ∀{M}{V}{V′}
  → M ⇓ V
  → M ⇓ V′
    ------
  → V ≡ V′ 
⇓-determ {$ c} {.($ _)} {.($ _)} lit⇓ lit⇓ = refl
⇓-determ {ƛ N} {.(ƛ _)} {.(ƛ _)} lam⇓ lam⇓ = refl
⇓-determ {(L · M)} {V} {V′} (app⇓ L⇓λN M⇓W w NW⇓V)
                            (app⇓ L⇓λN′ M⇓W′ w′ NW′⇓V′)
    with ⇓-determ L⇓λN L⇓λN′ | ⇓-determ M⇓W M⇓W′
... | refl | refl
    with ⇓-determ NW⇓V NW′⇓V′
... | refl = refl
⇓-determ {.(_ · _)} {V} {.blame} (app⇓ L⇓λN M⇓W w NW⇓V)
                                 (app⇓-blame-L L⇓blame)
    with ⇓-determ L⇓λN L⇓blame
... | ()    
⇓-determ {.(_ · _)} {V} {.blame} (app⇓ L⇓λN M⇓W w NW⇓V)
                                 (app⇓-blame-R L⇓λN′ M⇓blame)
    with ⇓-determ M⇓W M⇓blame | w
... | refl | ()
⇓-determ {.(_ · _)} {.blame} {V′} (app⇓-blame-L L⇓blame)
                                  (app⇓ L⇓λN M⇓V′₁ x M⇓V′₂)
    with ⇓-determ L⇓λN L⇓blame
... | ()
⇓-determ {.(_ · _)} {.blame} {.blame} (app⇓-blame-L M⇓V)
                                      (app⇓-blame-L M⇓V′) = refl
⇓-determ {.(_ · _)} {.blame} {.blame} (app⇓-blame-L L⇓λN)
                                      (app⇓-blame-R L⇓blame M⇓V′₁) 
    with ⇓-determ L⇓λN L⇓blame
... | ()
⇓-determ {.(_ · _)} {.blame} {V′} (app⇓-blame-R M⇓V M⇓blame)
                                  (app⇓ M⇓V′ M⇓W w M⇓V′₂)
    with ⇓-determ M⇓W M⇓blame | w
... | refl | ()
⇓-determ {.(_ · _)} {.blame} {.blame} (app⇓-blame-R L⇓λN M⇓V₁)
                                      (app⇓-blame-L L⇓blame)
    with ⇓-determ L⇓λN L⇓blame
... | ()
⇓-determ {.(_ · _)} {.blame} {.blame} (app⇓-blame-R M⇓V M⇓V₁)
                                       (app⇓-blame-R M⇓V′ M⇓V′₁) = refl
⇓-determ {.(_ ⟨ _ !⟩)} {.(_ ⟨ _ !⟩)} {.(_ ⟨ _ !⟩)} (inj⇓ M⇓V x)
                         (inj⇓ M⇓V′ x₁)
    with ⇓-determ M⇓V M⇓V′
... | refl = refl
⇓-determ {.(_ ⟨ _ !⟩)} {.(_ ⟨ _ !⟩)} {.blame} (inj⇓ M⇓V v)
                                          (inj⇓-blame M⇓blame)
    with ⇓-determ M⇓V M⇓blame | v
... | refl | ()
⇓-determ {.(_ ⟨ _ !⟩)} {.blame} {.(_ ⟨ _ !⟩)} (inj⇓-blame M⇓blame)
               (inj⇓ M⇓V v) 
    with ⇓-determ M⇓V M⇓blame | v
... | refl | ()
⇓-determ {.(_ ⟨ _ !⟩)} {.blame} {.blame} (inj⇓-blame M⇓blame)
                    (inj⇓-blame M⇓V′) = refl
⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {.blame} (proj⇓-blame M⇓V) (proj⇓-blame M⇓V′) = refl
⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {V′} (proj⇓-blame M⇓V) (collapse⇓ M⇓V′)
    with ⇓-determ M⇓V M⇓V′
... | ()
⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {.blame} (proj⇓-blame M⇓V) (collide⇓ M⇓V′ x) =
    refl
⇓-determ {.(_ ⟨ _ ?⟩)} {V} {.blame} (collapse⇓ M⇓V) (proj⇓-blame M⇓V′)
    with ⇓-determ M⇓V M⇓V′
... | ()
⇓-determ {.(_ ⟨ _ ?⟩)} {V} {V′} (collapse⇓ M⇓V) (collapse⇓ M⇓V′)
    with ⇓-determ M⇓V M⇓V′
... | refl = refl
⇓-determ {.(_ ⟨ _ ?⟩)} {V} {.blame} (collapse⇓ M⇓V) (collide⇓ M⇓V′ x)
    with ⇓-determ M⇓V M⇓V′
... | refl = ⊥-elim (x refl)
⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {.blame} (collide⇓ M⇓V x) (proj⇓-blame M⇓V′) =
    refl
⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {V′} (collide⇓ M⇓V x) (collapse⇓ M⇓V′)
    with ⇓-determ M⇓V M⇓V′
... | refl = ⊥-elim (x refl)
⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {.blame} (collide⇓ M⇓V x) (collide⇓ M⇓V′ x₁) =
    refl
⇓-determ {.blame} {.blame} {.blame} blame⇓ blame⇓ = refl
