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
data _⇓_ : Term → Term → ℕ → Set where
  zero⇓ : ∀{M}{N}
       -------------
     → (M ⇓ N) zero
     
  lit⇓ : ∀{c k}
       -------------------
     → ($ c ⇓ $ c) (suc k)
     
  lam⇓ : ∀{N k}
       -------------------
     → (ƛ N ⇓ ƛ N) (suc k)
     
  app⇓ : ∀{L M N W V k}
     → (L ⇓ ƛ N) k
     → (M ⇓ W) k
     → Value W
     → (N [ W ] ⇓ V) k
       -------------------
     → (L · M ⇓ V) (suc k)
     
  app⇓-blame-L : ∀{L M k}
     → (L ⇓ blame) k
       -----------------------
     → (L · M ⇓ blame) (suc k)
     
  app⇓-blame-R : ∀{L M V k}
     → (L ⇓ V) k
     → Value V
     → (M ⇓ blame) k
       -----------------------
     → (L · M ⇓ blame) (suc k)
     
  inj⇓ : ∀{M V G k}
     → (M ⇓ V) k
     → Value V
       -----------------------------
     → (M ⟨ G !⟩ ⇓ V ⟨ G !⟩) (suc k)
     
  inj⇓-blame : ∀{M G k}
     → (M ⇓ blame) k
       --------------------------
     → (M ⟨ G !⟩ ⇓ blame) (suc k)
     
  proj⇓-blame : ∀{M H k}
     → (M ⇓ blame) k
       --------------------------
     → (M ⟨ H ?⟩ ⇓ blame) (suc k)
  
  collapse⇓ : ∀{M V G k}
     → (M ⇓ V ⟨ G !⟩) k
       ----------------------
     → (M ⟨ G ?⟩ ⇓ V) (suc k)
  
  collide⇓ : ∀{M V G H k}
     → (M ⇓ V ⟨ G !⟩) k
     → G ≢ H
       --------------------------
     → (M ⟨ H ?⟩ ⇓ blame) (suc k)
  
  blame⇓ : ∀{k}
       -----------------------
     → (blame ⇓ blame) (suc k)

-- infixr 6 _⇑_
-- data _⇑_ : Term → ℕ → Set where
--   ⇑zero : ∀{M} → M ⇑ zero
--   app⇑ : ∀{L M N W k}
--      → L ⇓ ƛ N
--      → M ⇓ W → Value W
--      → N [ W ] ⇑ k
--      → L · M ⇑ (suc k)
--   app⇑-L : ∀{L M k} → L ⇑ k → L · M ⇑ (suc k)
--   app⇑-R : ∀{L M N k} → L ⇓ ƛ N → M ⇑ k → L · M ⇑ (suc k)
--   inj⇑ : ∀{M G k} → M ⇑ k → M ⟨ G !⟩ ⇑ (suc k)
--   proj⇑ : ∀{M H k} → M ⇑ k → M ⟨ H ?⟩ ⇑ (suc k)

-- _⇑ : Term → Set
-- M ⇑ = ∀ k → M ⇑ k

⇓-value : ∀ V → Value V → ∀{k} → (V ⇓ V) k
⇓-value V v {zero} = zero⇓
⇓-value .(ƛ N) (ƛ̬ N) {suc k} = lam⇓
⇓-value .($ c) ($̬ c) {suc k}= lit⇓
⇓-value (V ⟨ G !⟩) (v 〈 G 〉) {suc k}
    with ⇓-value V v {k}
... | V⇓V = inj⇓ V⇓V v

_⟱_ : Term → Term → Set
M ⟱ V = ∀ k → (M ⇓ V) k

⟱-value : ∀ V → Value V → V ⟱ V
⟱-value V v k = ⇓-value V v

⟱-app : ∀{L M N W V}
   → L ⟱ ƛ N
   → M ⟱ W
   → Value W
   → (N [ W ]) ⟱ V
     --------------
   → (L · M) ⟱ V
⟱-app {L} {M} {N} {W} {V} L↓λN M↓W w NW↓V zero = zero⇓
⟱-app {L} {M} {N} {W} {V} L↓λN M↓W w NW↓V (suc k) =
    app⇓ (L↓λN k) (M↓W k) w (NW↓V k)

-- ⇓-determ : ∀{M}{V}{V′}
--   → M ⇓ V
--   → M ⇓ V′
--     ------
--   → V ≡ V′ 
-- ⇓-determ {$ c} {.($ _)} {.($ _)} lit⇓ lit⇓ = refl
-- ⇓-determ {ƛ N} {.(ƛ _)} {.(ƛ _)} lam⇓ lam⇓ = refl
-- ⇓-determ {(L · M)} {V} {V′} (app⇓ L⇓λN M⇓W w NW⇓V)
--                             (app⇓ L⇓λN′ M⇓W′ w′ NW′⇓V′)
--     with ⇓-determ L⇓λN L⇓λN′ | ⇓-determ M⇓W M⇓W′
-- ... | refl | refl
--     with ⇓-determ NW⇓V NW′⇓V′
-- ... | refl = refl
-- ⇓-determ {.(_ · _)} {V} {.blame} (app⇓ L⇓λN M⇓W w NW⇓V)
--                                  (app⇓-blame-L L⇓blame)
--     with ⇓-determ L⇓λN L⇓blame
-- ... | ()    
-- ⇓-determ {.(_ · _)} {V} {.blame} (app⇓ L⇓λN M⇓W w NW⇓V)
--                                  (app⇓-blame-R L⇓V v M⇓blame)
--     with ⇓-determ M⇓W M⇓blame | w
-- ... | refl | ()
-- ⇓-determ {.(_ · _)} {.blame} {V′} (app⇓-blame-L L⇓blame)
--                                   (app⇓ L⇓λN M⇓V′₁ x M⇓V′₂)
--     with ⇓-determ L⇓λN L⇓blame
-- ... | ()
-- ⇓-determ {.(_ · _)} {.blame} {.blame} (app⇓-blame-L M⇓V)
--                                       (app⇓-blame-L M⇓V′) = refl
-- ⇓-determ {.(_ · _)} {.blame} {.blame} (app⇓-blame-L L⇓V)
--                                       (app⇓-blame-R L⇓blame v M⇓V′₁)  = refl
-- ⇓-determ {.(_ · _)} {.blame} {V′} (app⇓-blame-R M⇓V v M⇓blame)
--                                   (app⇓ M⇓V′ M⇓W w M⇓V′₂)
--     with ⇓-determ M⇓W M⇓blame | w
-- ... | refl | ()
-- ⇓-determ {.(_ · _)} {.blame} {.blame} (app⇓-blame-R L⇓λN v M⇓V₁)
--                                       (app⇓-blame-L L⇓blame) = refl
-- ⇓-determ {.(_ · _)} {.blame} {.blame} (app⇓-blame-R M⇓V v M⇓V₁)
--                                        (app⇓-blame-R M⇓V′ v′ M⇓V′₁) = refl
-- ⇓-determ {.(_ ⟨ _ !⟩)} {.(_ ⟨ _ !⟩)} {.(_ ⟨ _ !⟩)} (inj⇓ M⇓V x)
--                          (inj⇓ M⇓V′ x₁)
--     with ⇓-determ M⇓V M⇓V′
-- ... | refl = refl
-- ⇓-determ {.(_ ⟨ _ !⟩)} {.(_ ⟨ _ !⟩)} {.blame} (inj⇓ M⇓V v)
--                                           (inj⇓-blame M⇓blame)
--     with ⇓-determ M⇓V M⇓blame | v
-- ... | refl | ()
-- ⇓-determ {.(_ ⟨ _ !⟩)} {.blame} {.(_ ⟨ _ !⟩)} (inj⇓-blame M⇓blame)
--                (inj⇓ M⇓V v) 
--     with ⇓-determ M⇓V M⇓blame | v
-- ... | refl | ()
-- ⇓-determ {.(_ ⟨ _ !⟩)} {.blame} {.blame} (inj⇓-blame M⇓blame)
--                     (inj⇓-blame M⇓V′) = refl
-- ⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {.blame} (proj⇓-blame M⇓V) (proj⇓-blame M⇓V′) = refl
-- ⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {V′} (proj⇓-blame M⇓V) (collapse⇓ M⇓V′)
--     with ⇓-determ M⇓V M⇓V′
-- ... | ()
-- ⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {.blame} (proj⇓-blame M⇓V) (collide⇓ M⇓V′ x) =
--     refl
-- ⇓-determ {.(_ ⟨ _ ?⟩)} {V} {.blame} (collapse⇓ M⇓V) (proj⇓-blame M⇓V′)
--     with ⇓-determ M⇓V M⇓V′
-- ... | ()
-- ⇓-determ {.(_ ⟨ _ ?⟩)} {V} {V′} (collapse⇓ M⇓V) (collapse⇓ M⇓V′)
--     with ⇓-determ M⇓V M⇓V′
-- ... | refl = refl
-- ⇓-determ {.(_ ⟨ _ ?⟩)} {V} {.blame} (collapse⇓ M⇓V) (collide⇓ M⇓V′ x)
--     with ⇓-determ M⇓V M⇓V′
-- ... | refl = ⊥-elim (x refl)
-- ⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {.blame} (collide⇓ M⇓V x) (proj⇓-blame M⇓V′) =
--     refl
-- ⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {V′} (collide⇓ M⇓V x) (collapse⇓ M⇓V′)
--     with ⇓-determ M⇓V M⇓V′
-- ... | refl = ⊥-elim (x refl)
-- ⇓-determ {.(_ ⟨ _ ?⟩)} {.blame} {.blame} (collide⇓ M⇓V x) (collide⇓ M⇓V′ x₁) =
--     refl
-- ⇓-determ {.blame} {.blame} {.blame} blame⇓ blame⇓ = refl

-- ⇓-value-eq : ∀{V W} → Value V → V ⇓ W → W ≡ V
-- ⇓-value-eq {V}{W} v V⇓W = ⇓-determ V⇓W (⇓-value V v)

-- inj⇑-inv : ∀{M G} → M ⟨ G !⟩ ⇑ → M ⇑
-- inj⇑-inv {M}{G} MG⇑ k
--     with MG⇑ (suc k)
-- ... | inj⇑ M⇑k = M⇑k

-- values-dont-diverge : ∀{V} → Value V → V ⇑ → ⊥
-- values-dont-diverge {V} v V⇑
--     with V⇑ (suc zero) | v
-- ... | inj⇑{M = V′} V′⇑0 | v′ 〈 _ 〉 = values-dont-diverge v′ (inj⇑-inv V⇑)

-- --blame-eval-not-value : ∀{V} → blame ⇓ V → ⊥
-- --blame-eval-not-value {V} 
-- --blame-eval-not-value {V} 

-- blame-doesnt-diverge : blame ⇑ → ⊥
-- blame-doesnt-diverge b⇑
--     with b⇑ 1
-- ... | ()


