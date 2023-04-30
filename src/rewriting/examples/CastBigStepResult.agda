{-# OPTIONS --rewriting #-}
module rewriting.examples.CastBigStepResult where

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

data Result : Set where
  val : Term → Result
  blameR : Result
  timeout : Result

data Halt : Result → Set where
  blameH : Halt blameR
  valueH : ∀{V} → Halt (val V)

data Exception : Result → Set where
  blameX : Exception blameR
  timeoutX : Exception timeout

infixr 6 _⇓ᵏ_
data _⇓ᵏ_ : Term → Result → ℕ → Set where
  ⇓ᵏzero : ∀{M} → (M ⇓ᵏ timeout) zero
  
  lit⇓ᵏ : ∀{c k} → ($ c ⇓ᵏ val ($ c)) (suc k)
  
  lam⇓ᵏ : ∀{N k} → (ƛ N ⇓ᵏ val (ƛ N)) (suc k)
  
  app⇓ᵏ : ∀{L M N W R k}
     → (L ⇓ᵏ val (ƛ N)) k
     → (M ⇓ᵏ val W) k
     → (N [ W ] ⇓ᵏ R) k
       --------------------
     → (L · M ⇓ᵏ R) (suc k)
     
  app⇓ᵏ-raise-L : ∀{L M E k}
     → (L ⇓ᵏ E) k
     → Exception E
       ---------------------
     → (L · M ⇓ᵏ E) (suc k)
     
  app⇓ᵏ-raise-R : ∀{L M N E k}
     → (L ⇓ᵏ val (ƛ N)) k
     → (M ⇓ᵏ E) k
     → Exception E
       --------------------
     → (L · M ⇓ᵏ E) (suc k)
     
  inj⇓ᵏ : ∀{M V G k}
     → (M ⇓ᵏ val V) k
       ------------------------------------
     → (M ⟨ G !⟩ ⇓ᵏ val (V ⟨ G !⟩)) (suc k)
     
  inj⇓ᵏ-raise : ∀{M G E k}
      → (M ⇓ᵏ E) k
      → Exception E
        -----------------------
      → (M ⟨ G !⟩ ⇓ᵏ E) (suc k)
      
  proj⇓ᵏ-raise : ∀{M H E k}
     → (M ⇓ᵏ E) k
     → Exception E
       -----------------------
     → (M ⟨ H ?⟩ ⇓ᵏ E) (suc k)
     
  collapse⇓ᵏ : ∀{M V G k}
     → (M ⇓ᵏ val (V ⟨ G !⟩)) k
       ---------------------------
     → (M ⟨ G ?⟩ ⇓ᵏ val V) (suc k)
     
  collide⇓ᵏ : ∀{M V G H k}
     → (M ⇓ᵏ val (V ⟨ G !⟩)) k
     → G ≢ H
       ----------------------------------
     → (M ⟨ H ?⟩ ⇓ᵏ blameR) (suc k)
     
  blame⇓ᵏ : ∀{k} → (blame ⇓ᵏ blameR) (suc k)

⇓ᵏ-value : ∀ V → Value V → ∃[ k ] (V ⇓ᵏ val V) k
⇓ᵏ-value .(ƛ N) (ƛ̬ N) = 1 , lam⇓ᵏ
⇓ᵏ-value .($ c) ($̬ c) = 1 , lit⇓ᵏ
⇓ᵏ-value (V ⟨ G !⟩) (v 〈 G 〉)
    with ⇓ᵏ-value V v
... | k , V⇓ᵏV = suc k , inj⇓ᵏ V⇓ᵏV 

⇓ᵏ-to-value : ∀ {M}{V}{k} → (M ⇓ᵏ val V) k → Value V
⇓ᵏ-to-value lit⇓ᵏ = $̬ _
⇓ᵏ-to-value lam⇓ᵏ = ƛ̬ _
⇓ᵏ-to-value (app⇓ᵏ L⇓ᵏλN M⇓ᵏW N[W]⇓ᵏV) = ⇓ᵏ-to-value N[W]⇓ᵏV
⇓ᵏ-to-value (inj⇓ᵏ M⇓ᵏV) = (⇓ᵏ-to-value M⇓ᵏV) 〈 _ 〉
⇓ᵏ-to-value (collapse⇓ᵏ M⇓ᵏV)
    with ⇓ᵏ-to-value M⇓ᵏV
... | v 〈 _ 〉 = v

⇓ᵏ-determ : ∀{M}{R}{R′}{k}
  → (M ⇓ᵏ R) k
  → (M ⇓ᵏ R′) k
    ------
  → R ≡ R′ 
⇓ᵏ-determ {M} ⇓ᵏzero ⇓ᵏzero = refl
⇓ᵏ-determ {.($ _)} lit⇓ᵏ lit⇓ᵏ = refl
⇓ᵏ-determ {.(ƛ _)} lam⇓ᵏ lam⇓ᵏ = refl
⇓ᵏ-determ {.(_ · _)} (app⇓ᵏ L⇓ᵏλN M⇓ᵏW NW⇓ᵏR) (app⇓ᵏ L⇓ᵏλN′ M⇓ᵏW′ NW′⇓ᵏR′)
    with ⇓ᵏ-determ L⇓ᵏλN L⇓ᵏλN′ | ⇓ᵏ-determ M⇓ᵏW M⇓ᵏW′
... | refl | refl = ⇓ᵏ-determ NW⇓ᵏR NW′⇓ᵏR′
⇓ᵏ-determ {.(_ · _)} (app⇓ᵏ L⇓ᵏλN M⇓ᵏW NW⇓ᵏR) (app⇓ᵏ-raise-L L⇓ᵏE ex)
    with ⇓ᵏ-determ L⇓ᵏλN L⇓ᵏE | ex
... | refl | ()
⇓ᵏ-determ {.(_ · _)} (app⇓ᵏ L⇓ᵏλN M⇓ᵏW NW⇓ᵏR) (app⇓ᵏ-raise-R L⇓ᵏλN′ M⇓ᵏE ex)
    with ⇓ᵏ-determ M⇓ᵏW M⇓ᵏE | ex
... | refl | ()
⇓ᵏ-determ {.(_ · _)} (app⇓ᵏ-raise-L L⇓ᵏE ex) (app⇓ᵏ L⇓ᵏλN′ M⇓ᵏW NW′⇓ᵏE′)
    with ⇓ᵏ-determ L⇓ᵏE L⇓ᵏλN′ | ex
... | refl | ()
⇓ᵏ-determ {.(_ · _)} (app⇓ᵏ-raise-L L⇓ᵏE ex) (app⇓ᵏ-raise-L L⇓ᵏE′ ex′) =
    ⇓ᵏ-determ L⇓ᵏE L⇓ᵏE′
⇓ᵏ-determ {.(_ · _)} (app⇓ᵏ-raise-L L⇓ᵏE ex) (app⇓ᵏ-raise-R L⇓ᵏλN′ M⇓ᵏE′ ex′)
    with ⇓ᵏ-determ L⇓ᵏE L⇓ᵏλN′ | ex
... | refl | ()
⇓ᵏ-determ {.(_ · _)} (app⇓ᵏ-raise-R L⇓ᵏλN M⇓ᵏE ex) (app⇓ᵏ L⇓ᵏλN′ M⇓ᵏW′ NW′⇓ᵏR′)
    with ⇓ᵏ-determ M⇓ᵏE M⇓ᵏW′ | ex
... | refl | ()
⇓ᵏ-determ {.(_ · _)} (app⇓ᵏ-raise-R L⇓ᵏλN M⇓ᵏE ex) (app⇓ᵏ-raise-L L⇓ᵏE ex′)
    with ⇓ᵏ-determ L⇓ᵏλN L⇓ᵏE | ex′
... | refl | ()
⇓ᵏ-determ {.(_ · _)} (app⇓ᵏ-raise-R L⇓ᵏλN M⇓ᵏE ex) (app⇓ᵏ-raise-R L⇓ᵏλN′ M⇓ᵏE′ ex′) =
    ⇓ᵏ-determ M⇓ᵏE M⇓ᵏE′
⇓ᵏ-determ {.(_ ⟨ _ !⟩)} (inj⇓ᵏ M⇓ᵏV) (inj⇓ᵏ M⇓ᵏV′)
    with ⇓ᵏ-determ M⇓ᵏV M⇓ᵏV′
... | refl = refl
⇓ᵏ-determ {.(_ ⟨ _ !⟩)} (inj⇓ᵏ M⇓ᵏV) (inj⇓ᵏ-raise M⇓ᵏE′ ex′)
    with ⇓ᵏ-determ M⇓ᵏV M⇓ᵏE′ | ex′
... | refl | ()
⇓ᵏ-determ {.(_ ⟨ _ !⟩)} (inj⇓ᵏ-raise M⇓ᵏE ex) (inj⇓ᵏ M⇓ᵏV′)
    with ⇓ᵏ-determ M⇓ᵏE M⇓ᵏV′ | ex
... | refl | ()
⇓ᵏ-determ {.(_ ⟨ _ !⟩)} (inj⇓ᵏ-raise M⇓ᵏE ex) (inj⇓ᵏ-raise M⇓ᵏE′ ex′) =
    ⇓ᵏ-determ M⇓ᵏE M⇓ᵏE′
⇓ᵏ-determ {.(_ ⟨ _ ?⟩)} (proj⇓ᵏ-raise M⇓ᵏE ex) (proj⇓ᵏ-raise M⇓ᵏE′ ex′) =
    ⇓ᵏ-determ M⇓ᵏE M⇓ᵏE′
⇓ᵏ-determ {.(_ ⟨ _ ?⟩)} (proj⇓ᵏ-raise M⇓ᵏE ex) (collapse⇓ᵏ M⇓ᵏV′)
    with ⇓ᵏ-determ M⇓ᵏE M⇓ᵏV′ | ex
... | refl | ()
⇓ᵏ-determ {.(_ ⟨ _ ?⟩)} (proj⇓ᵏ-raise M⇓ᵏE ex) (collide⇓ᵏ M⇓ᵏB′ x)
    with ⇓ᵏ-determ M⇓ᵏE M⇓ᵏB′ | ex
... | refl | ()
⇓ᵏ-determ {.(_ ⟨ _ ?⟩)} (collapse⇓ᵏ M⇓ᵏV) (proj⇓ᵏ-raise M⇓ᵏE′ ex′)
    with ⇓ᵏ-determ M⇓ᵏV M⇓ᵏE′ | ex′
... | refl | ()
⇓ᵏ-determ {.(_ ⟨ _ ?⟩)} (collapse⇓ᵏ M⇓ᵏV) (collapse⇓ᵏ M⇓ᵏV′)
    with ⇓ᵏ-determ M⇓ᵏV M⇓ᵏV′
... | refl = refl
⇓ᵏ-determ {.(_ ⟨ _ ?⟩)} (collapse⇓ᵏ M⇓ᵏV) (collide⇓ᵏ M⇓ᵏB′ neq)
    with ⇓ᵏ-determ M⇓ᵏV M⇓ᵏB′
... | refl = ⊥-elim (neq refl)
⇓ᵏ-determ {.(_ ⟨ _ ?⟩)} (collide⇓ᵏ M⇓ᵏB neq) (proj⇓ᵏ-raise M⇓ᵏR′ ex′)
    with ⇓ᵏ-determ M⇓ᵏB M⇓ᵏR′ | ex′
... | refl | ()
⇓ᵏ-determ {.(_ ⟨ _ ?⟩)} (collide⇓ᵏ M⇓ᵏB neq) (collapse⇓ᵏ M⇓ᵏR′)
    with ⇓ᵏ-determ M⇓ᵏB M⇓ᵏR′
... | refl = ⊥-elim (neq refl)
⇓ᵏ-determ {.(_ ⟨ _ ?⟩)} (collide⇓ᵏ M⇓ᵏB neq) (collide⇓ᵏ M⇓ᵏR′ neq′) = refl
⇓ᵏ-determ {.blame} blame⇓ᵏ blame⇓ᵏ = refl

⇓ᵏval-upClosed : ∀{M}{V}{j}{k}
   → (M ⇓ᵏ val V) j
   → j ≤ k
   → (M ⇓ᵏ val V) k
⇓ᵏval-upClosed {.($ _)} {.($ _)} {.(suc _)} {.(suc _)} lit⇓ᵏ (s≤s j≤k) = lit⇓ᵏ
⇓ᵏval-upClosed {.(ƛ _)} {.(ƛ _)} {.(suc _)} {.(suc _)} lam⇓ᵏ (s≤s j≤k) = lam⇓ᵏ
⇓ᵏval-upClosed {L · M} {V} {suc j} {suc k} (app⇓ᵏ{N = N}{W} L⇓ᵏλNj M⇓ᵏWj NW⇓ᵏV)
   (s≤s j≤k) =
   app⇓ᵏ (⇓ᵏval-upClosed L⇓ᵏλNj j≤k) (⇓ᵏval-upClosed M⇓ᵏWj j≤k)
        (⇓ᵏval-upClosed NW⇓ᵏV j≤k)
⇓ᵏval-upClosed {M ⟨ _ !⟩} {.(_ ⟨ _ !⟩)} {suc j} {suc k} (inj⇓ᵏ M⇓ᵏVj) (s≤s j≤k) =
   inj⇓ᵏ (⇓ᵏval-upClosed M⇓ᵏVj j≤k)
⇓ᵏval-upClosed {.(_ ⟨ _ ?⟩)} {V} {suc j} {suc k} (collapse⇓ᵏ M⇓ᵏVj) (s≤s j≤k) =
   collapse⇓ᵏ (⇓ᵏval-upClosed M⇓ᵏVj j≤k)

⇓ᵏblame-upClosed : ∀{M}{j}{k}
   → (M ⇓ᵏ blameR) j
   → j ≤ k
   → (M ⇓ᵏ blameR) k
⇓ᵏblame-upClosed {.(_ · _)} {suc j} {suc k} (app⇓ᵏ L⇓ᵏλN M⇓ᵏW NW⇓ᵏb) (s≤s j≤k) =
    app⇓ᵏ (⇓ᵏval-upClosed L⇓ᵏλN j≤k) (⇓ᵏval-upClosed M⇓ᵏW j≤k)
         (⇓ᵏblame-upClosed NW⇓ᵏb j≤k)
⇓ᵏblame-upClosed {.(_ · _)} {suc j} {suc k} (app⇓ᵏ-raise-L L⇓ᵏb ex) (s≤s j≤k) =
    app⇓ᵏ-raise-L (⇓ᵏblame-upClosed L⇓ᵏb j≤k) ex
⇓ᵏblame-upClosed {.(_ · _)} {suc j} {suc k} (app⇓ᵏ-raise-R L⇓ᵏλN M⇓ᵏb ex) (s≤s j≤k) =
    app⇓ᵏ-raise-R (⇓ᵏval-upClosed L⇓ᵏλN j≤k) (⇓ᵏblame-upClosed M⇓ᵏb j≤k) ex
⇓ᵏblame-upClosed {.(_ ⟨ _ !⟩)} {suc j} {suc k} (inj⇓ᵏ-raise M⇓ᵏb ex) (s≤s j≤k) =
    inj⇓ᵏ-raise (⇓ᵏblame-upClosed M⇓ᵏb j≤k) ex
⇓ᵏblame-upClosed {.(_ ⟨ _ ?⟩)} {suc j} {suc k} (proj⇓ᵏ-raise M⇓ᵏb ex) (s≤s j≤k) =
    proj⇓ᵏ-raise (⇓ᵏblame-upClosed M⇓ᵏb j≤k) ex
⇓ᵏblame-upClosed {.(_ ⟨ _ ?⟩)} {suc j} {suc k} (collide⇓ᵏ M⇓ᵏV x) (s≤s j≤k) =
    collide⇓ᵏ (⇓ᵏval-upClosed M⇓ᵏV j≤k) x
⇓ᵏblame-upClosed {.blame} {suc j} {suc k} blame⇓ᵏ (s≤s j≤k) =
    blame⇓ᵏ

⇓ᵏhalt-upClosed : ∀{M}{R}{j}{k}
   → (M ⇓ᵏ R) j
   → Halt R
   → j ≤ k
   → (M ⇓ᵏ R) k
⇓ᵏhalt-upClosed {M} {.blameR} {j} {k} M⇓R blameH j≤k = ⇓ᵏblame-upClosed M⇓R j≤k
⇓ᵏhalt-upClosed {M} {.(val _)} {j} {k} M⇓R valueH j≤k = ⇓ᵏval-upClosed M⇓R j≤k

⇓ᵏval-down : ∀{M}{V}{k}{j}
   → (M ⇓ᵏ val V) k
   → j ≤ k
   → (M ⇓ᵏ val V) j  ⊎  (M ⇓ᵏ timeout) j
⇓ᵏval-down {M} {V} {k} {zero} M⇓V j≤k = inj₂ ⇓ᵏzero
⇓ᵏval-down {.($ _)} {.($ _)} {suc k} {suc j} lit⇓ᵏ (s≤s j≤k) = inj₁ lit⇓ᵏ
⇓ᵏval-down {.(ƛ _)} {.(ƛ _)} {suc k} {suc j} lam⇓ᵏ (s≤s j≤k) = inj₁ lam⇓ᵏ
⇓ᵏval-down {.(_ · _)} {V} {suc k} {suc j} (app⇓ᵏ L⇓λN M⇓W NW⇓V) (s≤s j≤k)
    with ⇓ᵏval-down L⇓λN j≤k
... | inj₂ L⇑ = inj₂ (app⇓ᵏ-raise-L L⇑ timeoutX)
... | inj₁ L⇓λNj
    with ⇓ᵏval-down M⇓W j≤k
... | inj₂ M⇑ = inj₂ (app⇓ᵏ-raise-R L⇓λNj M⇑ timeoutX)
... | inj₁ M⇓Wj
    with ⇓ᵏval-down NW⇓V j≤k
... | inj₁ NW⇓Vj = inj₁ (app⇓ᵏ L⇓λNj M⇓Wj NW⇓Vj)
... | inj₂ NW⇑ = inj₂ (app⇓ᵏ L⇓λNj M⇓Wj NW⇑)
⇓ᵏval-down {.(_ ⟨ _ !⟩)} {.(_ ⟨ _ !⟩)} {suc k} {suc j} (inj⇓ᵏ M⇓V) (s≤s j≤k)
    with ⇓ᵏval-down M⇓V j≤k
... | inj₁ M⇓V′ = inj₁ (inj⇓ᵏ M⇓V′)
... | inj₂ M⇑ = inj₂ (inj⇓ᵏ-raise M⇑ timeoutX)
⇓ᵏval-down {.(_ ⟨ _ ?⟩)} {V} {suc k} {suc j} (collapse⇓ᵏ M⇓V) (s≤s j≤k)
    with ⇓ᵏval-down M⇓V j≤k
... | inj₁ M⇓V! = inj₁ (collapse⇓ᵏ M⇓V!)
... | inj₂ M⇑ = inj₂ (proj⇓ᵏ-raise M⇑ timeoutX)

⇓ᵏtimeout-downClosed : ∀{M}{k}{j}
   → (M ⇓ᵏ timeout) k
   → j ≤ k
   → (M ⇓ᵏ timeout) j
⇓ᵏtimeout-downClosed {M} {zero} {.zero} M⇑k z≤n = ⇓ᵏzero
⇓ᵏtimeout-downClosed {M} {suc k} {.zero} M⇑k z≤n = ⇓ᵏzero
⇓ᵏtimeout-downClosed {.(_ · _)} {suc k} {suc j} (app⇓ᵏ L⇓λN M⇓W NW⇑)(s≤s j≤k)
    with ⇓ᵏval-down L⇓λN j≤k
... | inj₂ L⇑ = app⇓ᵏ-raise-L L⇑ timeoutX
... | inj₁ L⇓λNj
    with ⇓ᵏval-down M⇓W j≤k
... | inj₂ M⇑ = app⇓ᵏ-raise-R L⇓λNj M⇑ timeoutX
... | inj₁ M⇓Wj = app⇓ᵏ L⇓λNj M⇓Wj (⇓ᵏtimeout-downClosed NW⇑ j≤k)
⇓ᵏtimeout-downClosed {_} {suc k} {suc j} (app⇓ᵏ-raise-L L⇑ ex) (s≤s j≤k) =
    app⇓ᵏ-raise-L (⇓ᵏtimeout-downClosed L⇑ j≤k) ex
⇓ᵏtimeout-downClosed {_} {suc k} {suc j} (app⇓ᵏ-raise-R L⇓λN M⇑ ex) (s≤s j≤k)
    with ⇓ᵏval-down L⇓λN j≤k
... | inj₂ L⇑ = app⇓ᵏ-raise-L L⇑ timeoutX
... | inj₁ L⇓λNj = app⇓ᵏ-raise-R L⇓λNj (⇓ᵏtimeout-downClosed M⇑ j≤k) ex
⇓ᵏtimeout-downClosed {_} {suc k} {suc j} (inj⇓ᵏ-raise M⇑k ex) (s≤s j≤k) =
    inj⇓ᵏ-raise (⇓ᵏtimeout-downClosed M⇑k j≤k) ex
⇓ᵏtimeout-downClosed {_} {suc k} {suc j} (proj⇓ᵏ-raise M⇑k ex) (s≤s j≤k) =
    proj⇓ᵏ-raise (⇓ᵏtimeout-downClosed M⇑k j≤k) ex


⇓ᵏ-value-eq : ∀{V}{R}{k} → Value V → (V ⇓ᵏ R) k → R ≡ val V
⇓ᵏ-value-eq {V}{R}{k} v V⇓R
    with ⇓ᵏ-value V v
... | j , V⇓Vj
    with j ≤? k
... | yes lt
    with ⇓ᵏ-determ V⇓R (⇓ᵏval-upClosed V⇓Vj lt)
... | refl = refl
⇓ᵏ-value-eq {V}{R}{k} v V⇓R | j , V⇓Vj
    | no nlt
    with R
... | timeout = {!!}
... | blameR
    with ⇓ᵏ-determ V⇓Vj (⇓ᵏblame-upClosed V⇓R (<⇒≤ (≰⇒> nlt)))
... | ()
⇓ᵏ-value-eq {V}{R}{k} v V⇓R | j , V⇓Vj | no nlt
    | val W
    with ⇓ᵏ-determ V⇓Vj (⇓ᵏval-upClosed V⇓R (<⇒≤ (≰⇒> nlt)))
... | refl = refl



-- -- inj⇑-inv : ∀{M G} → M ⟨ G !⟩ ⇑∀ → M ⇑∀
-- -- inj⇑-inv {M}{G} MG⇑ k
-- --     with MG⇑ (suc k)
-- -- ... | inj⇑ M⇑k = M⇑k

-- -- values-dont-diverge : ∀{V} → Value V → V ⇑∀ → ⊥
-- -- values-dont-diverge {V} v V⇑
-- --     with V⇑ (suc zero) | v
-- -- ... | inj⇑{M = V′} V′⇑0 | v′ 〈 _ 〉 = values-dont-diverge v′ (inj⇑-inv V⇑)

-- -- --blame-eval-not-value : ∀{V} → blame ⇓ᵏ V → ⊥
-- -- --blame-eval-not-value {V} 
-- -- --blame-eval-not-value {V} 

-- -- blame-doesnt-diverge : blame ⇑∀ → ⊥
-- -- blame-doesnt-diverge b⇑
-- --     with b⇑ 1
-- -- ... | ()


