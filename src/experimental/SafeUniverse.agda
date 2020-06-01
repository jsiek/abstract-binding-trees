{-

This file contains Jeremy's notes while reading the paper

A Type and Scope Safe Universe of Syntaxes with Binding:
Their Semantics and Proofs

by Allais, Atken, Chapman, McBride, and McKinna.

-}

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; _++_; foldr)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)  
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Size

module experimental.SafeUniverse where

{-
  Things that have property I in context List I.
  For example, variables and terms are Type -Scoped.
-}
_-Scoped : Set → Set₁
I -Scoped = I → List I → Set

{-
  Combinators for threading a context through some logical formulas.
 -}

private
  variable
    E E′ : Set

  {- Implication -}
  infixr 3 _→̇_
  _→̇_ : (P Q : E → Set) → (E → Set)
  (P →̇ Q) Γ = P Γ → Q Γ

  {- Conjunction -}
  _×̇_ : (P Q : E → Set) → (E → Set)
  (P ×̇ Q) Γ = P Γ × Q Γ

  {- The function δ changes the context -}
  _⊢_ : (E → E′) → (E′ → Set) → (E → Set)
  (δ ⊢ Q) Γ = Q (δ Γ)

  {- Ignore the context -}
  κ : Set → (E → Set)
  κ P Γ = P

  {- Quantify over all contexts -}
  [_] : (E → Set) → Set
  [ Q ] = ∀{Γ} → Q Γ

data Var : ∀{I : Set} → I -Scoped where
  z : ∀{I : Set}{i : I} → [ (i ∷_) ⊢ Var i ]
  s : ∀{I : Set}{i j : I} → [ Var i →̇ (j ∷_) ⊢ Var i ]

{-

 Environments are functions from variables to values,
 represented as functions.

 They are wrapped in a record just to help Agda inference.

-}

record _-Env {I : Set} (Γ : List I) (𝒱 : I -Scoped) (Δ : List I) : Set where
  constructor mkren
  field lookup : ∀{i} → Var i Γ → 𝒱 i Δ

{-
   Extend an environment, mapping zero to a new value.
-}
infixl 10 _∙_
_∙_ : ∀{I Γ Δ 𝒱}{σ : I} → (Γ -Env) 𝒱 Δ → 𝒱 σ Δ → ((σ ∷ Γ) -Env) 𝒱 Δ
_∙_ {I}{Γ}{Δ}{𝒱}{σ} ρ v = mkren G
    where
    G : {i : I} → Var i (σ ∷ Γ) → 𝒱 i Δ
    G {i} z = v
    G {i} (s x) = _-Env.lookup ρ x

{-
   Map a function f over all the values in an environment.
-}

map-env : ∀{I : Set}{𝒱 𝒲 : I -Scoped}{Γ Δ Θ : List I}
  → (∀ {i : I} → 𝒱 i Δ → 𝒲 i Θ)
  → (Γ -Env) 𝒱 Δ
  → (Γ -Env) 𝒲 Θ
map-env f (mkren lookup) = mkren (λ {i} x → f (lookup x))

{- A thinning rename variables from context Γ to Δ. -}

Thinning : ∀{I} → List I → List I → Set
Thinning {I} Γ Δ = (Γ -Env) Var Δ

{- P is true after any renaming from Γ. -}

□ : ∀{I} → (List I → Set) → (List I → Set)
(□ P) Γ = [ Thinning Γ →̇ P ]          {- ∀{Δ} → Thinning Γ Δ → P Δ -}

{-
   A property P is Thinabble if it is preserved under renamings.

   If a term has no free variables, then
   renaming the term does not change it.

 -}

Thinnable : ∀{I} → (List I → Set) → Set
Thinnable P = [ P →̇ □ P ]

id : ∀{I : Set}{Γ : List I} → Thinning Γ Γ
id = mkren (λ x → x)

{- □ P is true now because it's true after the identity renaming. -}

extract : ∀{I : Set}{P : List I → Set} → [ □ P →̇ P ]
extract = λ □PΓ → □PΓ id

_⨾_ : ∀{I : Set}{Γ Δ Θ : List I} → Thinning Γ Δ → Thinning Δ Θ → Thinning Γ Θ
ρ₁ ⨾ ρ₂ = mkren (λ x → _-Env.lookup ρ₂ (_-Env.lookup ρ₁ x))

{- □ P implies  □ □ P by composition of renaming -}

duplicate : ∀{I : Set}{P : List I → Set} → [ □ P →̇ □ (□ P) ]
duplicate = λ □PΓ ρ₁ ρ₂ → □PΓ (ρ₁ ⨾ ρ₂)

th□ : ∀{I : Set}{P : List I → Set} → Thinnable (□ P)
th□ = duplicate

module STLC where

  infixr 3 _⇒_
  data Type : Set where
    α     : Type
    _⇒_  : Type → Type → Type

  data Term : Type -Scoped where
    `_  : ∀{σ : Type} → [ Var σ →̇ Term σ ]
    _·_  : ∀{σ τ : Type} → [ Term (σ ⇒ τ) →̇ Term σ →̇ Term τ ]
    ƛ  : ∀{σ τ : Type} → [ (σ ∷_) ⊢ Term τ →̇ Term (σ ⇒ τ) ]

  record Sem (𝒱 𝒞 : Type -Scoped) : Set where
    field th𝒱 : ∀{τ} → Thinnable (𝒱 τ)
          return : ∀{τ : Type} → [ 𝒱 τ  →̇  𝒞 τ ]
          _•_ : ∀{σ τ : Type} → [ 𝒞 (σ ⇒ τ)  →̇  𝒞 σ →̇ 𝒞 τ ]
          Λ : ∀{τ : Type} → (σ : Type) → [ □ (𝒱 σ →̇ 𝒞 τ)  →̇  𝒞 (σ ⇒ τ) ]
    
    extend : ∀{Γ Δ Θ : List Type}{σ : Type}
       → Thinning Δ Θ
       → (Γ -Env) 𝒱 Δ
       → 𝒱 σ Θ
       → ((σ ∷ Γ) -Env) 𝒱 Θ
    extend {Γ}{Δ}{Θ}{σ} r ρ v = (map-env (λ w → th𝒱 w r) ρ) ∙ v
    
    sem : ∀{Γ Δ : List Type}{τ : Type}
        → (Γ -Env) 𝒱 Δ
        → (Term τ Γ → 𝒞 τ Δ)
    sem ρ (` x) = return (_-Env.lookup ρ x)
    sem ρ (L · M) = sem ρ L • sem ρ M
    sem ρ (ƛ N) = Λ _ λ {Σ} r v → sem (extend r ρ v) N

  thVar : {τ : Type} → Thinnable (Var τ)
  thVar {τ} x r = _-Env.lookup r x

  Renaming : Sem Var Term
  Renaming = record { th𝒱 = thVar ; return = `_ ; _•_ = _·_ ;
                      Λ = λ σ b → ƛ (b (mkren s) z) }
  ren = Sem.sem Renaming

  Subst : Sem Term Term
  Subst = record { th𝒱 = λ M r → ren r M ; return = λ M → M ; _•_ = _·_ ;
                   Λ = λ σ b → ƛ (b (mkren s) (` z)) }

  
{-
   Universe of Data Types a la Chapman, Dagand, McBride, and Morris.
-}

module CDMM where

  data Desc (I J : Set) : Set₁ where
    tag/st : (A : Set) → (A → Desc I J) → Desc I J
    child : J → Desc I J → Desc I J
    done : I → Desc I J

  ⟦_⟧ : ∀{I J : Set } → Desc I J → (J → Set) → (I → Set)
  ⟦ tag/st A d ⟧ X i = Σ[ a ∈ A ] (⟦ d a ⟧ X i)
  ⟦ child j d ⟧ X i = X j × ⟦ d ⟧ X i
  ⟦ done i' ⟧ X i = i ≡ i'

  data ListTags : Set where
    t-nil t-cons : ListTags

  listD : Set → Desc ⊤ ⊤ 
  listD A = tag/st ListTags G
    where
    G : ListTags → Desc ⊤ ⊤
    G t-nil = done tt
    G t-cons = tag/st A λ _ → child tt (done tt)

  fmap : ∀{I J : Set}{X Y : J → Set}
     → (d : Desc I J)
     → [ X →̇ Y ]
     → [ (⟦ d ⟧ X) →̇ (⟦ d ⟧ Y) ]
  fmap (tag/st A d) f ⟨ a , rst ⟩ = ⟨ a , fmap (d a) f rst ⟩
  fmap (child j d) f ⟨ ch , rst ⟩ = ⟨ (f ch) , (fmap d f rst) ⟩
  fmap (done i) f refl = refl

  data μ {I : Set} (d : Desc I I) : Size → I → Set where
    rec : ∀{i : I}{s'} → ⟦ d ⟧ (μ d s') i → μ d (↑ s') i

  fold : ∀{I : Set}{X}{s'}
     → (d : Desc I I)
     → [ ⟦ d ⟧ X →̇ X ]
     → [ μ d s' →̇ X ]
  fold d algebra (rec t) = algebra (fmap d (fold d algebra) t)

  Listℕ : Set
  Listℕ = μ (listD ℕ) ∞ tt

  Nat : ⊤ → Set
  Nat tt = ℕ

  length : (xs : Listℕ) → ℕ
  length (rec ⟨ t-nil , refl ⟩) = 0
  length (rec ⟨ t-cons , ⟨ x , ⟨ xs , refl ⟩ ⟩ ⟩) = suc (length xs)

  len-algebra : [ ⟦ listD ℕ ⟧ Nat →̇ Nat ]
  len-algebra ⟨ t-nil , refl ⟩ = 0
  len-algebra ⟨ t-cons , ⟨ x , ⟨ len-xs , refl ⟩ ⟩ ⟩ = suc len-xs

  len : (xs : Listℕ) → ℕ
  len xs = fold (listD ℕ) len-algebra xs

data Desc (I : Set) : Set₁ where
  tag/st : (A : Set) → (A → Desc I) → Desc I
  child : List I → I → Desc I       → Desc I
  ⦂_ : I                          → Desc I

⟦_⟧ : ∀{I : Set} → Desc I → (List I → I -Scoped) → (I -Scoped)
⟦ tag/st A d ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
⟦ child Δ j d ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
⟦ ⦂ i' ⟧ X i Γ = i ≡ i'

Scope : ∀{I : Set} → I -Scoped → List I → I -Scoped
Scope P Δ i = (Δ ++_) ⊢ P i

{- Tm -}
data TermTree {I : Set} (d : Desc I) : Size → I -Scoped where
  var : ∀{i : I}{s} → [ Var i →̇ TermTree d (↑ s) i ]
  con : ∀{i : I}{s} → [ ⟦ d ⟧ (Scope (TermTree d s)) i →̇ TermTree d (↑ s) i ]

module STLC2 where

  open STLC using (Type; α; _⇒_)
    
  data Tag : Set where
    t-app t-lam : Type → Type → Tag

  STLC-D : Desc Type
  STLC-D = tag/st Tag G
    where G : Tag → Desc Type
          G (t-app σ τ) = child [] (σ ⇒ τ) (child [] σ (⦂ τ))
          G (t-lam σ τ) = child (σ ∷ []) τ (⦂ (σ ⇒ τ))

  pattern `_ x = var x
  pattern _·_ L M = con ⟨ t-app _ _ , ⟨ L , ⟨ M , refl ⟩ ⟩ ⟩
  pattern ƛ_ N = con ⟨ t-lam _ _ , ⟨ N , refl ⟩ ⟩ 

{-
   The sum of two descriptions is a description.
-}

_`+_ : ∀{I} → Desc I → Desc I → Desc I
_`+_ {I} d e = tag/st Bool G
  where G : Bool → Desc I
        G false = d
        G true = e

case : ∀{I}{d e : Desc I}{A : Set}{X}{i : I}{Γ}
   → (⟦ d ⟧ X i Γ → A)
   → (⟦ e ⟧ X i Γ → A)
   → (⟦ d `+ e ⟧ X i Γ → A)
case thn els ⟨ false , v ⟩ = thn v
case thn els ⟨ true , v ⟩ = els v 

{-
   Finite product of descriptions
-}

Xs : ∀{I} → List I → Desc I → Desc I
Xs js d = foldr (child []) d js

unXs : ∀{I : Set}{d}{X}{i : I}{Γ}
   → (Δ : List I)
   → ⟦ Xs Δ d ⟧ X i Γ
   → All (λ i → X [] i Γ) Δ × ⟦ d ⟧ X i Γ
unXs {I} {d} {X} {i} {Γ} [] v = ⟨ [] , v ⟩
unXs {I} {d} {X} {i} {Γ} (τ ∷ Δ) ⟨ x , rst ⟩ =
    ⟨ x ∷ proj₁ (unXs Δ rst) , (proj₂ (unXs Δ rst)) ⟩

Kripke : ∀{I : Set} (𝒱 𝒞 : I -Scoped) → List I → I -Scoped
Kripke 𝒱 𝒞 [] i = 𝒞 i
Kripke 𝒱 𝒞 Γ i = □ ((Γ -Env) 𝒱 →̇ 𝒞 i)

{-
  A batch of values coming into scope are represented by an
  environment, i.e., (Γ -Env) 𝒱.
-}

record Sem {I : Set} (d : Desc I) (𝒱 𝒞 : I -Scoped) : Set where
  field th𝒱 :     ∀{i} → Thinnable (𝒱 i)
        return :  ∀{i} → [ 𝒱 i  →̇  𝒞 i ]
        algebra : ∀{i} → [ ⟦ d ⟧ (Kripke 𝒱 𝒞) i  →̇  𝒞 i ] 

_-Comp : ∀{I : Set} → List I → I -Scoped → List I → Set₁
(_-Comp) {I} Γ 𝒞 Δ = ∀ {d : Desc I}{s : Size}{i : I} → TermTree d s i Γ → 𝒞 i Δ 

