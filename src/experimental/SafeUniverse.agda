{-

This file contains Jeremy's notes while reading the paper

A Type and Scope Safe Universe of Syntaxes with Binding:
Their Semantics and Proofs

by Allais, Atken, Chapman, McBride, and McKinna.

-}

open import Data.List using (List; _∷_; map)
open import Data.Product using (_×_)

module experimental.SafeUniverse where

{-
  Things that have property I in context List I, like variables.
-}
_-Scoped : Set → Set₁
I -Scoped = I → List I → Set

{-
 Combinators for threading a context
 through some logical formulas.
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

_<$>_ : ∀{I : Set}{𝒱 𝒲 : I -Scoped}{Γ Δ Θ : List I}
  → (∀ {i : I} → 𝒱 i Δ → 𝒲 i Θ)
  → (Γ -Env) 𝒱 Δ
  → (Γ -Env) 𝒲 Θ
f <$> mkren lookup = mkren (λ {i} x → f (lookup x))

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

{-
extend : ∀{σ : I} → Thinning Γ (σ ∷ Γ)
extend = mkren (λ x → s x)
-}

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

module Lambda where

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
          return : ∀{τ : Type} → [ 𝒱 τ →̇ 𝒞 τ ]
          _•_ : ∀{σ τ : Type} → [ 𝒞 (σ ⇒ τ) →̇ 𝒞 σ →̇ 𝒞 τ ]
          Λ : ∀{τ : Type} → (σ : Type) → [ □ (𝒱 σ →̇ 𝒞 τ) →̇ 𝒞 (σ ⇒ τ) ]
    
    extend : ∀{Γ Δ Θ : List Type}{σ : Type}
       → Thinning Δ Θ
       → (Γ -Env) 𝒱 Δ
       → 𝒱 σ Θ
       → ((σ ∷ Γ) -Env) 𝒱 Θ
    extend {Γ}{Δ}{Θ}{σ} r ρ v = ((λ w → th𝒱 w r) <$> ρ) ∙ v
    
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

  
