open import Data.List using (List; _∷_)
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

private
  variable
    I J : Set
    i : I
    j : J

data Var : I -Scoped where
  z : [ (i ∷_) ⊢ Var i ]
  s : [ Var i →̇ (j ∷_) ⊢ Var i ]


module Lambda where

  infixr 3 _⇒_

  data Type : Set where
    α     : Type
    _⇒_  : Type → Type → Type

  private
    variable
      σ τ : Type
      Γ Δ : List Type

  data Lam : Type -Scoped where
    V  : [ Var σ →̇ Lam σ ]
    A  : [ Lam (σ ⇒ τ) →̇ Lam σ →̇ Lam τ ]
    L  : [ (σ ∷_) ⊢ Lam τ →̇ Lam (σ ⇒ τ) ]

{-

 Environments are functions from variables to values,
 represented as functions.

 They are wrapped in a record just to help Agda inference.

-}

record _-Env (Γ : List I) (𝒱 : I -Scoped) (Δ : List I) : Set where
  constructor pack
  field lookup : ∀{i} → Var i Γ → 𝒱 i Δ

{- Rename variables from context Γ to Δ -}
Thinning : List I → List I → Set
Thinning Γ Δ = (Γ -Env) Var Δ

{- P is true after any renaming from Γ -}
□ : (List I → Set) → (List I → Set)
(□ P) Γ = [ Thinning Γ →̇ P ]          {- ∀{Δ} → Thinning Γ Δ → P Δ -}

{- A property P is Thinabble if it is preserved under renamings. -}
Thinnable : (List I → Set) → Set
Thinnable P = [ P →̇ □ P ]

private
  variable
    P Q : List I → Set
  variable
    Γ Δ : List I
    
id : Thinning Γ Γ
id = pack (λ x → x)

extract : [ □ P →̇ P ]
extract = λ □PΓ → □PΓ id
