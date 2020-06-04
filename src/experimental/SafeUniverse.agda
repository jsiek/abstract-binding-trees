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
open import Function using (_∘_)
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
  var-z : ∀{I : Set}{i : I} → [ (i ∷_) ⊢ Var i ]
  var-s : ∀{I : Set}{i j : I} → [ Var i →̇ (j ∷_) ⊢ Var i ]

injectˡ : ∀ {I : Set}{σ : I} Δ → [ Var σ →̇ (_++ Δ) ⊢ Var σ ]
injectˡ k var-z      = var-z
injectˡ k (var-s v)  = var-s (injectˡ k v)

injectʳ : ∀ {I : Set}{σ : I} Δ → [ Var σ →̇ (Δ ++_) ⊢ Var σ ]
injectʳ []        v = v
injectʳ (y ∷ ys)  v = var-s (injectʳ ys v)

{-

 Environments are functions from variables to values,
 represented as functions.

 They are wrapped in a record just to help Agda inference.

-}

record _-Env {I : Set} (Γ : List I) (𝒱 : I -Scoped) (Δ : List I) : Set where
  constructor mkren
  field lookup : ∀{i} → Var i Γ → 𝒱 i Δ

ε : ∀{I : Set}{𝒱 : I -Scoped}{Δ : List I} → ([] -Env) 𝒱 Δ
ε = mkren (λ { () })

{- Extend an environment, mapping zero to a new value. -}

infixl 10 _∙_
_∙_ : ∀{I Γ Δ 𝒱}{σ : I} → (Γ -Env) 𝒱 Δ → 𝒱 σ Δ → ((σ ∷ Γ) -Env) 𝒱 Δ
_∙_ {I}{Γ}{Δ}{𝒱}{σ} ρ v = mkren G
    where
    G : {i : I} → Var i (σ ∷ Γ) → 𝒱 i Δ
    G {i} var-z = v
    G {i} (var-s x) = _-Env.lookup ρ x

{- Map a function f over all the values in an environment. -}

map-env : ∀{I : Set}{𝒱 𝒲 : I -Scoped}{Γ Δ Θ : List I}
  → (∀ {i : I} → 𝒱 i Δ → 𝒲 i Θ)
  → (Γ -Env) 𝒱 Δ
  → (Γ -Env) 𝒲 Θ
map-env f (mkren lookup) = mkren (λ {i} x → f (lookup x))

{-

  The split function takes a variable that lives in the concatenation
  of two contexts and figures out which to the two it really lives in.
  The result is the variable reinterpreted as a variable of
  one of the two contexts. The result is expressed using the
  Split data type. The last index of Split is the original
  variable, an the left/right inject functions relate the
  result variable back to the original one.

-}

data Split {I : Set} (i : I) Γ Δ : Var i (Γ ++ Δ) → Set where
  inj₁ : (k : Var i Γ) → Split i Γ Δ (injectˡ Δ k)
  inj₂ : (k : Var i Δ) → Split i Γ Δ (injectʳ Γ k)

split : ∀ {I : Set}{i : I}{Δ}
   → (Γ : List I)
   → (k : Var i (Γ ++ Δ))
   → Split i Γ Δ k
split []      k         = inj₂ k
split (σ ∷ Γ) var-z     = inj₁ var-z
split (σ ∷ Γ) (var-s k) with split Γ k
... | inj₁ k₁ = inj₁ (var-s k₁)
... | inj₂ k₂ = inj₂ k₂

{- The operation ρ₁ >> ρ₂ concatenates the two environments. -}

_>>_ : ∀{I : Set}{Γ Δ Θ : List I}{𝒱 : I -Scoped}
   → (Γ -Env) 𝒱 Θ
   → (Δ -Env) 𝒱 Θ
   → ((Γ ++ Δ) -Env) 𝒱 Θ
_>>_ {I}{Γ}{Δ}{Θ}{𝒱} ρ₁ ρ₂ = mkren L
    where
    L : ∀{i} → Var i (Γ ++ Δ) → 𝒱 i Θ
    L {i} x
        with split Γ x
    ... | inj₁ x₁ = _-Env.lookup ρ₁ x₁
    ... | inj₂ x₂ = _-Env.lookup ρ₂ x₂

{- A thinning renames variables from context Γ to Δ. -}

Thinning : ∀{I} → List I → List I → Set
Thinning {I} Γ Δ = (Γ -Env) Var Δ

{- The following is named 'extend' in the paper. -}
th-extend : ∀{I}{Γ : List I}{σ : I} → Thinning Γ (σ ∷ Γ)
th-extend {I}{Γ}{σ} = mkren L
    where L : {i : I} → Var i Γ → Var i (σ ∷ Γ)
          L {i} x = var-s x
    

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

th^Var : {I : Set}{τ : I} → Thinnable (Var τ)
th^Var {I}{τ} x r = _-Env.lookup r x

th^Env : ∀{I : Set}{𝒱}{Γ : List I}
   → (∀ {i : I} → Thinnable (𝒱 i))
   → Thinnable ((Γ -Env) 𝒱)
th^Env {I}{𝒱}{Γ} thVi {Δ} ρ {θ} r = mkren L
    where L : {i : I} → Var i Γ → 𝒱 i θ
          L {i} x = thVi (_-Env.lookup ρ x) r

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
    field th^𝒱 : ∀{τ} → Thinnable (𝒱 τ)
          return : ∀{τ : Type} → [ 𝒱 τ  →̇  𝒞 τ ]
          _•_ : ∀{σ τ : Type} → [ 𝒞 (σ ⇒ τ)  →̇  𝒞 σ →̇ 𝒞 τ ]
          Λ : ∀{τ : Type} → (σ : Type) → [ □ (𝒱 σ →̇ 𝒞 τ)  →̇  𝒞 (σ ⇒ τ) ]
    
    extend : ∀{Γ Δ Θ : List Type}{σ : Type}
       → Thinning Δ Θ
       → (Γ -Env) 𝒱 Δ
       → 𝒱 σ Θ
       → ((σ ∷ Γ) -Env) 𝒱 Θ
    extend {Γ}{Δ}{Θ}{σ} r ρ v = (map-env (λ w → th^𝒱 w r) ρ) ∙ v
    
    sem : ∀{Γ Δ : List Type}{τ : Type}
        → (Γ -Env) 𝒱 Δ
        → (Term τ Γ → 𝒞 τ Δ)
    sem ρ (` x) = return (_-Env.lookup ρ x)
    sem ρ (L · M) = sem ρ L • sem ρ M
    sem ρ (ƛ N) = Λ _ λ {Σ} r v → sem (extend r ρ v) N

  Renaming : Sem Var Term
  Renaming = record { th^𝒱 = th^Var ; return = `_ ; _•_ = _·_ ;
                      Λ = λ σ b → ƛ (b (mkren var-s) var-z) }
  ren = Sem.sem Renaming

  Subst : Sem Term Term
  Subst = record { th^𝒱 = λ M r → ren r M ; return = λ M → M ; _•_ = _·_ ;
                   Λ = λ σ b → ƛ (b (mkren var-s) (` var-z)) }

  
{-
   Universe of Data Types a la Chapman, Dagand, McBride, and Morris.
-}

module CDMM where

  data CDMM-Desc (I J : Set) : Set₁ where
    tag/st : (A : Set) → (A → CDMM-Desc I J) → CDMM-Desc I J
    child : J → CDMM-Desc I J → CDMM-Desc I J
    done : I → CDMM-Desc I J

  ⟦_⟧ : ∀{I J : Set } → CDMM-Desc I J → (J → Set) → (I → Set)
  ⟦ tag/st A d ⟧ X i = Σ[ a ∈ A ] (⟦ d a ⟧ X i)
  ⟦ child j d ⟧ X i = X j × ⟦ d ⟧ X i
  ⟦ done i' ⟧ X i = i ≡ i'

  data ListTags : Set where
    t-nil t-cons : ListTags

  listD : Set → CDMM-Desc ⊤ ⊤ 
  listD A = tag/st ListTags G
    where
    G : ListTags → CDMM-Desc ⊤ ⊤
    G t-nil = done tt
    G t-cons = tag/st A λ _ → child tt (done tt)

  fmap : ∀{I J : Set}{X Y : J → Set}
     → (d : CDMM-Desc I J)
     → [ X →̇ Y ]
     → [ (⟦ d ⟧ X) →̇ (⟦ d ⟧ Y) ]
  fmap (tag/st A d) f ⟨ a , rst ⟩ = ⟨ a , fmap (d a) f rst ⟩
  fmap (child j d) f ⟨ ch , rst ⟩ = ⟨ (f ch) , (fmap d f rst) ⟩
  fmap (done i) f refl = refl

  data μ {I : Set} (d : CDMM-Desc I I) : Size → I → Set where
    rec : ∀{i : I}{s'} → ⟦ d ⟧ (μ d s') i → μ d (↑ s') i

  fold : ∀{I : Set}{X}{s'}
     → (d : CDMM-Desc I I)
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


{-
  The Generic Universe
 -}

data Desc (I : Set) : Set₁ where
  tag/st : (A : Set) → (A → Desc I) → Desc I
  child : List I → I → Desc I       → Desc I
  ⦂_ : I                          → Desc I

{-
 Interpret a description into an Agda type that
 consists of products and dependents sums.
 * X interprets the children.
 * i is the 'type'.
 * Γ is the current context.
 -}
⟦_⟧ : ∀{I : Set} → Desc I → (List I → I -Scoped) → (I -Scoped)
⟦ tag/st A d ⟧ X i Γ = Σ[ a ∈ A ] (⟦ d a ⟧ X i Γ)
⟦ child Δ j d ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
   {- Δ specifies the newly bound variables,
      j is the 'type' of the child -}
⟦ ⦂ i' ⟧ X i Γ = i ≡ i'

{-
 Map the function f over all the children of the node.
 -}
fmap : ∀{I : Set}{X Y}{Γ Δ : List I}{i : I}
   → (d : Desc I)
   → (∀ Θ i → X Θ i Γ → Y Θ i Δ)
   → ⟦ d ⟧ X i Γ
   → ⟦ d ⟧ Y i Δ
fmap (tag/st A d) f ⟨ a , rst ⟩ = ⟨ a , fmap (d a) f rst ⟩
fmap (child Δ j d) f ⟨ ch , rst ⟩ = ⟨ (f Δ j ch) , (fmap d f rst) ⟩
fmap (⦂ i') f refl = refl

Scope : ∀{I : Set} → I -Scoped → List I → I -Scoped
Scope P Δ i = (Δ ++_) ⊢ P i

{-

 A term is either 
 * a variable, or
 * a node described by description d, where the children are also
   terms.

 -}
data Term {I : Set} (d : Desc I) : Size → I -Scoped where
  var : ∀{i : I}{s} → [ Var i →̇ Term d (↑ s) i ]
  node : ∀{i : I}{s} → [ ⟦ d ⟧ (Scope (Term d s)) i →̇ Term d (↑ s) i ]

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
  pattern _·_ L M = node ⟨ t-app _ _ , ⟨ L , ⟨ M , refl ⟩ ⟩ ⟩
  pattern ƛ_ N = node ⟨ t-lam _ _ , ⟨ N , refl ⟩ ⟩ 

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

{-
  A batch of values coming into scope are represented by an
  environment, i.e., (Γ -Env) 𝒱.
-}

Kripke : ∀{I : Set} (𝒱 𝒞 : I -Scoped) → List I → I -Scoped
{-
Kripke 𝒱 𝒞 [] i = 𝒞 i
-}
Kripke 𝒱 𝒞 Γ i = □ ((Γ -Env) 𝒱 →̇ 𝒞 i)

{- Fold over a term. -}

record Sem {I : Set} (d : Desc I) (𝒱 𝒞 : I -Scoped) : Set where
  field th^𝒱 :     ∀{i} → Thinnable (𝒱 i)
        return :  ∀{i} → [ 𝒱 i  →̇  𝒞 i ]
        algebra : ∀{i} → [ ⟦ d ⟧ (Kripke{I} 𝒱 𝒞) i  →̇  𝒞 i ] 

  _-Comp : List I → I -Scoped → List I → Set
  (_-Comp) Γ 𝒞 Δ = ∀{s : Size}{i : I} → Term d s i Γ → 𝒞 i Δ 

  {- 
    sem interprets a term in environment ρ, producing a result in 𝒞 i Δ.
   -}
  sem : ∀{Γ Δ}
      → (Γ -Env) 𝒱 Δ
      → (Γ -Comp) 𝒞 Δ

  {-
    body is used to interpret each child of a node.
   -}
  body : ∀{Γ Δ}{s : Size}
      → (Γ -Env) 𝒱 Δ
      → ∀ Θ i 
      → Scope (Term d s) Θ i Γ
      → Kripke 𝒱 𝒞 Θ i Δ

  sem ρ (var x) = return (_-Env.lookup ρ x)
  sem ρ (node {j}{s} t) = algebra (fmap d (body {s = s} ρ) t)
  
{-
  body ρ [] i t = sem ρ t
-}
  body ρ Θ i t r vs = sem (vs >> (th^Env th^𝒱 ρ r)) t

{- Helpers for folds that produce terms, such as substitution. -}

record VarLike {I : Set} (𝒱 : I -Scoped) : Set where
  field th^𝒱 : ∀{i : I} → Thinnable (𝒱 i)
        new : ∀{i} → [ (i ∷_) ⊢ 𝒱 i ]

  base : ∀{Γ} → (Γ -Env) 𝒱 Γ
  base {Γ = []}    = ε
  base {Γ = σ ∷ Γ} = (th^Env th^𝒱 base th-extend) ∙ new

  freshʳ : ∀{Γ} → (Δ : List I) → (Γ -Env) 𝒱 (Δ ++ Γ)
  freshʳ Δ = th^Env th^𝒱 base (mkren (injectʳ Δ))

  freshˡ : ∀{Γ} → (Δ : List I) → (Γ -Env) 𝒱 (Γ ++ Δ)
  freshˡ k = th^Env th^𝒱 base (mkren (injectˡ _))

open VarLike

vl^Var : ∀{I} → VarLike {I} Var
vl^Var {I} = record { th^𝒱 = th^Var ; new = var-z }

reify : ∀{I : Set}{𝒱 𝒞 : I -Scoped}{Γ}
   → VarLike 𝒱
   → ∀ Δ i → Kripke 𝒱 𝒞 Δ i Γ → Scope 𝒞 Δ i Γ
{-
reify vl^𝒱 []         i b = b
reify vl^𝒱 Δ@(_ ∷ _)  i b = b (freshʳ vl^Var Δ) (freshˡ vl^𝒱 _)
-}
reify vl^𝒱 Δ i b = b (freshʳ vl^Var Δ) (freshˡ vl^𝒱 _)

module Rename {I : Set} (d : Desc I) where

  Renaming : Sem d Var (Term d ∞)
  Renaming = record { th^𝒱 = λ x r → _-Env.lookup r x
                    ; return = var
                    ; algebra = node ∘ fmap d (reify vl^Var) }
  open Sem Renaming renaming (sem to sem-ren)

  ren : ∀{Γ Δ : List I}{i : I}
     → (Γ -Env) Var Δ
     → Term d ∞ i Γ
     → Term d ∞ i Δ
  ren ρ t = sem-ren ρ t

module Subst {I : Set} (d : Desc I) where
  open Rename d using (ren)

  th^Term : ∀{i : I} → Thinnable (Term d ∞ i)
  th^Term t ρ = ren ρ t

  vl^Term : VarLike (Term d ∞)
  vl^Term = record { th^𝒱 = th^Term ; new = var var-z }

  Substitution : Sem d (Term d ∞) (Term d ∞)
  Substitution = record { th^𝒱 = λ t r → ren r t
                        ; return = λ x → x
                        ; algebra = node ∘ fmap d (reify vl^Term) }
  open Sem Substitution renaming (sem to sem-subst)

  sub : ∀{Γ Δ : List I}{i : I}
     → (Γ -Env) (Term d ∞) Δ
     → Term d ∞ i Γ
     → Term d ∞ i Δ
  sub σ t = sem-subst σ t

