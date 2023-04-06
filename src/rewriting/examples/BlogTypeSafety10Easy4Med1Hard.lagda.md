# Type Safety in 10 Easy, 4 Medium, and 1 Hard Lemma using Step-indexed Logical Relations

```
{-# OPTIONS --rewriting #-}
module rewriting.examples.BlogTypeSafety10Easy4Med1Hard where
```

Ok, so the title of this post gives it away that logical relations are
overkill for proving type safety. The proof technique is better suited
to proving more interesting properties such as parametricity, program
equivalence, and the gradual guarantee.  Nevertheless, understanding a
proof of type safety via logical relations is a helpful stepping stone
to understanding these more complex use cases, especial when the
logical relations employ more advanced techniques, such as step
indexing.  In this blog post I prove type safety of a cast calculus,
that is, for an intermediate language of the gradually typed lambda
calculus.  The proof is in Agda and the proof uses step-indexed
logical relations because the presence of the unknown (aka. dynamic)
type prevents the use of regular logical relations. To reduce the
clutter of reasoning about step indexing, we conduct the proof using a
temporal logic, in the spirit of the LSLR logic of Dreyer, Ahmed, and
Birkedal (2011), that we embed in Agda.

## Review of the Cast Calculus

```
open import rewriting.examples.Cast
```

We'll review the syntax and reduction rules of this cast calculus.
Just like the lambda calculus, types include base types (Booleans and
natural numbers), and function types. To support gradual typing, we
include the unknown type ★.

    ι ::= 𝔹 | ℕ
    A,B,C,G,H ::= ι | A ⇒ B | ★

The ground types are 

    g,h ::= ι | ★⇒★

Just like the lambda calculus, there are variables (de Bruijn),
lambdas, and application. We also throw in literals (Booleans and
natural numbers).  To support gradual typing, we include a term `M ⟨ G
, g !⟩` for injecting from a ground type `G` to the unknown type, and
dually, a term `M ⟨ H , h ?⟩` for projecting from the unknown type
back out to a ground type.  Finally, we include the `blame` term to
represent trapped runtime errors.  The syntax is a bit odd to make
Agda happy.

    L,M,N ::= ` x | ƛ N | L · M | $ k | M ⟨ G , g !⟩ | M ⟨ H , h ?⟩ | blame

This cast calculus is somewhat unusual in that it only includes injections
and projections but not the other kinds of casts that one typically
has in a cast calculus, e.g. from `★ ⇒ ℕ` to `ℕ ⇒ ℕ`. That is OK
because those other casts can still be expressed in this cast calculus.

The values include lambdas, literals, and injected values.

    V,W ::= ƛ N | $ c | V ⟨ G , g !⟩

The reduction rules make use of frames, which are defined as follows.

    F ::= □· M | V ·□ | □⟨ G , g !⟩ | □⟨ H , h ?⟩

The operation `F ⟦ M ⟧` plugs a term into a frame.

The reduction rules of the cast calculus are as follows:

    (ξ)        If M —→ N, then F ⟦ M ⟧ —→ F ⟦ N ⟧
    (ξ-blame)  F ⟦ blame ⟧ —→ blame
    (β)        (ƛ N) · W —→ N [ W ]
    (collapse) V ⟨ G , g !⟩ ⟨ G , g ?⟩ —→ V
    (collide)  If G ≢ H, then V ⟨ G , g !⟩ ⟨ H , h ?⟩ —→ blame.


## A First Attempt at a Logical Relation for Type Safety

The following is a first attempt to define a logical relation for type
safety for the cast calculus. The predicate 𝓔 expresses the semantic
notion of a term being well typed at a given type A. Here we say that
a term M is well typed at type A if it satisfies "progress" and
"preservation". The progress part says that M is either (1) a
(semantic) value, (2) reducible, or (3) an error. The preservation part
says that if M reduces to N, then N is also semantically well typed at A.

    ℰ⟦_⟧ : (A : Type) → Term → Set
    ℰ⟦ A ⟧ M = (𝒱 ⟦ A ⟧ M ⊎ reducible M ⊎ Blame M)
                × (∀ N → (M —→ N) → ℰ⟦ A ⟧ N)

The predicate 𝓥 expresses the semantic notion of a value being well
typed a some type A. For a base type `ι` (𝔹 or ℕ), the value must be
the appropriate kind of literal (Boolean or natural number). For a
function type `A ⇒ B`, the value must be a lambda expression `ƛ N`,
and furthermore, substituting any value `W` that is semantically well
typed at `A` into the body `N` produces a term that is semantically
well typed at `B`.

    𝒱⟦_⟧ : (A : Type) → Term → Set
    𝒱⟦ ι ⟧ ($ ι′ c) = ι ≡ ι′
    𝒱⟦ A ⇒ B ⟧ (ƛ N) = ∀ W → 𝒱⟦ A ⟧ W → ℰ⟦ B ⟧ (N [ W ])
    𝒱⟦ ★ ⟧ (V ⟨ G , g !⟩) = Value V × 𝒱⟦ G ⟧ V
    𝒱⟦ _ ⟧ _ = ⊥

Note that the definitions of 𝓔 and 𝓥 are recursive. Unfortunately they
are not proper definitions of (total) functions because there is no
guarantee of termination. For simple languages, like the Simply Typed
Lambda Calculus, 𝓥 can be defined by recursion on the type A. However,
here we have the unknown type ★ and the recursion for that clause
invokes `𝒱⟦ G ⟧ V`, but `G` is not a structural part of ★.  (The
definition of 𝓔 above is also problematic, but one can reformulate 𝓔
to remove the recursion in 𝓔.)

## An Explicitly Step-indexed Logical Relation for Type Safety

We can force the definitions of 𝓔 and 𝓥 to terminate using
step-indexing (aka. the "gasoline" technique), which was first applied
to logical relations by Appel and McAllester (TOPLAS 2001). We add a
parameter k (a natural number) to 𝓔 and 𝓥, and decrement k on each
recursive call. When k is zero, 𝓔 and 𝓥 accept all terms. Thus, the
meaning of `𝓔⟦ A ⟧ M k` is that term `M` is guaranteed to behave
according to type `A` for `k` reduction steps, but after that there
are no guarantees.

    ℰ⟦_⟧ : (A : Type) → Term → ℕ → Set
    ℰ⟦ A ⟧ M 0 = ⊤
    ℰ⟦ A ⟧ M (suc k) = (𝒱 ⟦ A ⟧ M k ⊎ reducible M ⊎ Blame M)
                        × (∀ N → (M —→ N) → ℰ⟦ A ⟧ N k)

    𝒱⟦_⟧ : (A : Type) → Term → ℕ → Set
    𝒱⟦ A ⟧ M 0 = ⊤
    𝒱⟦ ι ⟧ ($ ι′ c) (suc k) = ι ≡ ι′
    𝒱⟦ A ⇒ B ⟧ (ƛ N) (suc k) = ∀ W → 𝒱⟦ A ⟧ W k → ℰ⟦ B ⟧ (N [ W ]) k
    𝒱⟦ ★ ⟧ (V ⟨ G , g !⟩) (suc k) = Value V × 𝒱⟦ G ⟧ V k
    𝒱⟦ _ ⟧ _ (suc k) = ⊥

We now have proper definitions of 𝓔 and 𝓥 but proving theorems about
these definitions involves a fair bit of reasoning about the step
indices, which is tedious, especially in Agda because it's support for
automating arithmetic proofs is cumbersome to use.  To streamline the
definitions and proofs that involve step indexing, Dreyer, Ahmed, and
Birkedal (2011) propose the use of a temporal logic that hides the
step indexing. Next we discuss the embedding of such a logic in Agda.


## Step-indexed Logic

```
open import rewriting.examples.StepIndexedLogic
```

Our Step-indexed Logic (SIL) is a first-order logic (i.e., a logic
with "and", "or", "implies", "for all"). To distinguish its
connectives from Agda's, we add a superscript "o". So "and" is written
`×ᵒ`, "implies" is written `→ᵒ`, and so on.  The SIL also includes a
notion of time in which there is clock counting down. The logic is
designed in such a way that if a formula `P` is true at some time then
`P` stays true in the future (at lower counts). When the clock reaches
zero, every formula becomes true.  Furthermore, the logic includes a
"later" operator, written `▷ᵒ P`, meaning that `P` is true one clock
tick in the future.

Just as `Set` is the type of true/false formulas in Agda, `Setᵒ` is
the type of true/false formulas in SIL. It is a record that bundles
the formula itself, represented with a function of type `ℕ → Set`,
with proofs that the formula is downward closed and true at zero.

    record Setᵒ : Set₁ where
      field
        # : ℕ → Set
        down : downClosed #
        tz : # 0                -- tz short for true at zero
    open Setᵒ public

For example, the "false" proposition is false at every time except zero.

    ⊥ᵒ : Setᵒ
    ⊥ᵒ = record { # = λ { zero → ⊤ ; (suc k) → ⊥ }
                ; down = ... ; tz = ... }

The "and" proposition `P ×ᵒ Q` is true at a given time `k` if both `P`
and `Q` are true at time `k`.

    _×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
    P ×ᵒ Q = record { # = λ k → # P k × # Q k
                    ; down = ... ; tz = ... }

We embed arbitrary Agda formulas into the step-indexed logic with the
following operator, written `S ᵒ`, which is true if and only if `S` is
true, except at time zero, when `S ᵒ` has to be true.

    _ᵒ  : Set → Setᵒ
    S ᵒ = record { # = λ { zero → ⊤ ; (suc k) → S }
                 ; down = ... ; tz = ... }

In addition to true/false propositions, the step-indexed logic can
express predicates, which we represent in Agda simply as functions
into `Setᵒ`.

    Predᵒ : Set → Set₁
    Predᵒ A = A → Setᵒ





```

open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)

instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

mreduce : Term × Term → Fun (Term × Term) ⊤ Wellfounded
mreduce (M , N) = (M ≡ N)ᶠ ⊎ᶠ (∃ᶠ[ L ] (M —→ L)ᶠ ×ᶠ ▷ᶠ (recur (L , N)))

infix 2 _—→*_
_—→*_ : Term → Term → Set
M —→* N =
   let F : Fun (Term × Term) (Term × Term) Wellfounded
       F = flipᶠ mreduce tt in
   Σ[ n ∈ ℕ ] (#(μᵒ F (M , N)) n)
