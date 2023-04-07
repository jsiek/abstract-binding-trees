# Type Safety in 10 Easy, 4 Medium, and 1 Hard Lemma using Step-indexed Logical Relations

```
{-# OPTIONS --rewriting #-}
module rewriting.examples.BlogTypeSafety10Easy4Med1Hard where

open import Data.Nat
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)

```

Ok, so logical relations are overkill for proving type safety. The
proof technique is better suited to proving more interesting
properties such as parametricity, program equivalence, and the gradual
guarantee.  Nevertheless, understanding a proof of type safety via
logical relations is a helpful stepping stone to understanding these
more complex use cases, especial when the logical relations employ
more advanced techniques, such as step indexing.  In this blog post I
prove type safety of a cast calculus (an intermediate language of the
gradually typed lambda calculus).  The proof is in Agda and the proof
uses step-indexed logical relations because the presence of the
unknown type (aka. dynamic type) prevents the use of regular logical
relations. To reduce the clutter of reasoning about step indexing, we
conduct the proof using a temporal logic, in the spirit of the LSLR
logic of Dreyer, Ahmed, and Birkedal (2011), that we embed in Agda.

## Review of the Cast Calculus

```
open import rewriting.examples.Cast
```

We review the syntax and reduction rules of this cast calculus.  Just
like the lambda calculus, types include base types (Booleans and
natural numbers), and function types. To support gradual typing, we
include the unknown type ★.

    ι ::= 𝔹 | ℕ
    A,B,C,G,H ::= ι | A ⇒ B | ★

The ground types are 

    G,H ::= ι | ★⇒★

Just like the lambda calculus, there are variables (de Bruijn indices),
lambdas, and application. We also throw in literals (Booleans and
natural numbers).  To support gradual typing, we include a term
`M ⟨ G !⟩` for injecting from a ground type `G` to the unknown type, and
a term `M ⟨ H ?⟩` for projecting from the unknown type
back out to a ground type.  Finally, we include the `blame` term to
represent trapped runtime errors.  The syntax is a bit odd to make
Agda happy.

    L,M,N ::= ` x | ƛ N | L · M | $ k | M ⟨ G !⟩ | M ⟨ H ?⟩ | blame

This cast calculus is somewhat unusual in that it only includes injections
and projections but not the other kinds of casts that one typically
has in a cast calculus, e.g. from `★ ⇒ ℕ` to `ℕ ⇒ ℕ`. That is OK
because those other casts can still be expressed in this cast calculus.

The values include lambdas, literals, and injected values.

    V,W ::= ƛ N | $ c | V ⟨ G !⟩

The reduction rules make use of frames, which are defined as follows.

    F ::= □· M | V ·□ | □⟨ G !⟩ | □⟨ H ?⟩

The operation `F ⟦ M ⟧` plugs a term into a frame.

The reduction rules of the cast calculus are as follows:

    (ξ)        If M —→ N, then F ⟦ M ⟧ —→ F ⟦ N ⟧
    (ξ-blame)  F ⟦ blame ⟧ —→ blame
    (β)        (ƛ N) · W —→ N [ W ]
    (collapse) V ⟨ G !⟩ ⟨ G ?⟩ —→ V
    (collide)  If G ≢ H, then V ⟨ G !⟩ ⟨ H ?⟩ —→ blame.


## A First Attempt at a Logical Relation for Type Safety

The following is a first attempt to define a logical relation for type
safety for the cast calculus. The predicate 𝓔 expresses the semantic
notion of a term being well typed at a given type A. Here we define that
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
well typed at `B`. For the unknown type `★`, the value must be
an injection of a value `V` from some ground type `G`, and `V`
must be semantically well typed at `G`.

    𝒱⟦_⟧ : (A : Type) → Term → Set
    𝒱⟦ ι ⟧ ($ c) = ι ≡ typeof c
    𝒱⟦ A ⇒ B ⟧ (ƛ N) = ∀ W → 𝒱⟦ A ⟧ W → ℰ⟦ B ⟧ (N [ W ])
    𝒱⟦ ★ ⟧ (V ⟨ G !⟩) = Value V × 𝒱⟦ typeofGround G ⟧ V
    𝒱⟦ _ ⟧ _ = ⊥

Note that the definitions of 𝓔 and 𝓥 are recursive. Unfortunately they
are not proper definitions of (total) functions because there is no
guarantee of their termination. For simple languages, like the Simply
Typed Lambda Calculus, 𝓥 can be defined by recursion on the type
`A`. However, here we have the unknown type `★` and the recursion in that
clause invokes `𝒱⟦ typeofGround G ⟧ V`, but `typeofGround G` is
not a structural part of ★ (nothing is).
(The definition of 𝓔 above is also problematic, but one could
reformulate 𝓔 to remove the recursion in 𝓔.)

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
    𝒱⟦ ★ ⟧ (V ⟨ G !⟩) (suc k) = Value V × 𝒱⟦ typeofGround G ⟧ V k
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

The "for all" proposition `∀ᵒ[ a ] P` is true at a given time `k` if
the predicate `P` is true for all `a` at time `k`.

    ∀ᵒ : ∀{A : Set} → (A → Setᵒ) → Setᵒ
    ∀ᵒ{A} P = record { # = λ k → ∀ (a : A) → # (P a) k
                     ; down = ... ; tz = ... }

The "exists" proposition `∃ᵒ[ a ] P` is true at a given time `k` if
the predicate `P` is true for some `a` at time `k`. However, we
must require that the type `A` is inhabited.

    ∃ᵒ : ∀{A : Set}{{_ : Inhabited A}} → (A → Setᵒ) → Setᵒ
    ∃ᵒ{A} P = record { # = λ k → Σ[ a ∈ A ] # (P a) k
                         ; down = ... ; tz = ... }

We embed arbitrary Agda formulas into the step-indexed logic with the
following operator, written `S ᵒ`, which is true if and only if `S` is
true, except at time zero, when `S ᵒ` has to be true.

    _ᵒ  : Set → Setᵒ
    S ᵒ = record { # = λ { zero → ⊤ ; (suc k) → S }
                 ; down = ... ; tz = ... }

Next we discuss the most important and interesting of the propositions,
the one for defining a recursive predicate. The following is a first
attempt at writing down the type of this proposition. The idea is that
this constructor of recursive predicates works like the Y-combinator
in that it turns a non-recursive predicate into a recursive one.

    recursiveᵒ : ∀{A}
       → (A → (A → Setᵒ) → Setᵒ)
         -----------------------
       → A → Setᵒ

The non-recursive predicate has type `A → (A → Setᵒ) → Setᵒ`. It has
an extra parameter `(A → Setᵒ)` that will be supplied with the
recursive predicate itself. To clarify, lets look at an example.
Suppose we wanted to define multi-step reduction according to
the following rules:

                M —→ L    L —→* N
    -------     ------------------
    M —→* M     M —→* N

We would first define a non-recursive predicate that has an extra
parameter, let us name it `R` for recursion.

    mreduce : Term × Term → (Term × Term → Setᵒ) → Setᵒ
    mreduce (M , N) R = (M ≡ N)ᵒ ⊎ᵒ (∃ᵒ[ L ] (M —→ L)ᵒ ×ᵒ R (L , N))

Because we use "exists" with a Term, we need to prove that Term is inhabited.

```
instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

```
We then apply the `recursiveᵒ` proposition to `mreduce` to
obtain the desired recursive predicate `—→*`.

    _—→*_ : Term → Term → Setᵒ
    M —→* N = recursiveᵒ mreduce (M , N)

The problem with the above story is that it's not possible (to my
knowledge) to construct a recursive predicate from an arbitrary
function of type `A → (A → Setᵒ) → Setᵒ`. Instead, we need to place
restrictions on the function. In particular, if we make sure that the
recursion never happens "now", but only "later", then it becomes
possible to construct `recursiveᵒ`. We define the `RecSetᵒ` type in
Agda to capture this restriction.

    RecSetᵒ A κ

The `A` in `RecSetᵒ A κ` the parameter type for the recursion
and κ is `Now` or `Later`.  We then define variants of all the
propositions that work on RecSetᵒ instead of Setᵒ and that track
whether the recursive call happened now or later.

For example, the "later" operator, `▷ᶠ P`, asserts that `P` is true
the future, so regardless of whether `P` contained any recursive
calls, the predicate `▷ᶠ P` can safely say that use of recursion in it
happened `Later`.

    ▷ᶠ : ∀{A}{κ} → RecSetᵒ A κ → RecSetᵒ A Later

The "and" operator, `P ×ᶠ Q` is categorized as `Later` only if
both `P` and `Q` are `Later`. Otherwise it is `Now`.
So we use the following function to choose:

    choose : Kind → Kind → Kind
    choose Now Now = Now
    choose Now Later = Now
    choose Later Now = Now
    choose Later Later = Later

Here's the type of the "and" operator:

    _×ᶠ_ : ∀{A}{κ₁ κ₂} → RecSetᵒ A κ₁ → RecSetᵒ A κ₂ → RecSetᵒ A (choose κ₁ κ₂)

The other propositions following a similar pattern.

The special `recur` proposition invokes the recursion. It takes an
argument of type `A` and produces a `RecSetᵒ` that indicates that the
recursion happened `Now`.

    recurᶠ : ∀{A} → A → RecSetᵒ A Now

So the type of `recursiveᵒ` takes a non-recursive function from `A` to
a `RecSetᵒ` and then produces a recursive predicate in `A`.

    recursiveᵒ : ∀{A}
       → (A → RecSetᵒ A Later)
         ---------------------
       → A → Setᵒ

Let's revisit the example of defining multi-step reduction.  The
non-recursive `mreduce` predicate is defined as follows.

```
mreduce : Term × Term → RecSetᵒ (Term × Term) Later
mreduce (M , N) = (M ≡ N)ᶠ ⊎ᶠ (∃ᶠ[ L ] (M —→ L)ᶠ ×ᶠ ▷ᶠ (recurᶠ (L , N)))
```

Note that the `R` parameter has become implicit; it is hidden inside
the `RecSetᵒ` type. Also the use of `R`, the application `R (L , N)`
is replaced by `▷ᶠ (recurᶠ (L , N))`.

We define the recursive predicate `M —→* N` by applying `recursiveᵒ`
to `mreduce`.

```
infix 2 _—→*_
_—→*_ : Term → Term → Setᵒ
M —→* N = recursiveᵒ mreduce (M , N)
```

Here are a couple uses of the multi-step reduction relation.

```
X₀ : #($ (Num 0) —→* $ (Num 0)) 1
X₀ = inj₁ refl

X₁ : #((ƛ ($ (Num 1))) · $ (Num 0) —→* $ (Num 1)) 2
X₁ = inj₂ (_ , (β ($̬ _) , inj₁ refl))
```
