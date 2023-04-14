# Type Safety in 10 Easy, 4 Medium, and 1 Hard Lemma using Step-indexed Logical Relations

```
{-# OPTIONS --rewriting #-}
module rewriting.examples.BlogTypeSafety10Easy4Med1Hard where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
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
open import rewriting.examples.StepIndexedLogic2
```

Our Step-indexed Logic (SIL) is a first-order logic (i.e., a logic
with "and", "or", "implies", "for all"). To distinguish its
connectives from Agda's, we add a superscript "o". So "and" is written
`×ᵒ`, "implies" is written `→ᵒ`, and so on.  SIL also includes a
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

    μᵒ : ∀{A}
       → (A → (A → Setᵒ) → Setᵒ)
         -----------------------
       → A → Setᵒ

The non-recursive predicate has type `A → (A → Setᵒ) → Setᵒ`. It has
an extra parameter `(A → Setᵒ)` that will be bound to the
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
We then apply the `μᵒ` proposition to `mreduce` to
obtain the desired recursive predicate `—→*`.

    _—→*_ : Term → Term → Setᵒ
    M —→* N = μᵒ mreduce (M , N)

The problem with the above story is that it's not possible (to my
knowledge) to construct a recursive predicate from an arbitrary
function of type `A → (A → Setᵒ) → Setᵒ`. Instead, we need to place
restrictions on the function. In particular, if we make sure that the
recursion never happens "now", but only "later", then it becomes
possible to construct `μᵒ`. We define the `Setˢ` type in Agda to
capture this restriction. (The superscript "s" stands for step
indexed.) Furthermore, to allow the nesting of recursive definitions,
we must generalize from a single predicate parameter to an environment
of predicates. The type of the environment is given by a `Context`:

    Context : Set₁
    Context = List Set

We represent recursive environments with tuples.

    RecEnv : Context → Set₁
    RecEnv [] = topᵖ 
    RecEnv (A ∷ Γ) = (A → Setᵒ) × RecEnv Γ

We use de Bruijn indices to represent the variables that refer to the
recursive predicates, which we define as follows.

    data _∋_ : Context → Set → Set₁ where
      zeroˢ : ∀{Γ}{A} → (A ∷ Γ) ∋ A
      sucˢ : ∀{Γ}{A}{B} → Γ ∋ B → (A ∷ Γ) ∋ B

For each variable, we track whether it has been used "now"
or not. So we define `Time` as follows.

    data Time : Set where
      Now : Time
      Later : Time

and the following defines a list of times, one for each variable in `Γ`.

    data Times : Context → Set₁ where
      ∅ : Times []
      cons : ∀{Γ}{A} → Time → Times Γ → Times (A ∷ Γ)

The `Setˢ` type is a record indexed by the type of the environment and
by the times for each variable. The representation of `Setˢ` (the `#`
field) is a function that maps an environment of predicates
(one predicate for each in-scope μ) to a `Setᵒ`.

    record Setˢ (Γ : Context) (ts : Times Γ) : Set₁ where
      field
        # : RecEnv Γ → Setᵒ 
        ...
    open Setˢ public

We define variants of all the propositional connectives to work on
Setˢ.

The "later" operator asserts that `P` is true in the future, so the
predicate `▷ˢ P` can safely say that any use of recursive predicate in
`P` happen `Later`.

    laters : ∀ (Γ : Context) → Times Γ
    laters [] = ∅
    laters (A ∷ Γ) = cons Later (laters Γ)

    ▷ˢ : ∀{Γ}{ts : Times Γ}
       → Setˢ Γ ts
         -----------------
       → Setˢ Γ (laters Γ)

The "and" operator, `P ×ˢ Q` is categorized as `Later` only if both
`P` and `Q` are `Later`. Otherwise it is `Now`.  We use the following
function to make this choice:

    choose : Kind → Kind → Kind
    choose Now Now = Now
    choose Now Later = Now
    choose Later Now = Now
    choose Later Later = Later

We define `combine` to apply `choose` to a list of times.

    combine : ∀{Γ} (ts₁ ts₂ : Times Γ) → Times Γ
    combine {[]} ts₁ ts₂ = ∅
    combine {A ∷ Γ} (cons x ts₁) (cons y ts₂) =
        cons (choose x y) (combine ts₁ ts₂)

Here's the type of the "and" operator:

    _×ˢ_ : ∀{Γ}{ts₁ ts₂ : Times Γ} → Setˢ Γ ts₁ → Setˢ Γ ts₂
       → Setˢ Γ (combine ts₁ ts₂)

The other propositions follow a similar pattern.

The membership formula `a ∈ x` is true when `a` is in the predicate
bound to variable `x` in the environment. The time for `x` is required
to be `Now`.

    one-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
    one-now (B ∷ Γ) zeroˢ = cons Now (laters Γ)
    one-now (B ∷ Γ) (sucˢ x) = cons Later (one-now Γ x)

    _∈_ : ∀{Γ}{A}
       → A
       → (x : Γ ∋ A)
       → Setˢ Γ (one-now Γ x)
    a ∈ x =
      record { # = λ δ → (lookup x δ) a
             ; ... }

The `μˢ` formula defines a (possibly nested) recursive predicate.

    μˢ : ∀{Γ}{ts : Times Γ}{A}
       → (A → Setˢ (A ∷ Γ) (cons Later ts))
         ----------------------------------
       → (A → Setˢ Γ ts)

It takes a non-recursive predicate from `A` to `Setˢ` and produces a
recursive predicate in `A`. Note that the variable `zeroˢ`, the
one introduced by this `μˢ`, is required to have time `Later`.

If the recursive predicate is not nested inside other recursive
predicates, then you can directly use the following `μᵒ` operator.

    μᵒ : ∀{A}
       → (A → Setˢ (A ∷ []) (cons Later ∅))
         ----------------------------------
       → (A → Setᵒ)

Let's revisit the example of defining multi-step reduction.  The
non-recursive `mreduce` predicate is defined as follows.

```
mreduce : Term × Term → Setˢ ((Term × Term) ∷ []) (cons Later ∅)
mreduce (M , N) = (M ≡ N)ˢ ⊎ˢ (∃ˢ[ L ] (M —→ L)ˢ ×ˢ ▷ˢ (((L , N) ∈ zeroˢ)))
```

Note that the `R` parameter has become implicit; it has moved into the
environment. Also the application `R (L , N)` is replaced by
`▷ˢ ((L , N) ∈ zeroˢ)`, where the de Bruijn index `zeroˢ` refers to
the predicate `R` in the environment.

We define the recursive predicate `M —→* N` by applying `μᵒ`
to `mreduce`.

```
infix 2 _—→*_
_—→*_ : Term → Term → Setᵒ
M —→* N = μᵒ mreduce (M , N)
```

Here are a couple uses of the multi-step reduction relation.

```
X₀ : #($ (Num 0) —→* $ (Num 0)) 1
X₀ = inj₁ refl

X₁ : #((ƛ ($ (Num 1))) · $ (Num 0) —→* $ (Num 1)) 2
X₁ = inj₂ (_ , (β ($̬ _) , inj₁ refl))
```

## Proofs in Step-indexed Logic

Just like first-orderd logic, SIL comes with rules of deduction for
carrying out proofs. The judgement form is `𝓟 ⊢ᵒ P`, where `𝓟` is a
list of assumptions and `P` is a formula.  The judgement `𝓟 ⊢ᵒ P` is
true iff for every time `k`, all of `𝓟` are true at `k` implies that `P`
is true at `k`. So in Agda we have the following definition.

    Πᵒ : List Setᵒ → Setᵒ
    Πᵒ [] = ⊤ᵒ
    Πᵒ (P ∷ 𝓟) = P ×ᵒ Πᵒ 𝓟 

    _⊢ᵒ_ : List Setᵒ → Setᵒ → Set
    𝓟 ⊢ᵒ P = ∀ k → # (Πᵒ 𝓟) k → # P k

Many of the deduction rules are the same as in first order logic.
For example, here are the introduction and elimination rules
for conjunction. We use the same notation as Agda, but with
a superscript "o".

    _,ᵒ_ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
      → 𝓟 ⊢ᵒ P
      → 𝓟 ⊢ᵒ Q
        ------------
      → 𝓟 ⊢ᵒ P ×ᵒ Q

    proj₁ᵒ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
      → 𝓟 ⊢ᵒ P ×ᵒ Q
        ------------
      → 𝓟 ⊢ᵒ P

    proj₂ᵒ : ∀{𝓟 : List Setᵒ }{P Q : Setᵒ}
      → 𝓟 ⊢ᵒ P ×ᵒ Q
        ------------
      → 𝓟 ⊢ᵒ Q

Analogous to `subst` in Agda's standard library, SIL has `substᵒ`
which says that if `P` and `Q` are equivant, then a proof of `P` gives
a proof of `Q`.

    substᵒ : ∀{𝓟}{P Q : Setᵒ}
      → P ≡ᵒ Q
        -------------------
      → 𝓟 ⊢ᵒ P  →  𝓟 ⊢ᵒ Q

The deduction rules also include ones for the "later" operator.  As we
mentioned earlier, if a proposition is true now it will also be true
later.

  monoᵒ : ∀ {𝓟}{P}
     → 𝓟 ⊢ᵒ P
       -----------
     → 𝓟 ⊢ᵒ  ▷ᵒ P

One can transport induction on natural numbers into SIL to obtain the
following Löb rule, which states that when proving any property `P`,
one is allowed to assume that `P` is true later.

  lobᵒ : ∀ {𝓟}{P}
     → (▷ᵒ P) ∷ 𝓟 ⊢ᵒ P
       -----------------------
     → 𝓟 ⊢ᵒ P

For comparison, here's induction on natural numbers

      P 0
    → (∀ k → P k → P (suc k))
    → ∀ n → P n

In the world of SIL, propositions are always true at zero, so the base
case `P 0` is not necessary. The induction step `(∀ k → P k → P (suc k))`
is similar to the premise `(▷ᵒ P) ∷ 𝓟 ⊢ᵒ P` because `▷ᵒ` subtracts one.

As usual for temporal logics (or more generally, for modal logics),
there are distribution rules that push "later" through the other
logical connectives. For example, the following rule distributes
"later" through conjunction.

  ▷× : ∀{𝓟} {P Q : Setᵒ}
     → 𝓟 ⊢ᵒ (▷ᵒ (P ×ᵒ Q))
       ----------------------
     → 𝓟 ⊢ᵒ (▷ᵒ P) ×ᵒ (▷ᵒ Q)

This project was the first time for me conducting nontrivial proofs in
a modal logic, and it took some getting use to.


## Logical Relation for Type Safety

With the Step-indexed Logic in hand, we are ready to define a logical
relation for type safety. The two predicates 𝓔 and 𝓥 are mutually
recursive, so we combine them into a single recursive predicate named
`ℰ⊎𝒱` that takes a sum type, where the left side is for 𝓔 and the
right side is for 𝓥. We shall define `ℰ⊎𝒱` by an application of
`recursiveᵒ`, so we first need to define the non-recursive version of
`ℰ⊎𝒱`, which we call `pre-ℰ⊎𝒱`, defined below. It simply dispatches to
the non-recursive `pre-ℰ` and `pre-ℰ` which we define next.

```
ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Type × Term) ⊎ (Type × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

pre-ℰ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
ℰ⊎𝒱 (inj₁ (A , V)) = pre-𝒱 A V
ℰ⊎𝒱 (inj₂ (A , M)) = pre-ℰ A M
```

To improve the readability of our definitions, we define the following
notation for recursive applications of the 𝓔 and 𝓥 predicates.

```
ℰˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A ⟧ M = (inj₂ (A , M)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A ⟧ V = (inj₁ (A , V)) ∈ zeroˢ
```

The definition of pre-𝓔 and pre-𝓥 are of similar form to the
explicitly step-indexed definition of 𝓔 and 𝓥 above, however the
parameter `k` is gone and all of the logical connectives have a
superscript `f`, indicating that we're building a `RecSetᵒ`.  Also,
note that all the uses of `𝓔ˢ` and `𝓥ˢ` are guarded by the later
operator `▷ˢ`. Finally, in the definition of pre-𝓔, we do not use `▷ˢ
(𝓥⟦ A ⟧ M)` but instead use `pre-𝓥 A M` because we need to say there
that `M` is a semantic value now, not later.

```
pre-ℰ A M = (pre-𝒱 A M ⊎ˢ (reducible M)ˢ ⊎ˢ (Blame M)ˢ)
             ×ˢ (∀ˢ[ N ] (M —→ N)ˢ →ˢ ▷ˢ (ℰˢ⟦ A ⟧ N))
pre-𝒱 ★ (V ⟨ G !⟩ )      = (Value V)ˢ ×ˢ ▷ˢ (𝒱ˢ⟦ typeofGround G ⟧ V)
pre-𝒱 ($ₜ ι) ($ c)        = (ι ≡ typeof c)ˢ
pre-𝒱 (A ⇒ B) (ƛ N)      = ∀ˢ[ W ] ▷ˢ (𝒱ˢ⟦ A ⟧ W) →ˢ ▷ˢ (ℰˢ⟦ B ⟧ (N [ W ]))
pre-𝒱 A M                = ⊥ ˢ
```

We define ℰ and 𝒱 by creating a recursive predicate (apply `μᵒ` to
`ℰ⊎𝒱`) and then apply it to either `inj₁` for 𝒱 or `inj₂` for ℰ.

```
ℰ⟦_⟧ : Type → Term → Setᵒ
ℰ⟦ A ⟧ M = (μᵒ ℰ⊎𝒱) (inj₂ (A , M))

𝒱⟦_⟧ : Type → Term → Setᵒ
𝒱⟦ A ⟧ V = (μᵒ ℰ⊎𝒱) (inj₁ (A , V))
```

To succinctly talk about the two aspects of 𝓔, we define semantic
`progress` and `preservation` as follows.

```
progress : Type → Term → Setᵒ
progress A M = 𝒱⟦ A ⟧ M ⊎ᵒ (reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ

preservation : Type → Term → Setᵒ
preservation A M = ∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N))
```

We can prove that ℰ is indeed equivalent to progress and preservation
by use of the `fixpointᵒ` theorem in SIL.

```
ℰ-stmt : ∀{A}{M}
  → ℰ⟦ A ⟧ M ≡ᵒ progress A M ×ᵒ preservation A M
ℰ-stmt {A}{M} =
  ℰ⟦ A ⟧ M                                                  ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ ℰ⊎𝒱 (inj₂ (A , M))                 ⩦⟨ fixpointᵒ ℰ⊎𝒱 (inj₂ (A , M)) ⟩
  # (ℰ⊎𝒱 (inj₂ (A , M))) ((μᵒ ℰ⊎𝒱) , ttᵖ)
              ⩦⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (fixpointᵒ ℰ⊎𝒱 (inj₁ (A , M))))
                                  (≡ᵒ-refl refl)) (≡ᵒ-refl refl) ⟩
  progress A M ×ᵒ preservation A M
  ∎
```

For convenience, we define introduction and elimination rules for ℰ.

```
ℰ-intro : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ progress A M
  → 𝓟 ⊢ᵒ preservation A M
    ----------------------
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
ℰ-intro 𝓟⊢prog 𝓟⊢pres = substᵒ (≡ᵒ-sym ℰ-stmt) (𝓟⊢prog ,ᵒ 𝓟⊢pres)

ℰ-progress : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
  → 𝓟 ⊢ᵒ progress A M
ℰ-progress 𝓟⊢ℰM = proj₁ᵒ (substᵒ ℰ-stmt 𝓟⊢ℰM )

ℰ-preservation : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
  → 𝓟 ⊢ᵒ preservation A M
ℰ-preservation 𝓟⊢ℰM = proj₂ᵒ (substᵒ ℰ-stmt 𝓟⊢ℰM )
```

