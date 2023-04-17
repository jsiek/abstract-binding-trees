# Type Safety in 10 Easy, 4 Medium, and 1 Hard Lemma using Step-indexed Logical Relations

```
{-# OPTIONS --rewriting #-}
module rewriting.examples.BlogTypeSafety10Easy4Med1Hard where

open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; yes; no)
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
unknown type (aka. dynamic type) prevents the use of logical relations
that are only indexed by types. To reduce the clutter of reasoning
about step indexing, we conduct the proof using a temporal logic, in
the spirit of the LSLR logic of Dreyer, Ahmed, and Birkedal (2011),
that we embed in Agda.

## Review of the Cast Calculus

```
open import Var
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

Just like the lambda calculus, there are variables (de Bruijn
indices), lambdas, and application. We throw in literals
(Booleans and natural numbers).  Also, to support gradual typing, we
include a term `M ⟨ G !⟩` for injecting from a ground type `G` to the
unknown type, and a term `M ⟨ H ?⟩` for projecting from the unknown
type back out to a ground type.  Finally, we include the `blame` term
to represent trapped runtime errors.

    L,M,N ::= ` x | ƛ N | L · M | $ k | M ⟨ G !⟩ | M ⟨ H ?⟩ | blame

This cast calculus is somewhat unusual in that it only includes
injections and projections but not the other kinds of casts that one
typically has in a cast calculus, such as a cast from one function type
`★ ⇒ ℕ` to another function type `ℕ ⇒ ℕ`. That is OK because those
other casts can still be expressed in this cast calculus.

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
safety for the cast calculus. The predicate ℰ expresses the semantic
notion of a term being well typed at a given type A. Here "semantic"
means "runtime behavior". We define that a term M is semantically well
typed at type A if it satisfies "progress" and "preservation". The
progress part says that M is either (1) a semantic value at type `A`,
(2) reducible, or (3) an error. The preservation part says that if M
reduces to N, then N is also semantically well typed at A.

    ℰ⟦_⟧ : (A : Type) → Term → Set
    ℰ⟦ A ⟧ M = (𝒱 ⟦ A ⟧ M ⊎ reducible M ⊎ Blame M)
                × (∀ N → (M —→ N) → ℰ⟦ A ⟧ N)

The predicate 𝒱 expresses the semantic notion of a value being well
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
    𝒱⟦ ★ ⟧ (V ⟨ G !⟩) = Value V × 𝒱⟦ gnd⇒ty G ⟧ V
    𝒱⟦ _ ⟧ _ = ⊥

Note that the definitions of ℰ and 𝒱 are recursive. Unfortunately they
are not proper definitions of (total) functions because there is no
guarantee of their termination. For simple languages, like the Simply
Typed Lambda Calculus, 𝒱 can be defined by recursion on the type
`A`. However, here we have the unknown type `★` and the recursion in that
clause invokes `𝒱⟦ gnd⇒ty G ⟧ V`, but `gnd⇒ty G` is
not a structural part of `★` (nothing is).
(The definition of ℰ above is also problematic, but one could
reformulate ℰ to remove the recursion in ℰ.)

## An Explicitly Step-indexed Logical Relation for Type Safety

We can force the definitions of ℰ and 𝒱 to terminate using
step-indexing (aka. the "gasoline" technique), which was first applied
to logical relations by Appel and McAllester (TOPLAS 2001). We add a
parameter k (a natural number) to ℰ and 𝒱, and decrement k on each
recursive call. When k is zero, ℰ and 𝒱 accept all terms. Thus, the
meaning of `ℰ⟦ A ⟧ M k` is that term `M` is guaranteed to behave
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
    𝒱⟦ ★ ⟧ (V ⟨ G !⟩) (suc k) = Value V × 𝒱⟦ gnd⇒ty G ⟧ V k
    𝒱⟦ _ ⟧ _ (suc k) = ⊥

We now have proper definitions of ℰ and 𝒱 but proving theorems about
these definitions involves a fair bit of reasoning about the step
indices, which is tedious, especially in Agda because it's support for
automating proofs about arithmetic is cumbersome to use.  To
streamline the definitions and proofs that involve step indexing,
Dreyer, Ahmed, and Birkedal (2011) propose the use of a temporal logic
that hides the step indexing. Next we discuss the embedding of such a
logic in Agda.


## Step-indexed Logic

```
open import rewriting.examples.StepIndexedLogic2
```

Our Step-indexed Logic (SIL) includes first-order logic (i.e., a logic
with "and", "or", "implies", "for all", etc.). To distinguish its
connectives from Agda's, we add a superscript "o". So "and" is written
`×ᵒ`, "implies" is written `→ᵒ`, and so on.  SIL also includes a
notion of time in which there is clock counting down. The logic is
designed in such a way that if a formula `P` is true at some time then
`P` stays true in the future (at lower counts). So formulas are
downward closed.  When the clock reaches zero, every formula becomes
true.  Furthermore, the logic includes a "later" operator, written `▷ᵒ
P`, meaning that `P` is true one clock tick in the future. When we use
SIL to reason about the cast calculus, one clock tick will correspond
to one reduction step.

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
must require that the type `A` is inhabited so that this proposition
is true at time zero.

    ∃ᵒ : ∀{A : Set}{{_ : Inhabited A}} → (A → Setᵒ) → Setᵒ
    ∃ᵒ{A} P = record { # = λ k → Σ[ a ∈ A ] # (P a) k
                         ; down = ... ; tz = ... }

We embed arbitrary Agda formulas into the step-indexed logic with the
following constant operator, written `S ᵒ`, which is true if and only
if `S` is true, except at time zero, when `S ᵒ` has to be true.

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
Suppose we want to define multi-step reduction according to
the following rules:

                M —→ L    L —→* N
    -------     ------------------
    M —→* M     M —→* N

We would first define a non-recursive predicate that has an extra
parameter, let us name it `R` for recursion. Inside the definition of
`mreduce`, we use `R` is the place where we would recursively use
`mreduce`, as follows.

    mreduce : Term × Term → (Term × Term → Setᵒ) → Setᵒ
    mreduce (M , N) R = (M ≡ N)ᵒ ⊎ᵒ (∃ᵒ[ L ] (M —→ L)ᵒ ×ᵒ R (L , N))

Because we use `∃ᵒ` with a Term, we need to prove that Term is inhabited.

```
instance
  TermInhabited : Inhabited Term
  TermInhabited = record { elt = ` 0 }

```
We then apply the `μᵒ` proposition to `mreduce` to
obtain the desired recursive predicate `—→*`.

    _—→*_ : Term → Term → Setᵒ
    M —→* N = μᵒ mreduce (M , N)

The problem with the above story is that it's not possible in Agda (to
my knowledge) to construct a recursive predicate from an arbitrary
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

We represent an environment of recursive predicates with a tuple of
the following type.

    RecEnv : Context → Set₁
    RecEnv [] = topᵖ 
    RecEnv (A ∷ Γ) = (A → Setᵒ) × RecEnv Γ

We use de Bruijn indices to represent the variables that refer to the
recursive predicates, which we define as follows.

    data _∋_ : Context → Set → Set₁ where
      zeroˢ : ∀{Γ}{A} → (A ∷ Γ) ∋ A
      sucˢ : ∀{Γ}{A}{B} → Γ ∋ B → (A ∷ Γ) ∋ B

For each variable, we track whether it has been used "now" or not. So
we define `Time` as follows. The `Later` constructor does double duty
to mean a predicate has either been used "later" or not at all.

    data Time : Set where
      Now : Time
      Later : Time

The following defines a list of times, one for each variable in `Γ`.

    data Times : Context → Set₁ where
      ∅ : Times []
      cons : ∀{Γ}{A} → Time → Times Γ → Times (A ∷ Γ)

The `Setˢ` type is a record indexed by the type of the environment and
by the time for each variable. The representation of `Setˢ` (the `#`
field) is a function that maps an environment of predicates
(one predicate for each in-scope μ) to a `Setᵒ`.

    record Setˢ (Γ : Context) (ts : Times Γ) : Set₁ where
      field
        # : RecEnv Γ → Setᵒ 
        ...
    open Setˢ public

We define variants of all the propositional connectives to work on
Setˢ.

The "later" operator `▷ˢ` asserts that `P` is true in the future, so the
predicate `▷ˢ P` can safely say that any use of recursive predicate in
`P` happens `Later`.

    laters : ∀ (Γ : Context) → Times Γ
    laters [] = ∅
    laters (A ∷ Γ) = cons Later (laters Γ)

    ▷ˢ : ∀{Γ}{ts : Times Γ}
       → Setˢ Γ ts
         -----------------
       → Setˢ Γ (laters Γ)

The "and" operator, `P ×ˢ Q` is categorized as `Later` for a variable
only if both `P` and `Q` are `Later` for that variable. Otherwise it
is `Now`.  We use the following function to make this choice:

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

    var-now : ∀ (Γ : Context) → ∀{A} → (x : Γ ∋ A) → Times Γ
    var-now (B ∷ Γ) zeroˢ = cons Now (laters Γ)
    var-now (B ∷ Γ) (sucˢ x) = cons Later (var-now Γ x)

    _∈_ : ∀{Γ}{A}
       → A
       → (x : Γ ∋ A)
       → Setˢ Γ (var-now Γ x)
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
which says that if `P` and `Q` are equivalent, then a proof of `P` gives
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
a modal logic, and it took some getting use to!


## Defining a Logical Relation for Type Safety

With the Step-indexed Logic in hand, we are ready to define a logical
relation for type safety. The two predicates ℰ and 𝒱 are mutually
recursive, so we combine them into a single recursive predicate named
`ℰ⊎𝒱` that takes a sum type, where the left side is for ℰ and the
right side is for 𝒱. We shall define `ℰ⊎𝒱` by an application of
`μᵒ`, so we first need to define the non-recursive version of
`ℰ⊎𝒱`, which we call `pre-ℰ⊎𝒱`, defined below. It simply dispatches to
the non-recursive `pre-ℰ` and `pre-ℰ` which we define next.

```
ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Type × Term) ⊎ (Type × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

pre-ℰ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (A , V)) = pre-𝒱 A V
pre-ℰ⊎𝒱 (inj₂ (A , M)) = pre-ℰ A M
```

To improve the readability of our definitions, we define the following
notation for recursive applications of the ℰ and 𝒱 predicates.

```
ℰˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A ⟧ M = (inj₂ (A , M)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A ⟧ V = (inj₁ (A , V)) ∈ zeroˢ
```

The definition of `pre-ℰ` and `pre-𝒱` below are of similar form to the
explicitly step-indexed definition of ℰ and 𝒱 above, however the
parameter `k` is gone and all of the logical connectives have a
superscript `s`, indicating that we're building a `Setˢ`.  Also,
note that all the uses of `ℰˢ` and `𝒱ˢ` are guarded by the later
operator `▷ˢ`. Finally, in the definition of `pre-ℰ`, we do not use `▷ˢ
(𝒱⟦ A ⟧ M)` but instead use `pre-𝒱 A M` because we need to say in that
spot that `M` is a semantic value now, not later.

```
pre-ℰ A M = (pre-𝒱 A M ⊎ˢ (reducible M)ˢ ⊎ˢ (Blame M)ˢ)
             ×ˢ (∀ˢ[ N ] (M —→ N)ˢ →ˢ ▷ˢ (ℰˢ⟦ A ⟧ N))
pre-𝒱 ★ (V ⟨ G !⟩ )      = (Value V)ˢ ×ˢ ▷ˢ (𝒱ˢ⟦ gnd⇒ty G ⟧ V)
pre-𝒱 ($ₜ ι) ($ c)        = (ι ≡ typeof c)ˢ
pre-𝒱 (A ⇒ B) (ƛ N)      = ∀ˢ[ W ] ▷ˢ (𝒱ˢ⟦ A ⟧ W) →ˢ ▷ˢ (ℰˢ⟦ B ⟧ (N [ W ]))
pre-𝒱 A M                = ⊥ ˢ
```

We define ℰ and 𝒱 by creating a recursive predicate (apply `μᵒ` to
`ℰ⊎𝒱`) and then apply it to an argument injected with either `inj₁`
for 𝒱 or `inj₂` for ℰ.

```
ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X

ℰ⟦_⟧ : Type → Term → Setᵒ
ℰ⟦ A ⟧ M = ℰ⊎𝒱 (inj₂ (A , M))

𝒱⟦_⟧ : Type → Term → Setᵒ
𝒱⟦ A ⟧ V = ℰ⊎𝒱 (inj₁ (A , V))
```

To succinctly talk about the two aspects of ℰ, we define semantic
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
  ℰ⟦ A ⟧ M                                                    ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 (inj₂ (A , M))              ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 (inj₂ (A , M)) ⟩
  # (pre-ℰ⊎𝒱 (inj₂ (A , M))) (ℰ⊎𝒱 , ttᵖ)
             ⩦⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (A , M))))
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

Similarly, we can derive the expected equations for 𝒱.

```
𝒱-base : ∀{ι}{c : Lit} → (𝒱⟦ $ₜ ι ⟧ ($ c)) ≡ᵒ (ι ≡ typeof c)ᵒ
𝒱-base = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

𝒱-dyn : ∀{G}{V} → 𝒱⟦ ★ ⟧ (V ⟨ G !⟩) ≡ᵒ ((Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G ⟧ V))
𝒱-dyn {G}{V} =
   let X = (inj₁ (★ , V ⟨ G !⟩)) in
   𝒱⟦ ★ ⟧ (V ⟨ G !⟩)                              ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                          ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                     ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G ⟧ V)             ∎

𝒱-fun : ∀{A B}{N}
   → 𝒱⟦ A ⇒ B ⟧ (ƛ N)
      ≡ᵒ (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
𝒱-fun {A}{B}{N} =
   let X = (inj₁ (A ⇒ B , ƛ N)) in
   𝒱⟦ A ⇒ B ⟧ (ƛ N)                                         ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                            ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                               ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))   ∎
```

We have defined `𝒱` such that it only accepts terms that are syntactic
values. (We included `Value V` in the case for `★` of `pre-𝒱`.)

```
𝒱⇒Value : ∀ {k} A M
   → # (𝒱⟦ A ⟧ M) (suc k)
     ---------------------
   → Value M
𝒱⇒Value ★ (M ⟨ G !⟩) (v , _) = v 〈 G 〉
𝒱⇒Value ($ₜ ι) ($ c) 𝒱M = $̬ c
𝒱⇒Value (A ⇒ B) (ƛ N) 𝒱M = ƛ̬ N
```

A value `V` in 𝒱 is also in ℰ. The definition of `progress` includes
values, and to prove preservation we not that a value is irreducible.

```
𝒱⇒ℰ : ∀{A}{𝒫}{V}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⟧ V
     ---------------
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ V
𝒱⇒ℰ {A}{𝒫}{V} 𝒫⊢𝒱V = ℰ-intro prog pres
    where
    prog = inj₁ᵒ 𝒫⊢𝒱V
    pres = Λᵒ[ N ] →ᵒI
            (Sᵒ⊢ᵒ λ V—→N →
             ⊢ᵒ-sucP 𝒫⊢𝒱V λ 𝒱V →
             ⊥-elim (value-irreducible (𝒱⇒Value A V 𝒱V ) V—→N))
```

## Semantic Type Safety

The `ℰ` predicate applies to closed terms, that is, terms without any
free variables, such as a whole program. However, we'll need a notion
of semantic type safety that also includes open terms. The standard
way to define safety for an open term `M` is to substitute the free
variables for values and then use `ℰ`. That is, we apply a
substitution `γ` to `M` where all the values in `γ` must be
semantically well typed. The following `𝓖` expresses this contraint on
`γ`.

```
𝓖⟦_⟧ : (Γ : List Type) → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ = []
𝓖⟦ A ∷ Γ ⟧ σ = (𝒱⟦ A ⟧ (σ 0)) ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x))
```

A term `M` is semantically well typed at `A` in context `Γ` if, 
for any well-typed substitution `γ`, we have `ℰ⟦ A ⟧ (⟪ γ ⟫ M)`.

```
_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
```

## The Fundamental Lemma via Compatibility Lemmas

The main lemma on our way to proving type safety is the Fundamental
Lemma, which states that well-typed programs are semantically type
safe. That is, well-typed programs behave as expected according to
their types.

    fundamental : ∀ {Γ A} → (M : Term)
      → Γ ⊢ M ⦂ A
        ----------
      → Γ ⊨ M ⦂ A

The proof of `fundamental` is by induction on the typing derivation,
with each case dispatching to a compatibility lemma.

The compatibility lemma for number literals is proved by show that
`$ (Num n)` is in `𝒱⟦ $ₜ ′ℕ ⟧` via the definition of `𝒱` and then
apply the `𝒱⇒ℰ` lemma.

```
compatible-nat : ∀{Γ}{n : ℕ}
    --------------------------
   → Γ ⊨ $ (Num n) ⦂ ($ₜ ′ℕ)
compatible-nat {Γ}{n} γ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))
```

The compability lemma for Boolean literals is the same.

```
compatible-bool : ∀{Γ}{b : 𝔹}
    ---------------------------
   → Γ ⊨ ($ (Bool b)) ⦂ ($ₜ ′𝔹)
compatible-bool {Γ}{b} γ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))
```

The compatibility lemma for the `blame` term is similar to the `𝒱⇒ℰ`
lemma in that `blame` is one of the alternatives allowed in `progress`
and `blame` is irreducible.

```
ℰ-blame : ∀{𝒫}{A} → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ blame
ℰ-blame {𝒫}{A} = ℰ-intro prog pres
    where
    prog = inj₂ᵒ (inj₂ᵒ (constᵒI isBlame))
    pres = Λᵒ[ N ] →ᵒI (Sᵒ⊢ᵒ λ blame→ → ⊥-elim (blame-irreducible blame→))

compatible-blame : ∀{Γ}{A}
     -------------
   → Γ ⊨ blame ⦂ A
compatible-blame {Γ}{A} γ = ℰ-blame
```

The compatibility lemma for variables makes use of the premise that
the values in the environment are semantically well typed.
The following lemma proves that for any variable `y` in `Γ`,
`γ` in `𝓖⟦ Γ ⟧` imples that `γ y` in `𝒱⟦ A ⟧`.

```
lookup-𝓖 : (Γ : List Type) → (γ : Subst)
  → ∀ {A}{y} → (Γ ∋ y ⦂ A)
  → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (γ y)
lookup-𝓖 (B ∷ Γ) γ {A} {zero} refl = Zᵒ
lookup-𝓖 (B ∷ Γ) γ {A} {suc y} ∋y =
    Sᵒ (lookup-𝓖 Γ (λ x → γ (suc x)) ∋y) 
```

Once we have `γ y` in `𝒱⟦ A ⟧`, we conclude by applying the `𝒱⇒ℰ`
lemma. (The `sub-var` lemma just says that `⟪ γ ⟫ (` x) ≡ γ x`.)

```
compatibility-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatibility-var {Γ}{A}{x} ∋x γ rewrite sub-var γ x = 𝒱⇒ℰ (lookup-𝓖 Γ γ ∋x)
```

The next compatibility lemma is for lambda abstraction.  To show that
`ƛ N` is in `ℰ⟦A ⇒ B⟧` we shows that `ƛ N` is in `𝒱⟦A ⇒ B⟧`.  According
to that definition, we need to show that for any argument value `W` in
`𝒱⟦ A ⟧` (later), we have `(⟪ ext γ ⟫ N) [ W ]` in `ℰ⟦ B ⟧` (also later).  But
that follows almost directly from the premise that `N` is semantically
type safe. From that premise we have

    ▷ᵒ ℰ ⟦ B ⟧ (⟪ W • γ ⟫ N)

and the Abstract Binding Tree library provides rewrites for the
following equation

    ⟪ W • γ ⟫ N = (⟪ ext γ ⟫ N) [ W ]

which gives us what we need:

    ▷ᵒ ℰ ⟦ B ⟧ (⟪ ext γ ⟫ N) [ W ]

Here's all the details in Agda:
```
compatible-lambda : ∀{Γ}{A}{B}{N}
   → (A ∷ Γ) ⊨ N ⦂ B
     -------------------
   → Γ ⊨ (ƛ N) ⦂ (A ⇒ B)
compatible-lambda {Γ}{A}{B}{N} ⊨N γ = 𝒱⇒ℰ ⊢𝒱λN
 where
 ⊢𝒱λN : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ (ƛ (⟪ ext γ ⟫ N))
 ⊢𝒱λN = (substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] →ᵒI ▷𝓔N[W]))
  where
  ▷𝓔N[W] : ∀{W} → ▷ᵒ 𝒱⟦ A ⟧ W ∷ 𝓖⟦ Γ ⟧ γ  ⊢ᵒ  ▷ᵒ ℰ⟦ B ⟧ ((⟪ ext γ ⟫ N) [ W ])
  ▷𝓔N[W] {W} = appᵒ (Sᵒ (▷→ (monoᵒ (→ᵒI (⊨N (W • γ)))))) Zᵒ
```

The next few compatibility lemmas, for application and casts, all
involve reasoning about the reduction of subexpressions.  Instead of
duplicating this reasoning, the standard approach is to put that
reasoning in the "bind" lemma, which we discuss next.

## Interlude: the "Bind" Lemma

The bind lemma says that if we have an expression `N` with a
subexpression `M` (so `N` is equal to plugging `M` into
an appropriate frame `F`, i.e. `N = F ⟦ M ⟧`), if
`M` is semantically safe, then to prove `ℰ⟦ A ⟧ (F ⟦ M ⟧)`
it suffices to prove that `ℰ⟦ A ⟧ (F ⟦ V ⟧))`
for some semantically safe value `V` that `M` reduced to.

    ℰ-bind : ∀{𝒫}{A}{B}{F}{M}
       → 𝒫 ⊢ᵒ ℰ⟦ B ⟧ M
       → 𝒫 ⊢ᵒ (∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧))
         ----------------------------------------------------------
       → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)

In the title of the blog post I alluded to 1 hard lemma.  This one's
it. Here's the proof. I'm too tired to explain it now!  But perhaps
the most interesting part of the proof is that it employs the `lobᵒ`
rule of SIL.

```

ℰ-f-cont : Type → Type → Frame → Term → Setᵒ
ℰ-f-cont A B F M = ∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)

ℰ-fp : Type → Type → Frame → Term → Setᵒ
ℰ-fp A B F M = ℰ⟦ B ⟧ M →ᵒ ℰ-f-cont A B F M →ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)

ℰ-bind-prop : Type → Type → Frame → Setᵒ
ℰ-bind-prop A B F = ∀ᵒ[ M ] ℰ-fp A B F M

frame-prop-lemma : ∀{𝒫}{A}{B}{M}{F}
   → 𝒫 ⊢ᵒ ▷ᵒ ℰ-bind-prop A B F
   → 𝒫 ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M
   → 𝒫 ⊢ᵒ ▷ᵒ ℰ-f-cont A B F M
   → 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M ⟧))
frame-prop-lemma{𝒫}{A}{B}{M}{F} IH ℰM V→FV =
  appᵒ (▷→ (appᵒ (▷→ (instᵒ (▷∀{P = λ M → ℰ-fp A B F M} IH) M)) ℰM)) V→FV

ℰ-f-cont-lemma : ∀{𝒫}{A}{B}{F}{M}{M′}
   → M —→ M′
   → 𝒫 ⊢ᵒ ℰ-f-cont A B F M
     -----------------------
   → 𝒫 ⊢ᵒ ℰ-f-cont A B F M′
ℰ-f-cont-lemma {𝒫}{A}{B}{F}{M}{M′} M→M′ ℰ-cont =
   Λᵒ[ V ]
    let M→V→ℰFV : 𝒫 ⊢ᵒ (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
        M→V→ℰFV = instᵒ ℰ-cont V in
    let M′→V→ℰFV : 𝒱⟦ B ⟧ V ∷ (M′ —↠ V)ᵒ ∷ 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
        M′→V→ℰFV = ⊢ᵒ-intro λ{ zero (𝒱Vn , M′→Vn , ⊨𝒫n) →
                                tz (ℰ⟦ A ⟧ (F ⟦ V ⟧))
                             ; (suc n) (𝒱Vsn , M′→Vsn , ⊨𝒫sn) →
                               ⊢ᵒ-elim M→V→ℰFV (suc n) ⊨𝒫sn (suc n) ≤-refl
                               (M —→⟨ M→M′ ⟩ M′→Vsn)
                               (suc n) ≤-refl 𝒱Vsn } in
    →ᵒI (→ᵒI M′→V→ℰFV)

open import rewriting.examples.CastDeterministic
  using (frame-inv2; deterministic)

ℰ-bind-aux : ∀{𝒫}{A}{B}{F} → 𝒫 ⊢ᵒ ℰ-bind-prop A B F
ℰ-bind-aux {𝒫}{A}{B}{F} = lobᵒ Goal
 where     
 Goal : ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫 ⊢ᵒ ℰ-bind-prop A B F
 Goal = Λᵒ[ M ] →ᵒI (→ᵒI Goal′)
  where
  Goal′ : ∀{M}
     → (ℰ-f-cont A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫
        ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
  Goal′{M} =
   let ⊢ℰM : 𝒫′ ⊢ᵒ ℰ⟦ B ⟧ M
       ⊢ℰM = Sᵒ Zᵒ in
   case3ᵒ (ℰ-progress ⊢ℰM) Mval Mred Mblame
   where
   𝒫′ = (ℰ-f-cont A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫

   Mval : 𝒱⟦ B ⟧ M ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mval =
     let ⊢𝒱M : 𝒱⟦ B ⟧ M ∷ 𝒫′ ⊢ᵒ 𝒱⟦ B ⟧ M
         ⊢𝒱M = Zᵒ in
     let ℰcontFM : 𝒱⟦ B ⟧ M ∷ 𝒫′ ⊢ᵒ ℰ-f-cont A B F M
         ℰcontFM = Sᵒ Zᵒ in
     let Cont = λ V → (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧) in
     appᵒ (appᵒ (instᵒ{P = Cont} ℰcontFM M) (constᵒI (M END))) ⊢𝒱M

   Mred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mred = ℰ-intro progressMred
         (Sᵒ⊢ᵒ λ redM → Λᵒ[ N ] →ᵒI (Sᵒ⊢ᵒ λ FM→N → (redM⇒▷ℰN redM FM→N)))
    where
    progressMred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMred =
       let redFM : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
           redFM = Sᵒ→Tᵒ⇒⊢ᵒ Zᵒ λ {(M′ , M→M′) → _ , (ξ F M→M′)} in
       inj₂ᵒ (inj₁ᵒ redFM)

    redM⇒▷ℰN : ∀{N} → reducible M → (F ⟦ M ⟧ —→ N)
       → 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
    redM⇒▷ℰN {N} rM FM→N =
         let finv = frame-inv2{M}{N}{F} rM FM→N in
         let M′ = proj₁ finv in
         let M→M′ = proj₁ (proj₂ finv) in
         let N≡ = proj₂ (proj₂ finv) in

         let IH : 𝒫′ ⊢ᵒ ▷ᵒ ℰ-bind-prop A B F
             IH = Sᵒ (Sᵒ Zᵒ) in
         let ℰM : 𝒫′ ⊢ᵒ ℰ⟦ B ⟧ M
             ℰM = Sᵒ Zᵒ in
         let ▷ℰM′ : 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M′
             ▷ℰM′ = appᵒ (instᵒ{P = λ N → (M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)}
                           (ℰ-preservation ℰM) M′)
                         (constᵒI M→M′) in
         let M→V→𝒱V→ℰFV : 𝒫′ ⊢ᵒ ℰ-f-cont A B F M
             M→V→𝒱V→ℰFV = Zᵒ in
         let M′→V→𝒱V→ℰFV : 𝒫′ ⊢ᵒ ℰ-f-cont A B F M′
             M′→V→𝒱V→ℰFV = ℰ-f-cont-lemma{𝒫′}{A}{B} M→M′ M→V→𝒱V→ℰFV in
         let ▷ℰFM′ : 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M′ ⟧))
             ▷ℰFM′ = frame-prop-lemma IH ▷ℰM′ (monoᵒ M′→V→𝒱V→ℰFV) in
         subst (λ N → 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym N≡) ▷ℰFM′

   Mblame : (Blame M)ᵒ ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mblame = ℰ-intro progressMblame
            (Sᵒ⊢ᵒ λ blameM → Λᵒ[ N ]
               →ᵒI (Sᵒ⊢ᵒ λ FM→N → blameM⇒▷ℰN blameM FM→N))
    where
    progressMblame : (Blame M)ᵒ ∷ 𝒫′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMblame =
       let redFM : (Blame M)ᵒ ∷ 𝒫′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
           redFM = Sᵒ→Tᵒ⇒⊢ᵒ Zᵒ λ {isBlame → _ , (ξ-blame F)} in
       inj₂ᵒ (inj₁ᵒ redFM)

    blameM⇒▷ℰN : ∀{N} → Blame M → (F ⟦ M ⟧ —→ N)
       → 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
    blameM⇒▷ℰN {N} isBlame FM→N =
        let eq = blame-frame FM→N in
        subst (λ N → 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym eq) (monoᵒ ℰ-blame)

ℰ-bind : ∀{𝒫}{A}{B}{F}{M}
   → 𝒫 ⊢ᵒ ℰ⟦ B ⟧ M
   → 𝒫 ⊢ᵒ (∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧))
     ----------------------------------------------------------
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
ℰ-bind {𝒫}{A}{B}{F}{M} ⊢ℰM ⊢𝒱V→ℰFV =
  appᵒ (appᵒ (instᵒ{𝒫}{P = λ M → ℰ-fp A B F M} ℰ-bind-aux M) ⊢ℰM) ⊢𝒱V→ℰFV
```

## More Compatibility Lemmas

The next compatibility lemma to proof is the one for function
application.  For that we'll need the following elimination lemma for
a value `V` in `𝒱⟦ A ⇒ B ⟧`.

```
safe-body : List Setᵒ → Term → Type → Type → Set
safe-body 𝒫 N A B = ∀{W} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))

𝒱-fun-elim : ∀{𝒫}{A}{B}{V}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
   → (∀ N → V ≡ ƛ N → safe-body 𝒫 N A B → 𝒫 ⊢ᵒ R)
    ------------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-fun-elim {𝒫}{A}{B}{V}{R} ⊢𝒱V cont =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → G {V} 𝒱Vsn ⊢𝒱V cont}
  where
  G : ∀{V}{n}
     → # (𝒱⟦ A ⇒ B ⟧ V) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
     → (∀ N → V ≡ ƛ N → safe-body 𝒫 N A B → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G{ƛ N}{n} 𝒱V ⊢𝒱V cont = cont N refl λ {W} →
      instᵒ{P = λ W → (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))}
                 (substᵒ 𝒱-fun ⊢𝒱V) W
```

The proof of compatibility for application begins with two uses of the
`ℰ-bind` lemma, once for subexpression `L` and again for `M`.  So we
obtain that `L` reduces to value `V` and `M` reduces to `W` and that
`𝒱⟦ A ⇒ B ⟧ V` and `𝒱⟦ A ⟧ W`.  At this point, our goal is to show
that `ℰ⟦ B ⟧ (V · W)`.  Next we use the elimination lemma on `𝒱⟦ A ⇒ B
⟧ V` which tells us that `V` is a lambda abstraction `ƛ N` with a
semantically safe body `N`.  We thus obtain the `progress` part of
`ℰ⟦ B ⟧ (V · W)` because `(ƛ N) · W —→ N [ W ]`.  For the preservation
part, we need to show that `ℰ⟦ B ⟧ (N [ W ])`, but that follows from
`𝒱⟦ A ⟧ W` and that `N` is a semantically safe body.

```
compatible-app : ∀{Γ}{A}{B}{L}{M}
   → Γ ⊨ L ⦂ (A ⇒ B)
   → Γ ⊨ M ⦂ A
     -------------------
   → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M γ = ⊢ℰLM
 where
 ⊢ℰLM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ B ⟧ (⟪ γ ⟫ (L · M))
 ⊢ℰLM = ℰ-bind {F = □· (⟪ γ ⟫ M)} (⊨L γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVM))
  where
  𝓟₁ = λ V → 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVM : ∀{V} → 𝓟₁ V ⊢ᵒ ℰ⟦ B ⟧ (V · ⟪ γ ⟫ M)
  ⊢ℰVM {V} = sucP⊢ᵒQ λ 𝒱Vsn →
       let v = 𝒱⇒Value (A ⇒ B) V 𝒱Vsn in
       let 𝓟₁⊢ℰM : 𝓟₁ V ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
           𝓟₁⊢ℰM = Sᵒ (Sᵒ (⊨M γ)) in
       ℰ-bind {F = v ·□} 𝓟₁⊢ℰM (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVW))
   where
   𝓟₂ = λ V W → 𝒱⟦ A ⟧ W ∷ (⟪ γ ⟫ M —↠ W)ᵒ ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ
                 ∷ 𝓖⟦ Γ ⟧ γ
   ⊢ℰVW : ∀{V W} → 𝓟₂ V W ⊢ᵒ ℰ⟦ B ⟧ (V · W)
   ⊢ℰVW {V}{W} =
     let ⊢𝒱V : 𝓟₂ V W ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
         ⊢𝒱V = Sᵒ (Sᵒ Zᵒ) in
     let ⊢𝒱W : 𝓟₂ V W ⊢ᵒ 𝒱⟦ A ⟧ W
         ⊢𝒱W = Zᵒ in
     ⊢ᵒ-sucP ⊢𝒱W λ 𝒱Wsn →
     let w = 𝒱⇒Value A W 𝒱Wsn in
     𝒱-fun-elim ⊢𝒱V λ {N′ refl 𝒱W→ℰNW →
     let prog : 𝓟₂ (ƛ N′) W ⊢ᵒ progress B (ƛ N′ · W)
         prog = (inj₂ᵒ (inj₁ᵒ (constᵒI (_ , (β w))))) in
     let pres : 𝓟₂ (ƛ N′) W ⊢ᵒ preservation B (ƛ N′ · W)
         pres = Λᵒ[ N ] →ᵒI (Sᵒ⊢ᵒ λ {r →
                let ⊢▷ℰN′W = appᵒ 𝒱W→ℰNW (monoᵒ ⊢𝒱W) in
                let eq = deterministic r (β w) in
                subst (λ N → 𝓟₂ (ƛ N′) W ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ N) (sym eq) ⊢▷ℰN′W}) in
     ℰ-intro prog pres
     }
```

The compability lemma for an injection cast also begins with applying
the bind lemma to subexpression `M`, taking us from `ℰ⟦ gnd⇒ty G ⟧ M`
to `𝒱⟦ gnd⇒ty G ⟧ V`. This also gives us that `V` is a syntactic
value via `𝒱⇒Value`. So we have `𝒱⟦ ★ ⟧ (V ⟨ G !⟩)` and then
conclude using `𝒱⇒ℰ`.

```
compatible-inject : ∀{Γ}{G}{M}
  → Γ ⊨ M ⦂ gnd⇒ty G
    --------------------
  → Γ ⊨ M ⟨ G !⟩ ⦂ ★
compatible-inject {Γ}{G}{M} ⊨M γ = ℰMg!
 where
 ℰMg! : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ ★ ⟧ ((⟪ γ ⟫ M) ⟨ G !⟩)
 ℰMg! = ℰ-bind {F = □⟨ G !⟩} (⊨M γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVg!))
  where
  𝓟₁ = λ V → 𝒱⟦ gnd⇒ty G ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVg! : ∀{V} → 𝓟₁ V ⊢ᵒ ℰ⟦ ★ ⟧ (V ⟨ G !⟩)
  ⊢ℰVg!{V} =
   ⊢ᵒ-sucP Zᵒ λ 𝒱Vsn →
   let v = 𝒱⇒Value (gnd⇒ty G) V 𝒱Vsn in
   𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-dyn) (constᵒI v ,ᵒ monoᵒ Zᵒ))
```

The last compatibility lemma is for a projection cast.
Here we also need an elimination lemma, this time for
a value `V` of type `★`.

```
𝒱-dyn-elim : ∀{𝒫}{V}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ ⟧ V
   → (∀ W G → V ≡ W ⟨ G !⟩
             → 𝒫 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G ⟧ W))
             → 𝒫 ⊢ᵒ R)
     ----------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-dyn-elim {𝒫}{V}{R} ⊢𝒱V cont =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → G 𝒱Vsn ⊢𝒱V cont }
  where
  G : ∀{V}{n}
      → # (𝒱⟦ ★ ⟧ V) (suc n)
      → 𝒫 ⊢ᵒ 𝒱⟦ ★ ⟧ V
      → (∀ W G → V ≡ W ⟨ G !⟩
               → 𝒫 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G ⟧ W))
               → 𝒫 ⊢ᵒ R)
      → 𝒫 ⊢ᵒ R
  G {W ⟨ G !⟩}{n} 𝒱Vsn ⊢𝒱V cont
      with 𝒱⇒Value ★ (W ⟨ G !⟩) 𝒱Vsn
  ... | w 〈 _ 〉 =
      let ⊢▷𝒱W = proj₂ᵒ (substᵒ (𝒱-dyn{V = W}) ⊢𝒱V) in
      cont W _ refl (constᵒI w ,ᵒ ⊢▷𝒱W)
```

The compatibility lemma for a projection `M ⟨ H ?⟩` begins by using
`ℰ-bind` on the subexpression `M` to obtain a value `V` where
`⟪ γ ⟫ M —↠ V` and `𝒱⟦ ★ ⟧ V`. We then apply lemma `𝒱-dyn-elim`
to compose `V` into an injection `W ⟨ G !⟩` of a value `W`
where `▷ᵒ 𝒱⟦ G ⟧ W`. We need to show `ℰ⟦ H ⟧ (W ⟨ G !⟩ ⟨ H ?⟩)`.
The progress part comes from showing that it reduces to `W`
(if `G ≡ H`) or to `blame`. The preservation part is from
`▷ᵒ 𝒱⟦ G ⟧ W` (in the `G ≡ H` case) or because `ℰ⟦ H ⟧ blame`.

```
compatible-project : ∀{Γ}{H}{M}
  → Γ ⊨ M ⦂ ★
    -----------------------------
  → Γ ⊨ M ⟨ H ?⟩ ⦂ gnd⇒ty H
compatible-project {Γ}{H}{M} ⊨M γ = ℰMh?
 where
 ℰMh? : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ gnd⇒ty H ⟧ ((⟪ γ ⟫ M) ⟨ H ?⟩)
 ℰMh? = ℰ-bind {F = □⟨ H ?⟩} (⊨M γ) (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVh?))
  where
  𝓟₁ = λ V → 𝒱⟦ ★ ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVh? : ∀{V} → 𝓟₁ V ⊢ᵒ ℰ⟦ gnd⇒ty H ⟧ (V ⟨ H ?⟩)
  ⊢ℰVh?{V} =
   let ⊢𝒱V : 𝓟₁ V ⊢ᵒ 𝒱⟦ ★ ⟧ V
       ⊢𝒱V = Zᵒ in
   𝒱-dyn-elim ⊢𝒱V λ { W G refl ⊢w×▷𝒱W →
   let ⊢w = proj₁ᵒ ⊢w×▷𝒱W in
   let ▷𝒱W = proj₂ᵒ ⊢w×▷𝒱W in
   ⊢ᵒ-sucP ⊢w λ{n} w →
   let prog : 𝓟₁ (W ⟨ G !⟩) ⊢ᵒ progress (gnd⇒ty H) ((W ⟨ G !⟩) ⟨ H ?⟩)
       prog = inj₂ᵒ (inj₁ᵒ (constᵒI (reduce-inj-proj w))) in
   let pres : 𝓟₁ (W ⟨ G !⟩) ⊢ᵒ preservation (gnd⇒ty H)((W ⟨ G !⟩) ⟨ H ?⟩)
       pres = Λᵒ[ N ] →ᵒI (Sᵒ⊢ᵒ λ r → Goal r w ▷𝒱W) in
   ℰ-intro prog pres
   }
    where
    reduce-inj-proj : ∀{G}{H}{W}
       → Value W
       → reducible ((W ⟨ G !⟩) ⟨ H ?⟩)
    reduce-inj-proj {G} {H} {W} w
        with G ≡ᵍ H
    ... | yes refl = W , (collapse w  refl)
    ... | no neq = blame , (collide w neq refl)
    
    Goal : ∀{W}{G}{H}{N}
       → (W ⟨ G !⟩ ⟨ H ?⟩) —→ N
       → Value W
       → 𝓟₁ (W ⟨ G !⟩) ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G ⟧ W
       → 𝓟₁ (W ⟨ G !⟩) ⊢ᵒ ▷ᵒ ℰ⟦ gnd⇒ty H ⟧ N
    Goal (ξξ □⟨ H ?⟩ refl refl r) w ▷𝒱W =
        ⊥-elim (value-irreducible (w 〈 _ 〉) r)
    Goal {W} (ξξ-blame □⟨ H ?⟩ ())
    Goal {W}{G}{G}{W} (collapse{H} w′ refl) w ▷𝒱W =
       ▷→▷ ▷𝒱W (→ᵒI (𝒱⇒ℰ Zᵒ))
    Goal {W} (collide x x₁ x₂) w ▷𝒱W = monoᵒ ℰ-blame
```

## Fundamental Lemma

The Fundamental Lemma states that a syntactically well-typed term is
also a semantically well-typed term. Or given how we have defined the
logical relations, it means that a well-typed term satisfies progress
and preservation.

```
fundamental : ∀ {Γ A} → (M : Term)
  → Γ ⊢ M ⦂ A
    ----------
  → Γ ⊨ M ⦂ A
fundamental {Γ} {A} .(` _) (⊢` ∋x) =
    compatibility-var ∋x
fundamental {Γ} {.($ₜ ′ℕ)} .($ (Num _)) (⊢$ (Num n)) =
    compatible-nat
fundamental {Γ} {.($ₜ ′𝔹)} .($ (Bool _)) (⊢$ (Bool b)) =
    compatible-bool
fundamental {Γ} {A} (L · M) (⊢· ⊢L ⊢M) =
    compatible-app{L = L}{M} (fundamental L ⊢L) (fundamental M ⊢M)
fundamental {Γ} {.(_ ⇒ _)} (ƛ N) (⊢ƛ ⊢N) =
    compatible-lambda {N = N} (fundamental N ⊢N)
fundamental {Γ} {.★} (M ⟨ G !⟩) (⊢⟨!⟩ ⊢M) =
    compatible-inject {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} (M ⟨ H ?⟩) (⊢⟨?⟩ ⊢M H) =
    compatible-project {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} .blame ⊢blame = compatible-blame
```

## Proof of Type Safety

For the Type Safety theorem, we need to consider multi-step reduction.
So we first prove the following lemma which states that if
`M —↠ N` and `M` is in `ℰ⟦ A⟧`, then `N` satisfies progress.
The lemma is by induction on the multi-step reduction.

```
sem-type-safety : ∀ {A} → (M N : Term)
  → (r : M —↠ N)
  → # (ℰ⟦ A ⟧ M) (suc (len r))
    ---------------------------------------------
  → Value N  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame   
sem-type-safety {A} M .M (.M END) (inj₁ 𝒱M , presM) =
    inj₁ (𝒱⇒Value A M 𝒱M)
sem-type-safety {A} M .M (.M END) (inj₂ (inj₁ r) , presM) =
    inj₂ (inj₁ r)
sem-type-safety {A} M .M (.M END) (inj₂ (inj₂ isBlame) , presM) =
    inj₂ (inj₂ refl)
sem-type-safety {A} M N (_—→⟨_⟩_ .M {M′} M→M′ M′→N) (_ , presM) =
    let ℰM′ : # (ℰ⟦ A ⟧ M′) (suc (len M′→N))
        ℰM′ = presM M′ (suc (suc (len M′→N))) ≤-refl M→M′ in
    sem-type-safety M′ N M′→N ℰM′
```

The Type Safety theorem is then a corollary of the Fundamental Lemma
together with the above lemma regarding multi-step reduction.

```
type-safety : ∀ {A} → (M N : Term)
  → [] ⊢ M ⦂ A
  → M —↠ N
    ---------------------------------------------
  → Value N  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame   
type-safety M N ⊢M M→N =
  let ℰM = ⊢ᵒ-elim ((fundamental M ⊢M) id) (suc (len M→N)) tt in
  sem-type-safety M N M→N ℰM 
```
