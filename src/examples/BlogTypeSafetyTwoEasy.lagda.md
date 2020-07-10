# Type Safety in Two Easy Lemmas

Wow, it's been seven years already since I blogged about [Type Safety
in Three Easy
Lemmas](http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html). Time
flies! In that blog post I showed how to prove type safety of a simple
language whose semantics was specified by a definitional interpreter.
I still like that approach, and it has proved useful to other
researchers on much larger projects such as the verified
[CakeML](https://cakeml.org/) compiler.

In the meantime, I've learned about the
[Agda](https://agda.readthedocs.io/en/v2.6.1/index.html) proof
assistant thanks to the book [Programming Language Foundations in
Agda](https://plfa.github.io/) (PLFA) and I've become excited by Agda's
abstraction mechanisms that enable proof reuse.  I'm working on an
Agda library for reusable programming language metatheory, called
[abstract-binding-trees](https://github.com/jsiek/abstract-binding-trees).
As the name suggests, it represents abstract syntax trees using Robert
Harper's notion of abstract *binding* trees (ABT), that is, trees that
are enhanced to know about variable bindings and variable occurrences
(See the book [Practical Foundations for Programming Languages](https://www.cs.cmu.edu/~rwh/pfpl/)). My library provides a
suite of useful functions on abstract binding trees, such as
substitution, and theorems about those functions. The neat thing about
these theorems is that they automatically apply to any language whose
grammar is built using abstract binding trees!

In this blog post I'll prove type safety of the simply-typed lambda
calculus (STLC) with respect to a semantic specified in the standard
way using a reduction semantics (standard for PL theory). The proof
includes just two easy lemmas: progress and preservation. Normally a
proof via progress and preservation also requires quite a few
technical lemmas about substitution, but in this case we get those
lemmas for free thanks to the `abstract-binding-trees` library.

This blog post is a literate Agda file, so the text will be
interspersed with the Agda code that defines the STLC and proves type
safety.

```
module examples.BlogTypeSafetyTwoEasy where
```

We'll be making use of the following items from the Agda standard
library.

```
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
```

## Syntax of the STLC

The `abstract-binding-trees` library provides a module named `Syntax`
that provides facilities for creating abstract binding trees.

```
open import Syntax
```

An abstract binding tree `ABT` consists of two kinds of nodes:

* Variables: A variable node is a leaf (no children) and stores the de
  Bruijn index for the variable.
  
* Operators: An operator node is tagged with the kind of operator and
  it has zero or more children, depending on the kind of operator.

The `ABT` data type is parameterized by the kinds of operators and
their signatures, which specifies things like the number of child
nodes for each kind of operator. To specify the operators, you create
a data type definition with one constructor for each kind of
operator. For the STLC the operators are lambda abstraction and
application.

```
data Op : Set where
  op-lam : Op
  op-app : Op
```

To specify the operator signatures, write a function that maps the
operators to a list of the `Sig` data type. The length of the list
says the number of children nodes and the `Sig` controls changes in
variable scoping for the child. The `Sig` data type is defined
by the `abstract-binding-trees` library as follows:

    data Sig : Set where
      ■ : Sig
      ν : Sig → Sig
      ∁ : Sig → Sig

The `ν` brings a variable into scope. The `∁` clears the scope of
the child, so that the child does not have access to the surrounding
lexical scope. The `■` terminates the changes in scope.

For the STLC, the signature function is defined as follows.

```
sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
```

With `Op` and `sig` defined, we can import the abstract binding tree
data type `ABT` from the `Syntax` library. We choose to rename it to
`Term`.

```
open Syntax.OpSig Op sig renaming (ABT to Term)
```

The raw abstract binding trees are verbose to deal with, so we use
Agda [pattern
synonyms](https://agda.readthedocs.io/en/v2.6.1/language/pattern-synonyms.html)
to obtain syntax that is closer to the pen-and-paper STLC.  We write
`ƛ N` for a lambda abstraction with body `N` and we write `L · M` for
the application of the function produces by `L` to the argument
produced by `M`.

```
pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
```

## Reduction Semantics

We define the reduction semantics for the STLC in the usual way,
with several congruence rules (the `ξ`'s) and the `β` rule for
function application. In the `β` rule, we use the substitution
function defined in the `abstract-binding-trees` library,
writing `N [ M ]` for replacing all the occurrences of de Bruijn index `0`
inside `N` with the term `M`.

```
infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M : Term}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {L M M′ : Term}
    → M —→ M′
      ---------------
    → L · M —→ L · M′

  ξ-ƛ : ∀ {N N′ : Term}
    → N —→ N′
      ---------------
    → (ƛ N) —→ (ƛ N′)

  β-ƛ : ∀ {N M : Term}
      --------------------
    → (ƛ N) · M —→ N [ M ]
```

## Type System

To make use of the theorems in the `abstract-binding-trees` library,
we need to use its approach to defining type systems.  Instead of
defining the whole type system ourselves using an Agda data type, we
instead specify 1) the types and 2) the side-conditions for each
typing rule.

For STLC, we have function types, written `A ⇒ B`, and the bottom
type `Bot`.

```
data Type : Set where
  Bot   : Type
  _⇒_   : Type → Type → Type
```

The library requires that we specify an extra side condition for the
variable rule, for which we define the following predicate `𝑉`.  We
don't really need an extra side condition, so we simply choose "true",
written `⊤` in Agda.

```
𝑉 : List Type → Var → Type → Set
𝑉 Γ x A = ⊤
```

Next we define the predicate `𝑃` that specifies the side conditions
for all the other syntax nodes. The definition of `𝑃` includes one
line for each operator. The `Vec` parameter contains the types of the
child nodes. The `BTypes` parameter contains the types of bound
variables. The last `Type` parameter is the type assigned to the
current node. So for lambda abstractions (`op-lam`),
the body has type `B`, the lambda's bound variable has type `A`, 
and we require that the type `C` of the lambda is a function
type from `A` to `B`, that is, `C ≡ A ⇒ B`. For application (`op-app`),
the function has type `C`, the argument has type `A`, and the
result type is `B` provided that `C` is a function type from `A` to `B`,
that is, `C ≡ A ⇒ B`.

```
𝑃 : (op : Op) → Vec Type (length (sig op)) → BTypes Type (sig op) → Type → Set
𝑃 op-lam (B ∷̌ []̌) ⟨ ⟨ A , tt ⟩ , tt ⟩ C = C ≡ A ⇒ B
𝑃 op-app (C ∷̌ A ∷̌ []̌) ⟨ tt , ⟨ tt , tt ⟩ ⟩ B = C ≡ A ⇒ B
```

We import the `ABTPredicate` module, using our definitions of `𝑉` and
`𝑃`, to obtain the type system for the STLC.

```
open import ABTPredicate Op sig 𝑉 𝑃
```

The raw typing rules are verbose, so we again use Agda's pattern
synonyms to create abbreviations to match the rule names in PLFA.

```
pattern ⊢` ∋x = var-p ∋x tt
pattern ⊢ƛ ⊢N eq = op-p {op = op-lam} (cons-p (bind-p (ast-p ⊢N)) nil-p) eq
pattern ⊢· ⊢L ⊢M eq = op-p {op = op-app}
                           (cons-p (ast-p ⊢L) (cons-p (ast-p ⊢M) nil-p)) eq
```

## Proof of Type Safety

We prove type safety with two lemmas: progress and preservation.


### Proof of Progress

The progress lemma states that every closed, well-typed term is either
a value (so it's finished computing) or it can reduce.

In the STLC, lambda abstractions are values.

```
data Value : Term → Set where

  V-ƛ : ∀ {N : Term}
      --------------
    → Value (ƛ N)
```

Following PLFA, we define an auxiliary data type to express the
conclusion of the progress lemma.

```
data Progress (M : Term) : Set where

  done :
      Value M
      ----------
    → Progress M

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M
```

The proof of progress is by induction on the typing derivation.  The
variable case is vacuous because `M` is closed (well typed in an empty
environment). In the lambda case, we're done. Regarding an application
`L · M`, the induction hypothesis tells us that term `L` either takes
a step or is already a lambda abstraction. In the former case,
the whole application reduces using the congruence rule `ξ-·₁`.
In the later case, the whole application reduces using β reduction.

```
progress : ∀ {M A}
  → [] ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N _)                          =  done V-ƛ
progress (⊢· ⊢L ⊢M _)
    with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ                              =  step β-ƛ
```

As you can see, to prove progress we didn't need help from the
`abstract-binding-trees` library.


### Proof of Preservation

The preservation lemma says that if a well-typed term reduces to
another term, then that term is also well typed. The proof is by
induction on the derivation of the reduction. The only interesting
case is the one for `β` reduction:

    (ƛ N) · M —→ N [ M ]

We know that

    (A ∷ Γ) ⊢ N ⦂ B
    Γ ⊢ M ⦂ A

and we need prove that

    Γ ⊢ N [ M ] ⦂ B

This requires the lemma that substitution preserves typing, which is
provided in the `SubstPreserve` module of the `abstract-binding-trees`
library.

```
open import SubstPreserve Op sig Type 𝑃 using (preserve-substitution)
```

So here is the proof of preservation.

```
preserve : ∀ {Γ M N A}
  → Γ ⊢ M ⦂ A
  → M —→ N
    ----------
  → Γ ⊢ N ⦂ A
preserve (⊢· ⊢L ⊢M refl) (ξ-·₁ L—→L′) = ⊢· (preserve ⊢L L—→L′) ⊢M refl
preserve (⊢· ⊢L ⊢M refl) (ξ-·₂ M—→M′) = ⊢· ⊢L (preserve ⊢M M—→M′) refl
preserve (⊢ƛ ⊢M refl) (ξ-ƛ M—→N) = ⊢ƛ (preserve ⊢M M—→N) refl
preserve {M = (ƛ N) · M} (⊢· (⊢ƛ ⊢N refl) ⊢M refl) β-ƛ =
    preserve-substitution N M ⊢N ⊢M
```

Thus we conclude the proof of type safety, having only needed to prove
two lemmas, progress and preservation. Thanks to the
`abstract-binding-trees` library, we did not need to prove that
substitution preserves types nor any of the many technical lemmas that
it depends on.


--  LocalWords:  definitional CakeML Agda PLFA Agda's metatheory ABT
--  LocalWords:  STLC BlogTypeSafetyTwoEasy suc proj tt Vec refl sym
--  LocalWords:  de Bruijn parameterized Sig sig OpSig ast infixl eq
--  LocalWords:  BTypes ABTPredicate SubstPreserve
