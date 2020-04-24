# Abstract Binding Trees

This is an Agda library for abstract binding trees as in Chapter 1 of
Robert Harper's book _Practical Foundations for Programming
Languages_.  An abstract binding tree (ABT) is an abstract syntax tree
that also knows about binders and variables. Thus, this library also
defines substitution on ABTs and provides theorems about substitution.
The library represents variables using de Bruijn indices.

An abstract binding tree `ABT` consists of two kinds of nodes:

* Variables: A variable node is a leaf (no children) and stores the de
  Bruijn index.
  
* Operators: An operator node is tagged with the kind of operator and
  it has zero or more children, depending on the kind of operator.

The `ABT` data type is defined in the [`Syntax`](./src/Syntax.agda)
module, which is parameterized by the kinds of operators and their
signatures, which specifies things like the number of child nodes for
each kind of operator.

To specify the operators, create a data type definition with one
constructor for each kind. Using the lambda calculus as an example,
one would define two kinds: one for lambda abstraction and another for
application.

	data Op : Set where
	  op-lam : Op
	  op-app : Op

To specify the signatures, write a function that maps your operators
to a list of natural numbers. The length of the list says the number
of children and the numbers in the list say how many variable bindings
come into scope for that child. For the lambda calculus, the signature
function would be as follows.

	sig : Op → List ℕ
	sig op-lam = 1 ∷ []
	sig op-app = 0 ∷ 0 ∷ []

A lambda abstraction has one child expression, its body, and one
variable binding comes into scope for the parameter.  Application has
two child expressions, the function and the argument. Application does
not bind any variables. Suppose we also wanted the language to include
`let` expressions. We could add another constructor to `Op`, perhaps
named `op-let`, and add the following line to the `sig` function.

	sig op-let = 0 ∷ 1 ∷ []

This says that a `let` has two child, the right-hand side and the
body.  The `let` does not bring any variable bindings into scope for
the right-hand side, but it does for the body expression.  With `Op`
and `sig` complete, we can instantiate and import the `Syntax` module.

    open import Syntax Op sig

As mentioned above, the `Syntax` module defines an `ABT` data type,
which we now look at in more detail. The constructor for variables,
the grave accent, takes one parameter, the natural number that is the
de Bruijn index for the variable. The constructor for operator nodes,
written `op ⦅ args ⦆` takes the operator and the arguments, which we
explain below.

    Var : Set
    Var = ℕ

    data Arg : ℕ → Set 
    data Args : List ℕ → Set

    data ABT : Set where
      `_ : Var → ABT
      _⦅_⦆ : (op : Op) → Args (sig op) → ABT

The `Args` data type is just a list representation, with constructors
`nil` and `cons`. However, it is parameterized by the list of numbers
that controls its length and binding structure. For each number in the
list, there is one element in the `Args`. 

    data Args where
      nil : Args []
      cons : ∀{n ls} → Arg n → Args ls → Args (n ∷ ls)

Each element of `Args` is an argument, defined by the `Arg` data type.
It is parameterized by a number that says how many variable bindings
come into scope. The `bind` constructor represents a variable binding
and decrements the number. The `ast` constructor is allowed when the
count reaches `0` and contains the abstract binding tree for the
child.

    data Arg where
      ast : ABT → Arg 0
      bind : ∀{n} → Arg n → Arg (suc n)

This use of `Args` and `Arg` makes for rather verbose notation for
abstract binding trees. Therefore we recommend that you use Agda's
pattern synonyms to introduce more concise syntax. For example, to use
`ƛ N` as the notation for lambda abstractions, you would define the
following pattern.

    pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

To use the syntax `L · M` for the application of function `L` to
argument `M`, you would write:

    infixl 7  _·_
    pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

The complete Agda code for this lambda calculus example is
in the file [`Lambda.agda`](./src/examples/Lambda.agda).


## Substitution

The library defines a type `Subst`, for _substitution_, to represent
mappings from de Bruijn indices to ABTs. The identity substitution is
`id`, it maps each variable to itself. Given some substitution `σ`,
the substitution `M • σ` maps `0` to the ABT `M` and each number `n`
greater than zero to `σ (n - 1)`.

The library defines the notation `⟦ σ ⟧ x` for applying a substitution
`σ` to a variable `x`.

For example.

    ⟦ M • L • id ⟧ 0 ≡ M
    ⟦ M • L • id ⟧ 1 ≡ L
    ⟦ M • L • id ⟧ 2 ≡ ` 0
    ⟦ M • L • id ⟧ 3 ≡ ` 1

In general, substitution replaces a variable `i` with
the ith ABT in the substitution:

    ⟦ M₀ • … • Mᵢ • … • Mⱼ • id ⟧ i ≡ Mᵢ

unless `i > j` where Mⱼ is the last ABT before the terminating `id`,
in which case the result is `i - (j + 1)`

    ⟦ M₀ • … • Mᵢ • … • Mⱼ • id ⟧ i ≡ ` (i - (j + 1))

The reason that the substitution subtracts `j + 1` from variables
greater than `j` is that we typically perform substition when removing
bindings from around a term, and so the remaining variables in the
term become closer to their bindings.

The library defines the notation `⟪ σ ⟫ M` for applying a substitution
`σ` to an ABT `M`. When `M` is a variable, we have
`⟪ σ ⟫ x ≡ ` ⟦ σ ⟧ x`. For example:

    ⟪ M • L • id ⟫ (` 0) ≡ ` (⟦ M • L • id ⟧ 0) ≡ M

Next suppose `M` is an application with variables in the operator and
argument positions.

    ⟪ M • L • id ⟫ (` 1 · ` 0) ≡ L · M

In general, substitution acts on application according to the
following equation.

    ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)

The action of substitution on lambda abstractions is more interesting
because the lambda brings a variable into scope. Consider the following
substitution.

    σ ≡ M₀ • M₁ • M₂ • … 

To transport this substitution across a lambda abstraction, we need to
do two things. First, inside the lambda, the de Bruijn index 0 is
bound to the lambda's parameter, and should not be changed by the
substitution. So the new substitution should map 0 to 0 and map the
rest of the natural numbers to M₀, M₁, M₂, ….  Second, as the
substitution σ moves over the lambda, each of the `Mᵢ` moves further
away from the bindings of their free variables. Thus, to make sure the
free variables in each `Mᵢ` still point to the appropriate bindings,
they all need to be incremented by one.  The library defines a shift
operator, written `↑ k`, that adds `k` to every free variable in an
ABT.  Putting these two actions together, the library defines a
function named `exts` that transports a substitution σ across one
lambda abstraction.

    exts σ ≡ ` 0 • ⟪ ↑ 1 ⟫ M₀ • ⟪ ↑ 1 ⟫ M₁ • …

So we have the following two equations about `exts`:

    (exts-0)     ⟦ exts σ ⟧ 0 ≡ 0
    (exts-suc)†  ⟦ exts σ ⟧ (suc x) ≡ ⟦ σ ⨟ ↑ 1 ⟧ x

where the operation `σ₁ ⨟ σ₂` composes two substitutions by applying
`σ₁` and then `σ₂`.

In general, substitution acts on lambda abstractions according
to the following equation.

    ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ exts σ ⟫ N)

Even more generally, and recalling the way in which we defined lambda
abstraction in terms of an ABT operator node, each occurrence of the
`bind` argument constructor causes substitution to introduce one
`exts` around the substitution.

Last but not least, the library introduces the notation `N [ M ]`
for the common case of substituting `M` for de Bruijn index 0
inside `N`.

    N [ M ] ≡ ⟪ M • id ⟫ N

For example, β reduction would be expressed as

    (ƛ N) M -→ N [ M ]

The following is an example of β reduction.
The inner ƛ is applied to `M`.

    (ƛ ((ƛ (` 0 · ` 1)) · M)) · L —→ (ƛ (M · ` 0)) · L


## Important Properties of Substitution

A fundamental property of (single) substitution is that two
substitutions commute with one another if the variables
are different, a property known as the Substitution Lemma
in Barendregt's The Lambda Calculus.

    M[ x := N ][ y := L ] ≡ M[ y := L ][ x := N[ y := L] ]

The Substitution Lemma is used, for example, in the proof of confluence
of the untyped lambda calculus.

Converting the Substitution Lemma to our notation and to Bruijn
indices (let `x` be index 0 and `y` be index 1), we obtain

    M[ N ][ L ] ≡ (⟪ exts (L • id) ⟫ M) [ N [ L ] ]

Generalizing the substitution by `L` to any simultaneous substitution
`σ`, we have the following theorem which is provided by the library.

    (commute-subst)†    ⟪ σ ⟫ (N [ M ]) ≡ (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ]

Setting up the infrastructure necessary to prove this theorem is a
fair bit of work, so it is nice to reuse this theorem instead of
having to prove it yourself.

The need for a slightly different property, shown below, arises in
proofs based on logical relations. A simultaneous substitution
followed by a single substitution can be combined into one
simultaneous substitution as follows.

    (exts-sub-cons)†    (⟪ exts σ ⟫ N) [ M ] ≡ ⟪ M • σ ⟫ N

The proof of this property is also provided in the library, using the
same infrastructure needed to prove `commute-subst`.


## Renaming, a special case of substitution

We refer to the special case of a substitution that maps variables to
variables as a _renaming_. In some situations, it helps to prove
lemmas about renaming on the way to proving the corresponding lemmas
about substitutions. For example, in
[`Lambda.agda`](./src/examples/Lambda.agda) we define a simple type
system for the lambda calculus and prove type safety via the standard
progress and preservation lemmas. For the preservation lemma, one must
prove that substitution preserves typing. That proof goes through more
smoothly if we first prove that renaming preserves typing.

We use much of the same syntax for renamings: `id` is the identity
renaming, `x • ρ` maps `0` to `x` and each number `n` greater than
zero to `ρ (n - 1)`. To apply a renaming `ρ` to a variable `x`, the
library defines the notation `⦉ ρ ⦊ x`. Similar to the `exts` function
for substitutions, the library defines an `ext` function that
transports a renaming across one binder, providing the following
equations.

    (ext-0)     ⦉ ext ρ ⦊ 0 ≡ 0
    (ext-suc)   ⦉ ext ρ ⦊ (suc x) ≡ suc (⦉ ρ ⦊ x)

To apply a renaming `ρ` to a term `M`, the library defines the
`rename` function. This function is quite similar to the `⟪_⟫`
function for substitutions, except that when it goes under a binder,
it uses `ext` instead of `exts`.  For example, here is the equation
for renaming applied to a lambda abstraction.

    rename ρ (ƛ N) ≡ ƛ (rename (ext ρ) N)

The library provides a function for converting a renaming to a
substitution, named `rename→subst`, and the following equation that
relates the application of a renaming to the application of the
corresponding substitution.

    (rename-subst)†     rename ρ M ≡ ⟪ rename→subst ρ ⟫ M

For example, from this equation we have

    rename (↑ 1) M ≡ ⟪ ↑ 1 ⟫ M

Combining this with the `(exts-suc)` equation, we can express `exts`
in terms of `rename`.

    (exts-suc-rename)   ⟦ exts σ ⟧ (suc x) ≡ rename (↑ 1) (⟪ σ ⟫ (` x))


## Going Deeper

You may very well have need of other equations involving
substitutions. If those equations only involve the following
substitution operators, then there is a decidable algorithm for
proving or disproving the equations.

    id
    ↑ k
    M • σ
    σ₁ ⨟ σ₂

These four operators form the σ algebra of Abadi, Cardelli, Curien,
and Levy (1991). The `exts` function is not part of the σ algebra but
it is equivalent to the following σ algebra expression.

    (exts-cons-shift)†     exts σ ≡ ` 0 • (σ ⨟ ↑ 1)

The equations of the σ algebra, adapted to ABTs, are as follows.

    (sub-head)  ⟦ M • σ ⟧ 0                   ≡ M
    (sub-tail)  ↑ 1 ⨟ (M • σ)                 ≡ σ
    (Z-shift)†  ⟦ ` 0 • ↑ 1 ⟧ x               ≡ ` x
    (sub-η)†    ⟦ (⟪ σ ⟫ (` 0)) • (↑ ⨟ σ) ⟧ x ≡ ⟦ σ ⟧ x

    (sub-op)    ⟪ σ ⟫ (op ⦅ args ⦆)     ≡ op ⦅ ⟪ σ ⟫₊ args ⦆
    (sub-nil)   ⟪ σ ⟫₊ nil             ≡ nil
    (sub-cons)  ⟪ σ ⟫₊ (cons arg args) ≡ cons (⟪ σ ⟫ₐ arg) (⟪ σ ⟫₊ args)
    (sub-ast)   ⟪ σ ⟫ₐ (ast M)         ≡ ast (⟪ σ ⟫ M)
    (sub-bind)  ⟪ σ ⟫ₐ (bind arg)      ≡ bind (⟪ exts σ ⟫ₐ arg)
    
    (sub-sub)†  ⟪ τ ⟫ ⟪ σ ⟫ M  ≡ ⟪ σ ⨟ τ ⟫ M

    (sub-idL)†   id ⨟ σ        ≡ σ
    (sub-idR)†   σ ⨟ id        ≡ σ
    (sub-assoc)† (σ ⨟ τ) ⨟ θ    ≡ σ ⨟ (τ ⨟ θ)
    (sub-dist)   (M • σ) ⨟ τ    ≡ (⟪ τ ⟫ M) • (σ ⨟ τ)

When the equations are applied from left to right, they form a rewrite
system that decides whether any two substitutions are equal.  Many of
the equations of the σ algebra are definitional equalities, so they
are automatically taken into account when you use `refl` to prove an
equality in Agda. The σ algebra equations that are not definitional
equalities are marked with a †. They have been added to Agda's
rewrites using the `--rewriting` option, so if you add the
`--rewriting` option to the top of your Agda files, then they will
also automatically be taken into account when you use
`refl`. Otherwise, you will need to manually apply the equations
marked with †.
