# Abstract Binding Trees

This is an Agda library for abstract binding trees as in Robert
Harper's book Practical Foundations for Programming Languages.  An
abstract binding tree (ABT) is a generic form of abstract syntax tree
that also knows about binders and variables. Thus, this library also
defines substitution on ABTs and provides theorems about substitution.
The library represents variables using de Bruijn indices.

An abstract binding tree `ABT` consists of two kinds of nodes:

* Variables: A variable node is a leaf (no children) and stores the de
  Bruijn index.
  
* Operators: An operator node is tagged with the kind of operator and
  it has zero or more children, depending on the kind of operator.

The `ABT` data type is defined in the `Syntax` module, which is
parameterized by the kinds of operators and their signatures, which
specifies things like the number of child nodes for each kind of
operator.

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
    
    data ABT : Set where
      `_ : Var → ABT
      _⦅_⦆ : (op : Op) → Args (sig op) → ABT

