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
parameterized by the kinds of operators and the signature of each
operator, which specifies things like the arity (number of
childer).

To specify the kinds of the operators, create a data type definition
with one constructor for each kind. Using the lambda calculus as an
example, one would need two kinds: one for lambda abstraction and
another for application.

	data Op : Set where
	  op-lam : Op
	  op-app : Op

To specify the signature, write a function that maps your operators to
a list of natural numbers. The length of the list says how many
children there must be, and the numbers in the list say how many
variables become bound for that child. For the lambda calculus,
the signature function would be:

	sig : Op → List ℕ
	sig op-lam = 1 ∷ []
	sig op-app = 0 ∷ 0 ∷ []

UNDER CONSTRUCTION
