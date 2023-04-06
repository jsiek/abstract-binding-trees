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
modal logic, in the spirit of the LSLR logic of Dreyer, Ahmed, and
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

    V,W ::= ƛ N | $ k | V ⟨ G , g !⟩

The reduction rules make use of frames, which are defined as follows.

    F ::= □· M | V ·□ | □⟨ G , g !⟩ | □⟨ H , h ?⟩

The operation `F ⟦ M ⟧` plugs a term into a frame.

The reduction rules of the cast calculus are as follows:

    (ξ)        If M —→ N, then F ⟦ M ⟧ —→ F ⟦ N ⟧
    (ξ-blame)  F ⟦ blame ⟧ —→ blame
    (β)        (ƛ N) · W —→ N [ W ]
    (collapse) V ⟨ G , g !⟩ ⟨ G , g ?⟩ —→ V
    (collide)  If G ≢ H, then V ⟨ G , g !⟩ ⟨ H , h ?⟩ —→ blame.


## Step-indexed Logic

```
open import rewriting.examples.StepIndexedLogic
```

The step-indexed logic is a first-order logic (i.e., a logic with
"and", "or", "implies", "for all"). To distinguish its connectives
from Agda's, we add a superscript "o". So "and" is written `×ᵒ`,
"implies" is written `→ᵒ`, and so on.  The step-indexed logic also
includes a notion of time in which there is clock counting down. The
logic is designed in such a way that if a formula `P` is true at some
time then `P` stays true in the future (at lower counts). When the
clock reaches zero, every formula becomes true.  Furthermore, the
logic includes a "later" operator, written `▷ᵒ P`, meaning that `P` is
true one clock tick in the future.

Just as `Set` is the type of true/false formulas in Agda, `Setᵒ` is
the type of true/false formulas in the step indexed logic. It is a
record that bundles the formula itself, represented with a function of
type `ℕ → Set`, with proofs that the formula is downward closed and
true at zero.

    record Setᵒ : Set₁ where
      field
        # : ℕ → Set
        down : downClosed #
        tz : # 0                -- tz short for true at zero
    open Setᵒ public

For example, the "false" proposition is false at every time except zero.

    ⊥ᵒ : Setᵒ
    ⊥ᵒ = record { # = λ { zero → ⊤ ; (suc k) → ⊥ }
                ; down = λ { zero ⊥n .zero z≤n → tt}
                ; tz = tt
                }

The "and" proposition `P ×ᵒ Q` is true at a given time `k` if both `P`
and `Q` are true at time `k`.

    _×ᵒ_ : Setᵒ → Setᵒ → Setᵒ
    P ×ᵒ Q = record { # = λ k → # P k × # Q k
                    ; down = λ k (Pk , Qk) j j≤k →
                              (down P k Pk j j≤k) , (down Q k Qk j j≤k)
                    ; tz = (tz P) , (tz Q)
                    }

We embed arbitrary Agda formulas into the step-indexed logic with the
following operator, written `S ᵒ`, which is true if and only if `S` is
true, except at time zero, when `S ᵒ` has to be true.

    _ᵒ  : Set → Setᵒ
    S ᵒ = record { # = λ { zero → ⊤ ; (suc k) → S }
                 ; down = λ { k Sk zero j≤k → tt
                            ; (suc k) Sk (suc j) j≤k → Sk}
                 ; tz = tt
                 }

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
M —→* N = Σ[ n ∈ ℕ ] (#(μᵒ (flipᶠ mreduce tt) (M , N)) n)
