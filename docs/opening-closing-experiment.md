# Milestone 1.3b — opening and closing experiment

## Purpose

Milestone 1.3a made the binding tradeoff visible at the datatype level. This
second experiment tests both candidate representations against the first
operations that actually move syntax across Takeuti binders.

The tested fragment is deliberately smaller than the substitution theory of
§5. In both prototypes we implement:

- closing and opening one free variable;
- closing and opening one free function;
- correct traversal through the independent variable and function binder
  namespaces;
- variable-abstraction blocks of the kind used in §2.6 and, for term bodies,
  §3.2;
- elementary round-trip checks at the index and direct-occurrence levels.

The experiment still leaves the full typing judgment extrinsic.

## 1. Common convention

A newly inserted binder occupies de Bruijn index `0` at the point where it is
introduced. Existing indices at or beyond the insertion cutoff are shifted by
one. Under a binder of the same namespace, the cutoff increases; under a binder
of the other namespace, it does not.

For a Takeuti abstraction block, repeated closing gives the first source name
index `0`, the second index `1`, and so on. This treats the block as a genuine
simultaneous binder rather than pretending that Takeuti wrote an iterated
sequence of unary abstractions.

## 2. Locally nameless result

`TakeutiGLC/Experiment/Binding/LocallyNamelessOps.lean` keeps all transformations
on the same raw `Variety` and `Formula` datatypes.

The important consequence is that the recursive clauses closely mirror the
paper-level description. Crossing a variable quantifier changes one natural
number cutoff; crossing a function quantifier changes the other. Crossing a
§2.6 abstraction adds the block size to the variable cutoff. No casts are
needed merely because the surrounding scope changed.

Block closing can therefore be written as repeated single-name closing over an
ordinary `List VariableName`, and block opening as the corresponding reverse
sequence.

The cost has not disappeared. Raw natural-number indices can be dangling, so a
stable locally nameless development will require a local-closure / well-scoped
predicate and preservation lemmas. The experiment shows, however, that this
obligation is separated from the definitions of opening and closing themselves.

## 3. Intrinsically scoped de Bruijn result

`TakeutiGLC/Experiment/Binding/DeBruijnOps.lean` performs the same operations on
families indexed by variable and function scope depths.

This buys a real invariant: an out-of-scope bound occurrence cannot be
constructed. But every opening or closing operation changes a datatype index.
As a result the implementation needs:

- finite-index insertion and removal functions on `Fin`;
- explicit proofs that each cutoff lies inside its current scope;
- arithmetic obligations when crossing quantifiers;
- casts or simplification steps when a Takeuti block changes a depth from
  `k + v` to `k + (v + 1)`;
- a dependent recursive definition for arbitrary block closing/opening.

This is in addition to the `Arguments` spine already forced by Lean's
positivity checker in M1.3a.

The intrinsic representation therefore pushes scope correctness into the
syntax and transformation types, but the price is paid continuously in the
implementation of syntax operations.

## 4. Round-trip checks

Both experiments include elementary laws showing that the bookkeeping itself
is coherent:

- inserting and then removing an older de Bruijn index restores that index;
- a direct free variable can be closed and opened again;
- an existing bound-variable occurrence is shifted and restored;
- a direct free-function application can be closed and opened again.

These are intentionally small laws. Full structural open/close theorems would
be useful later, but proving them now would begin to build the permanent
metatheory before Milestone 1 has selected the permanent syntax.

## 5. Comparison

### Construction complexity

The locally nameless definitions remain ordinary recursive functions on a
stable datatype. The intrinsically scoped definitions require dependent source
and target types, cutoff proofs, and finite-index arithmetic.

**Advantage: locally nameless.**

### Scope invariant

The intrinsically scoped representation rules out dangling bound references by
construction. Locally nameless raw syntax requires a separate local-closure
judgment.

**Advantage: intrinsically scoped de Bruijn.**

### Two binder namespaces

Both approaches handle the variable/function distinction cleanly. In both,
entering a binder in one namespace leaves the other namespace untouched.

**Roughly even.**

### Takeuti abstraction blocks

Blocks are easy to describe in either representation, but the locally nameless
implementation can use ordinary list folds. The intrinsically scoped version
must expose the changing scope depth in its result type.

**Advantage: locally nameless.**

### Prospects for §5 substitution

Takeuti's §5 definitions repeatedly traverse binders, rename to avoid capture,
and compose substitutions. The opening/closing experiment suggests that an
intrinsically scoped encoding would carry dependent scope arithmetic through
nearly every clause. Locally nameless syntax should keep the recursive
substitution definitions closer to the mathematical presentation, at the cost
of proving local-closure preservation separately.

This is an inference from the present experiment, not yet a formalized §5
substitution comparison.

## 6. Provisional assessment

The evidence now leans clearly toward **locally nameless syntax** for the stable
GLC core.

The reason is not merely shorter code. Takeuti's later metatheory is dominated
by transformations of syntax. A representation that makes every transformation
change dependent indices is likely to tax restriction, type elevation, and
proof-preserving substitution repeatedly. Locally nameless syntax concentrates
its main cost in a reusable well-scopedness layer instead.

Milestone 1 should nevertheless record the final choice in a separate syntax
design document rather than silently promoting this prototype. That design
record should specify the local-closure judgment, the historical-to-core
translation, and the intended treatment of Takeuti's homology before the stable
syntax API is created.
