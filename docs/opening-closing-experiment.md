# Milestone 1.3b — opening and closing experiment

## Status

**Historical design record.** This experiment supplied the decisive evidence for the Milestone 1 binding choice. The locally nameless representation was selected and is now implemented in the stable syntax namespace. The normative decision is recorded in [`syntax-design.md`](syntax-design.md).

This document is retained because it explains *why* the project chose locally nameless syntax rather than an intrinsically scoped `Fin`-indexed family.

## Purpose

M1.3a made the binding tradeoff visible at the datatype level. This second experiment tested both candidate representations against the first operations that actually move syntax across Takeuti binders.

The tested fragment was deliberately smaller than the substitution theory of §5. In both prototypes it implemented:

- closing and opening one free variable;
- closing and opening one free function;
- traversal through the independent variable and function binder namespaces;
- variable-abstraction blocks of the kind used in §2.6 and, for term bodies, §3.2;
- elementary round-trip checks at the index and direct-occurrence levels.

The experiment continued to leave the full typing judgment extrinsic so that it measured binding costs rather than typing costs.

## 1. Common convention

A newly inserted binder occupies de Bruijn index `0` at the point where it is introduced. Existing indices at or beyond the insertion cutoff are shifted by one. Under a binder of the same namespace, the cutoff increases; under a binder of the other namespace, it does not.

For a Takeuti abstraction block, repeated closing gives the first source name index `0`, the second index `1`, and so on. The block is still treated as a genuine simultaneous binder rather than as a claim that Takeuti wrote nested unary abstractions.

## 2. Locally nameless result

`TakeutiGLC/Experiment/Binding/LocallyNamelessOps.lean` keeps all transformations on the same raw `Variety` and `Formula` datatypes.

The recursive clauses closely mirror the paper-level description. Crossing a variable quantifier changes one natural-number cutoff; crossing a function quantifier changes the other. Crossing a §2.6 abstraction adds the block size to the variable cutoff. No casts are required merely because the surrounding scope changes.

Block closing can therefore be written as repeated single-name closing over an ordinary `List VariableName`, and block opening as the corresponding reverse sequence.

The cost is explicit rather than absent: raw natural-number indices may dangle, so a stable locally nameless development needs a local-closure / well-scopedness proposition and preservation lemmas. M2.1 has since implemented that structural well-scopedness layer in `TakeutiGLC/Syntax/Scope.lean`.

## 3. Intrinsically scoped de Bruijn result

`TakeutiGLC/Experiment/Binding/DeBruijnOps.lean` performs the same operations on syntax families indexed by variable and function scope depths.

This buys a strong invariant: an out-of-scope bound occurrence cannot be constructed. But every opening or closing operation changes a datatype index. The implementation therefore needs:

- finite-index insertion and removal functions on `Fin`;
- explicit proofs that cutoffs lie inside the current scope;
- arithmetic obligations when crossing quantifiers;
- casts or simplification when a Takeuti block changes a depth from expressions such as `k + v` to `k + (v + 1)`;
- dependent recursive definitions for arbitrary block closing/opening.

This burden comes in addition to the custom `Arguments` spine already forced by Lean's positivity checker in M1.3a.

The intrinsic representation therefore moves scope correctness into syntax and transformation types, but the price is paid repeatedly in ordinary syntax operations.

## 4. Round-trip checks

Both experiments include elementary bookkeeping laws such as:

- inserting and then removing an older de Bruijn index restores it;
- a direct free variable can be closed and opened again;
- an existing bound-variable occurrence is shifted and restored;
- a direct free-function application can be closed and opened again.

The experiment intentionally stopped short of proving a permanent metatheory over either prototype. Full structural open/close theorems belong to the stable Milestone 2 syntax, not to superseded experimental APIs.

## 5. Comparison

### Construction complexity

The locally nameless definitions are ordinary recursive functions on a stable datatype. The intrinsically scoped definitions require dependent source/target types, cutoff proofs, and finite-index arithmetic.

**Advantage: locally nameless.**

### Scope invariant

The intrinsically scoped representation rules out dangling bound references by construction. Locally nameless raw syntax requires a separate well-scopedness judgment.

**Advantage: intrinsically scoped de Bruijn.**

### Two binder namespaces

Both approaches handle the variable/function distinction cleanly. In both, entering a binder in one namespace leaves the other namespace untouched.

**Roughly even.**

### Takeuti abstraction blocks

Blocks are natural in either representation, but the locally nameless implementation can use ordinary list folds. The intrinsically scoped version exposes the changing scope depth in its result type.

**Advantage: locally nameless.**

### Prospects for §5 substitution

Takeuti's §5 definitions repeatedly traverse binders, rename to avoid capture, and compose substitutions. The experiment strongly suggested that an intrinsically scoped encoding would carry dependent scope arithmetic through nearly every clause. Locally nameless syntax keeps the recursive transformation definitions closer to the mathematical presentation while concentrating the main proof burden in reusable well-scopedness lemmas.

This was an architectural inference from opening/closing, not a formalized §5 substitution comparison.

## 6. Decision reached

The evidence from M1.3a and M1.3b led Milestone 1 to select **locally nameless syntax** for the stable GLC core.

The reason was not line count alone. Takeuti's later metatheory is transformation-heavy: §5 substitution, §7 restriction, and §8 type elevation all repeatedly traverse syntax. A representation that changes dependent datatype indices at every binder would make the binding representation an active proof burden throughout those later phases.

The selected design therefore concentrates scope obligations in a reusable structural invariant and keeps raw syntax transformations on stable recursive datatypes.

M2.1 has now implemented the first permanent consequences of that decision:

```text
TakeutiGLC/Syntax/Name.lean
TakeutiGLC/Syntax/Core.lean
TakeutiGLC/Syntax/Scope.lean
```

The next relevant test of the architecture will come from the stable typing, opening/closing, renaming, and §5 substitution layers. If those expose a concrete defect, the design can be revisited with evidence rather than preference.
