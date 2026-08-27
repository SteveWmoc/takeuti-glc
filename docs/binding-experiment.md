# Milestone 1.3 binding experiment

## Status

**Historical design record.** This document captures the M1.3a state of the
project before a binding representation was selected. The subsequent
opening/closing experiment chose the locally nameless alternative, and
`docs/syntax-design.md` records the stable decision. M2.1 has since promoted
that design to `TakeutiGLC/Syntax/Name.lean`, `Core.lean`, and `Scope.lean`.

The remainder of this document is intentionally preserved as the contemporaneous
experiment report. Future-tense statements below describe what was still open
at M1.3a; they are not the current project status.

This document compares two deliberately small representations of the binding
fragment needed for Takeuti's §§2.6, 2.8, 2.9, and 3.2. The common fragment
includes:

- free, special, and bound variable occurrences;
- free, special, and bound function occurrences;
- atomic formulas;
- `¬`, `∧`, and `∨`;
- variable quantifiers;
- function quantifiers;
- nonempty higher-type variable-abstraction blocks (§2.6);
- nonempty functional-abstraction blocks (§3.2).

The prototypes intentionally leave the full typing judgment extrinsic. In
particular, they record Takeuti type profiles at binders but do not yet prove in
the datatype that every application has exactly the argument types required by
§§2.3–2.5. This keeps the experiment focused on binding.

## 1. Common structural choices

Both prototypes remove source-level names for bound variables and bound
functions. The historical symbol layer in `TakeutiGLC/Syntax/Symbol.lean`
retains Takeuti's free/bound/special classification, but the experimental core
does not store that classification inside named occurrences. Instead,
`TakeutiGLC/Experiment/Names.lean` keeps only a profile and opaque name index.
The occurrence constructor itself determines whether such a name is free or
special; bound occurrences are represented only by de Bruijn indices.

This separation prevents contradictory core objects such as a constructor
labelled `freeVar` carrying a historical symbol tagged `bound`, and keeps the
binding comparison focused on the actual scope representation rather than on a
separate well-formedness condition for symbol kinds.

There are two independent binder classes:

```text
variable binders    function binders
```

They must remain independent because §2.8 quantifies over variables while §2.9
quantifies over functions. Entering one kind of binder must not alter the
indices of the other kind.

For §2.6 and §3.2, a higher-type abstraction binds a nonempty block of
variables. If the resulting type is

```text
(n₁ + 1, ..., nᵢ + 1),
```

the prototype stores the predecessor levels `n₁, ..., nᵢ`; the block size is
therefore always positive. The body is allowed to omit any or all of the newly
bound variables, preserving the vacuous abstractions allowed by Takeuti.

## 2. Intrinsically scoped de Bruijn prototype

File:

```text
TakeutiGLC/Experiment/Binding/DeBruijn.lean
```

The core types are indexed by two context depths:

```lean
Variety (varDepth funDepth : Nat)
Formula (varDepth funDepth : Nat)
Functional (varDepth funDepth : Nat)
```

A bound variable occurrence contains

```lean
Fin varDepth
```

and a bound function occurrence contains

```lean
Fin funDepth.
```

Consequently, an out-of-scope bound reference is unrepresentable. For example,
a closed object at variable depth `0` cannot contain a bound-variable occurrence
because `Fin 0` is empty.

### Quantifiers

A variable quantifier changes only the variable depth:

```text
Formula v f  --->  body : Formula (v + 1) f
```

while a function quantifier changes only the function depth:

```text
Formula v f  --->  body : Formula v (f + 1).
```

### Abstraction blocks

An abstraction over `i` variables extends only the variable context by `i`:

```text
Formula (i + v) f
```

for §2.6, and similarly for the term body of a §3.2 functional. Nothing in the
type requires the body to use all `i` new indices, so vacuous positions remain
representable.

### Immediate advantage

Scope correctness is carried by the datatype. Many impossible states simply
cannot be constructed.

### Immediate cost

A transformation that moves syntax across a binder changes its Lean type. For
example, closing a free variable under a new quantifier will have a shape like

```text
Formula v f -> Formula (v + 1) f.
```

Under nested binders, this requires cutoff-aware embeddings of `Fin` indices.
For an `i`-variable abstraction block, existing outer variable indices must be
embedded past `i` newly bound positions. The prototype therefore predicts that
renaming, closing, and substitution will carry nontrivial dependent bookkeeping.

The experiment also exposed an implementation cost: Lean's positivity checker
does not accept `List (Variety v f)` directly as a recursive field of this
mutually indexed family, so the prototype uses a mutually defined
`Arguments v f` spine instead.

That bookkeeping is not intrinsically a defect: it buys stronger raw scope
invariants. The following M1.3b experiment was designed to determine whether the
tradeoff remained favorable once opening and closing were implemented.

## 3. Locally nameless prototype

File:

```text
TakeutiGLC/Experiment/Binding/LocallyNameless.lean
```

The raw recursive syntax has no context indices. Free and special occurrences
use the same kind-free source names as the de Bruijn prototype, while bound
occurrences use raw natural-number de Bruijn indices:

```lean
boundVar    : Nat -> Variety
atomBound   : Nat -> List Variety -> Formula
boundFunApp : Nat -> List Variety -> Variety
```

Quantifier and abstraction constructors therefore do not change the Lean type
of their bodies.

### Immediate advantage

The recursive datatype stays stable while entering binders. This is attractive
for the operations that mirror Takeuti's own definitions: converting selected
free names to bound occurrences (closing), replacing bound occurrences by free
names (opening), and substituting for free variables or free functions.

In particular, §2.6 and §3.2 look very much like multi-name closing operations,
while §§2.8–2.9 look like single-name closing operations in two independent
namespaces.

### Immediate cost

Raw natural-number indices are not intrinsically checked against a context
depth. A real locally nameless development must therefore define and preserve a
local-closure / well-scopedness judgment with separate variable and function
depths.

Thus scope correctness moves from the datatype into propositions and proof
obligations.

## 4. Alpha-equivalence and Takeuti's homology

Both prototypes have an important advantage over a literal named encoding:
bound names are absent from the core representation. Renaming a bound variable
or bound function does not create a distinct raw object merely because a
different source-level letter was chosen.

This is promising for Takeuti's later notion of homologous expressions. The
intended long-term outcome is that source expressions differing only by bound
renaming translate to the same internal object, so that the calculus does not
need a pervasive quotient by alpha-equivalence.

This remains a design expectation until the historical source translation and
homology correspondence theorem are formalized.

## 5. What this first experiment established

The first prototype slice gave several conclusions that survived into the
stable design.

1. Separate variable and function binder namespaces are natural in both
   representations.
2. Takeuti's nonempty higher-type abstraction is naturally represented as a
   binder block rather than as an artificial nest of unary binders.
3. Vacuous abstraction requires no special case in either representation.
4. Historical symbol roles should be erased before entering the core; the
   occurrence constructor should determine free versus special, while bound
   occurrences should be indices only.
5. Eliminating bound source names from the core should make alpha-equivalence
   substantially simpler than a literal transcription.
6. The central tradeoff is explicit:
   - intrinsically scoped de Bruijn syntax pays for scope correctness in the
     types of transformations;
   - locally nameless syntax keeps transformations on a stable raw datatype but
     pays for scope correctness in well-scopedness proofs.

## 6. Subsequent outcome

M1.3b implemented opening and closing in both prototypes. The dependent scope
arithmetic of the intrinsically scoped version recurred throughout ordinary
transformations, while the locally nameless operations remained structurally
close to Takeuti's recursion. Milestone 1 therefore selected locally nameless
syntax. See [`opening-closing-experiment.md`](opening-closing-experiment.md) for
the comparison and [`syntax-design.md`](syntax-design.md) for the normative
decision.
