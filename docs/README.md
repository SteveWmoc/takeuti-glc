# Documentation

This directory separates three kinds of documentation that are easy to confuse in a foundational formalization: the **source specification**, the **design history**, and the **current implementation architecture**.

## Current documents

| Document | Status | Role |
| --- | --- | --- |
| [`syntax-spec.md`](syntax-spec.md) | Current | Faithful source-level account of Takeuti §§1–3; intentionally independent of Lean implementation details. |
| [`syntax-design.md`](syntax-design.md) | Current | Milestone 1 design record and source-to-core correspondence. M2.1 has implemented its name/core/scope layers. |
| [`binding-experiment.md`](binding-experiment.md) | Historical | M1.3a comparison of intrinsically scoped de Bruijn and locally nameless representations. |
| [`opening-closing-experiment.md`](opening-closing-experiment.md) | Historical | M1.3b experiment that supplied the decisive evidence for locally nameless syntax. |
| [`../ROADMAP.md`](../ROADMAP.md) | Current | Milestone status and project-wide QA policy. |

## Current implementation boundary

Milestone 2 is active. The permanent syntax modules are:

```text
TakeutiGLC/Syntax/TypeProfile.lean
TakeutiGLC/Syntax/Symbol.lean
TakeutiGLC/Syntax/Name.lean
TakeutiGLC/Syntax/Core.lean
TakeutiGLC/Syntax/Scope.lean
```

The stable core already fixes the following choices:

- shifted predecessor-level type profiles;
- a historical source-symbol layer separate from kind-free internal names;
- locally nameless binding;
- independent de Bruijn namespaces for variables and functions;
- nonempty simultaneous variable-abstraction blocks;
- structural well-scopedness as an explicit proposition rather than a datatype index;
- terms as type-`(0)` varieties rather than a fourth raw syntax category.

The next implementation layer is the extrinsic typing/well-formedness judgment for §§2–3. After that come auxiliary occurrence selection, stable opening/closing, renaming, weakening, and §5 substitution.

## Reading order

For the mathematical source, start with [`syntax-spec.md`](syntax-spec.md). For the Lean architecture, read [`syntax-design.md`](syntax-design.md). The two experiment documents are useful when the reason for the binding decision matters, but they are not normative specifications.

## Documentation rule

Documentation should say explicitly whether a statement is:

1. a definition or theorem from Takeuti's 1953 paper;
2. an implementation/design decision of this repository;
3. a later proof-theoretic result not proved in the 1953 paper; or
4. an intended future theorem that has not yet been formalized.

In particular, cut elimination is not to be described as a theorem of the 1953 paper: Takeuti presents it there as the fundamental conjecture.
