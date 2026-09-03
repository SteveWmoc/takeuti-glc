# Takeuti GLC

[![CI](https://github.com/SteveWmoc/takeuti-glc/actions/workflows/ci.yml/badge.svg)](https://github.com/SteveWmoc/takeuti-glc/actions/workflows/ci.yml)

A Lean 4 formalization of Gaisi Takeuti's generalized logic calculus (GLC), introduced in his 1953 paper *On a generalized logic calculus*.

> **Project status:** Milestone 2 is underway. Milestone 1 fixed the source specification and binding architecture; M2.1 promoted that design to a stable locally nameless syntax core with structural well-scopedness, and M2.2 adds the context-indexed extrinsic typing layer for §§2–3. Occurrence-sensitive source side conditions and Takeuti's indication machinery are the next formalization target.

## Source and scope

The repository includes a scan of the original article:

- Gaisi Takeuti, *On a generalized logic calculus* (1953): [`Takeuti53.pdf`](Takeuti53.pdf)

Takeuti's Chapter I develops the formal language and calculus: symbols, varieties and formulas, homology, substitution, and proof figures. Chapter II proves metatheorems involving restriction, type elevation, and the introduction of sets and functions.

The paper **states cut elimination as a fundamental conjecture; it does not prove it**. Any future cut-elimination phase in this repository is therefore explicitly separated from the formalization of the results actually proved in the 1953 article.

## What is implemented

The stable syntax layer currently contains:

- shifted Takeuti type profiles and function profiles;
- the historical source-level symbol classification;
- kind-free names for the internal syntax;
- raw `Variety`, `Formula`, and `Functional` syntax;
- independent de Bruijn namespaces for bound variables and bound functions;
- nonempty variable-abstraction blocks for §§2.6 and 3.2;
- structural well-scopedness judgments and closedness predicates;
- independent variable/function typing contexts;
- extrinsic typing for varieties and functionals;
- typed well-formedness for formulas and pointwise argument typing;
- the §2.10 term condition as type `(0)`.

Still to come in Milestone 2 are occurrence-sensitive source well-formedness for §§2.8–2.9, auxiliary occurrence selection for §3.2 and §5, opening/closing in the stable namespace, renaming and weakening, and Takeuti's capture-avoiding substitution machinery.

## Architecture

Milestone 1 compared an intrinsically scoped de Bruijn encoding with a locally nameless encoding. The project selected **locally nameless syntax** because Takeuti's later metatheory is transformation-heavy: substitution, restriction, and type elevation all benefit from keeping the raw recursive syntax stable while carrying scope correctness as a separate invariant.

Variable and function binders use separate de Bruijn namespaces. Historical bound names disappear at the source-to-core boundary, so ordinary core equality is intended to absorb admissible bound renaming rather than requiring a pervasive quotient by alpha-equivalence.

Typing is likewise extrinsic. `TypingContext` carries independent lists of variable types and function profiles; de Bruijn indices are typed by lookup, while free and special internal names carry their profiles directly. The typing relation enforces argument compatibility, the `(0)` result of function application, abstraction result profiles, and the term condition on functional bodies.

See [`docs/syntax-design.md`](docs/syntax-design.md) for the design record.

## Documentation

| Document | Purpose |
| --- | --- |
| [`docs/README.md`](docs/README.md) | Documentation index and current status |
| [`docs/syntax-spec.md`](docs/syntax-spec.md) | Source-level transcription of §§1–3 |
| [`docs/syntax-design.md`](docs/syntax-design.md) | Stable syntax architecture chosen in Milestone 1 |
| [`docs/binding-experiment.md`](docs/binding-experiment.md) | Historical M1.3a binding comparison |
| [`docs/opening-closing-experiment.md`](docs/opening-closing-experiment.md) | Historical M1.3b opening/closing comparison |
| [`ROADMAP.md`](ROADMAP.md) | Staged formalization plan |

## Build and QA

The project is pinned to Lean 4.33.1 and the matching mathlib release. Release-candidate toolchains are not used for the main development branch.

```bash
lake build
lake lint
```

For the same warning policy used in CI:

```bash
lake build --wfail
```

`lake lint` runs repository-level QA checks, including the no-placeholder policy, Lean/mathlib pin alignment, public-module coverage, trailing-whitespace checks, and Lean-source tab checks. CI runs both `lake build --wfail` and `lake lint`.

Use `lake update` only when intentionally refreshing the dependency manifest, and commit the resulting manifest together with the corresponding toolchain and mathlib pin changes.

## Repository layout

```text
TakeutiGLC/
  Syntax/       stable syntax and metatheory
  Experiment/   Milestone 1 design experiments retained for provenance
TakeutiGLC.lean public import root
docs/           specifications, experiments, and design records
ROADMAP.md      milestone plan
Takeuti53.pdf   source article
```

## Development policy

- Public Lean modules must be imported by `TakeutiGLC.lean`.
- `sorry` and `admit` are not permitted in project Lean source.
- CI treats Lean warnings as failures.
- Experimental code stays under `TakeutiGLC/Experiment`; stable metatheory belongs under `TakeutiGLC/Syntax` or later permanent namespaces.
- Claims in the documentation distinguish what Takeuti proves, what he conjectures, and what this repository has actually formalized.

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the working conventions used by the project.
