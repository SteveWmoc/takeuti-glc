# Takeuti GLC

A Lean 4 formalization of Gaisi Takeuti's generalized logic calculus (GLC), introduced in his 1953 paper *On a generalized logic calculus*.

> **Status:** Milestone 1 complete. The repository now contains a source-level specification of §§1–3, executable binding experiments, and a reviewed target architecture for the syntax. The stable syntax and substitution kernel are the next phase; no theorem of GLC is yet claimed as formalized.

## Source

The repository includes a scan of the original article:

- Gaisi Takeuti, *On a generalized logic calculus* (1953): [`Takeuti53.pdf`](Takeuti53.pdf)

Takeuti's Chapter I develops the formal language and calculus: symbols, varieties and formulas, homology of expressions, substitution, and proof figures. Chapter II proves metatheorems involving restriction, type elevation, and the introduction of sets and functions. The paper proposes cut elimination for GLC as a fundamental conjecture; it does not prove that conjecture.

## Current design

Milestone 1 selected a locally nameless core with separate de Bruijn namespaces for bound variables and bound functions. Free and special names remain named; historical bound names disappear at the core boundary. Scope correctness will be expressed by a reusable well-scopedness judgment, while typing will initially be an extrinsic context-indexed judgment.

The source transcription is recorded in [`docs/syntax-spec.md`](docs/syntax-spec.md), the binding experiments in [`docs/binding-experiment.md`](docs/binding-experiment.md) and [`docs/opening-closing-experiment.md`](docs/opening-closing-experiment.md), and the final Milestone 1 decision in [`docs/syntax-design.md`](docs/syntax-design.md).

## Intended scope

The project proceeds in layers:

1. type profiles and higher-type syntax design;
2. stable locally nameless syntax, scope, renaming, and substitution;
3. sequents and GLC derivations;
4. proof-preserving substitutions;
5. restriction and type-elevation translations;
6. the set-and-function applications proved in the article;
7. later comparison with modern higher-order cut-elimination results.

The immediate goal is Milestone 2: build the stable syntax library and prove the identity, composition, and commutation laws needed for Takeuti's §5 substitution theory.

## Building

The project uses Lean 4 and mathlib.

```bash
lake update
lake build
```

## Repository layout

- `TakeutiGLC/` — Lean source files
- `TakeutiGLC.lean` — public import root
- `docs/` — source specifications, experiments, and design records
- `ROADMAP.md` — staged development plan
- `Takeuti53.pdf` — the source article

## Development policy

Public modules must be imported by `TakeutiGLC.lean`. Continuous integration rejects `sorry` and `admit` in Lean source files.
