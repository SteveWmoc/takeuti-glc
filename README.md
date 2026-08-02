# Takeuti GLC

A Lean 4 formalization of Gaisi Takeuti's generalized logic calculus (GLC), introduced in his 1953 paper *On a generalized logic calculus*.

> **Status:** project scaffold. The repository currently records the source, design constraints, and a minimal compiling Lean library. No part of GLC is yet claimed as formalized.

## Source

The repository includes a scan of the original article:

- Gaisi Takeuti, *On a generalized logic calculus* (1953): [`Takeuti53.pdf`](Takeuti53.pdf)

Takeuti's Chapter I develops the formal language and calculus: symbols, varieties and formulas, homology of expressions, substitution, and proof figures. Chapter II proves metatheorems involving restriction, type elevation, and the introduction of sets and functions. The paper proposes cut elimination for GLC as a fundamental conjecture; it does not prove that conjecture.

## Intended scope

The project is expected to proceed in layers:

1. type profiles and scoped higher-type syntax;
2. varieties, functionals, and formulas;
3. alpha-equivalence or an alpha-free representation;
4. renaming and capture-avoiding substitution;
5. sequents and GLC derivations;
6. restriction and type-elevation translations;
7. the consistency-extension results proved in the article;
8. later comparison with modern higher-order cut-elimination results.

The immediate goal is deliberately modest: establish a faithful, maintainable syntax kernel before committing to the full calculus.

## Building

The project uses Lean 4 and mathlib.

```bash
lake update
lake build
```

## Repository layout

- `TakeutiGLC/` — Lean source files
- `TakeutiGLC.lean` — public import root
- `ROADMAP.md` — staged development plan
- `Takeuti53.pdf` — the source article

## Development policy

Public modules must be imported by `TakeutiGLC.lean`. Continuous integration rejects `sorry` and `admit` in Lean source files.
