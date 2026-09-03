# Contributing

This project is a formalization of a historically specific proof-theoretic system. Small, reviewable pull requests are preferred over broad rewrites, especially in the syntax and substitution layers.

## Before opening a pull request

Run:

```bash
lake build --wfail
lake lint
```

The first command treats Lean warnings as failures, matching CI. The second runs the repository QA driver.

## Lean source policy

- Do not use `sorry` or `admit` in project source.
- Every public module under `TakeutiGLC/` must be imported by `TakeutiGLC.lean`.
- Stable code belongs in permanent namespaces such as `TakeutiGLC/Syntax`; design experiments belong under `TakeutiGLC/Experiment`.
- Prefer small definitions with explicit invariants over hidden foundational assumptions.
- When a representation choice is historically nontrivial, document the source clause that motivates it.

## Source fidelity

The primary source is `Takeuti53.pdf`. Documentation and theorem names should distinguish among:

- what Takeuti defines;
- what Takeuti proves;
- what Takeuti conjectures;
- later proof-theoretic results;
- repository-specific representation choices.

If the formalization intentionally replaces named binding by an alpha-free representation, record the correspondence rather than silently rewriting the historical syntax.

## Pull request shape

A useful PR description normally contains:

1. the source section(s) being formalized;
2. the representation or theorem added;
3. the invariant or correspondence being established;
4. what is deliberately left for the next PR;
5. CI status and any known follow-up work.

Changes that alter the binding convention, type-profile interpretation, or source-to-core correspondence should also update the relevant design documentation.

## Dependency policy

Lean and mathlib are pinned together to the same stable release tag. Release candidates are not used on `main` unless a specific compatibility experiment requires them.

A deliberate toolchain upgrade should update, in the same pull request:

- `lean-toolchain`;
- the mathlib revision in `lakefile.lean`;
- `lake-manifest.json`;
- any documentation that names the pinned release.

Run `lake update` only when intentionally changing or refreshing dependencies, then commit the resulting manifest. `lake lint` checks that the Lean and mathlib release tags remain aligned.
