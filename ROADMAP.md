# Roadmap

This repository is being initialized before active development begins. The stages below are intended to prevent premature commitment to a difficult binding representation.

## Milestone 0 — Project scaffold

- [x] Preserve the source article in the repository.
- [x] Create a compiling Lean 4 library.
- [x] Add continuous integration and a no-placeholder policy.
- [x] Record the intended scope without claiming results not yet formalized.

## Milestone 1 — Formal specification of the syntax

- [x] Prototype Takeuti's type profiles with a shifted internal representation.
- [x] Record the type-level correspondence in `docs/syntax-spec.md`.
- [x] Transcribe Takeuti's symbol classes and formation rules from §§1–3.
- [x] Prototype the source-level variable, function, and logical symbol classes.
- [x] Build first intrinsically scoped de Bruijn and locally nameless binding prototypes.
- [x] Record the initial scoping tradeoffs in `docs/binding-experiment.md`.
- [x] Compare closing/opening operations for variable, function, and abstraction binders.
- [x] Separate historical notation from the final internal Lean representation.
- [x] Decide the binding representation.
- [x] State an explicit correspondence between Lean objects and Takeuti's varieties, formulas, and functionals.

**Deliverable:** a reviewed design document and small executable prototypes; not yet the final syntax API. The binding decision and source-to-core correspondence are recorded in `docs/syntax-design.md`.

## Milestone 2 — Renaming and substitution kernel

- [ ] Define renaming and weakening for every syntactic category.
- [ ] Define capture-avoiding substitution of varieties for variables.
- [ ] Define substitution of functionals for function symbols.
- [ ] Prove identity, composition, and commutation laws corresponding to §5.

**Deliverable:** a stable syntax library with no quotient-level ambiguity in ordinary use.

## Milestone 3 — Generalized logic calculus

- [ ] Define sequents.
- [ ] Define structural and logical inference rules.
- [ ] Define GLC derivations as finite proof trees.
- [ ] Define the bounded fragments `G^iLC` from the appendix.
- [ ] Compare the type-zero fragment with ordinary LK.

**Deliverable:** a faithful formal statement of Takeuti's calculus.

## Milestone 4 — Proof-preserving substitutions

- [ ] Lift variable substitution from formulas to derivations.
- [ ] Lift functional substitution from formulas to derivations.
- [ ] Formalize the corresponding metatheorems in §6.

**Deliverable:** the first substantial mechanized metatheorems of the paper.

## Milestone 5 — Restriction and type elevation

- [ ] Formalize restriction and strict restriction from §7.
- [ ] Formalize type elevation from §8.
- [ ] Prove that the translations preserve derivability.
- [ ] Formalize the set-and-function applications in §9.

**Deliverable:** the principal results actually proved in the 1953 article.

## Milestone 6 — Cut elimination, as a separate project phase

Takeuti states cut elimination for GLC (or even `G^1LC`) as a conjecture rather than proving it in this article. Any formalization of cut elimination must therefore use later proof-theoretic work and must include a careful comparison between those later calculi and the exact 1953 system.

- [ ] Identify the best modern target calculus and proof.
- [ ] Formalize or reuse its cut-elimination argument.
- [ ] Prove the necessary equivalence or interpretation theorem for Takeuti's GLC.

This milestone is intentionally outside the initial scope.
