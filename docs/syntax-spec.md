# Syntax specification

## Status

This document begins Milestone 1. It records the source-level conventions that
our Lean prototypes are intended to represent. The current code covers only
type profiles; it does **not** yet choose a binding representation or define
Takeuti's varieties, formulas, or functionals.

The primary source is Gaisi Takeuti, *On a generalized logic calculus* (1953),
included in this repository as [`Takeuti53.pdf`](../Takeuti53.pdf).

## 1. Type conventions in the paper

### 1.1 The distinguished type `(0)`

Takeuti treats `(0)` separately. Variables of type `(0)` have no argument
place (§1.1.1–§1.1.3). Varieties of type `(0)` are called *terms* (§2.10).

### 1.2 Nonzero profiles

A nonzero type has the form

```text
(n₁, ..., nᵢ)
```

where `i ≥ 1` and every displayed entry `nₖ` is a positive integer
(§1.1.4–§1.1.6 and §1.2.1–§1.2.3). A symbol of this type has `i` argument
places.

Takeuti permits the abbreviation `n` for the singleton type `(n)` (§2.11).
Thus `(0)` remains the distinguished base type, while `(1)`, `(2)`, and so on
are one-place higher types.

### 1.3 Argument levels

The formation rules are stated using a shifted profile

```text
(n₁ + 1, ..., nᵢ + 1).
```

In §§2.3–2.5, the `k`th argument place of a variable or function of this type
is filled by a variety of singleton type `(nₖ)`.

Consequently, the entries `n₁, ..., nᵢ` may be viewed as the predecessor
levels of the accepted arguments:

```text
symbol type:     (n₁ + 1, ..., nᵢ + 1)
argument types:  (n₁),     ..., (nᵢ)
```

The same shift appears in the abstraction clauses. Section 2.6 constructs a
variety of type `(n₁ + 1, ..., nᵢ + 1)` by abstracting variables of types
`(n₁), ..., (nᵢ)`. Section 3.2 assigns that same shifted type to a functional
formed by abstracting variables from a term.

### 1.4 Height

Section 5.1 defines the height of a variable, function, variety, or functional
of type `(n₁, ..., nᵢ)` to be the largest of the displayed numbers
`n₁, ..., nᵢ`. The distinguished type `(0)` therefore has height `0`.

## 2. Current Lean prototype

`TakeutiGLC/Syntax/TypeProfile.lean` uses the following shifted encoding:

```lean
inductive TypeProfile where
  | zero
  | higher (head : Nat) (tail : List Nat)
```

The intended correspondence is

```text
TypeProfile.zero
    ↔ (0)

TypeProfile.higher n [n₂, ..., nᵢ]
    ↔ (n + 1, n₂ + 1, ..., nᵢ + 1).
```

The constructor `higher` stores predecessor levels rather than the positive
entries displayed in the paper. This has three useful consequences:

1. a nonzero profile is nonempty by construction;
2. zero cannot occur among its displayed entries;
3. the types required at its argument places are obtained directly by mapping
   `TypeProfile.monotype` over the stored levels.

The prototype provides:

- `monotype n`, representing Takeuti's singleton type `(n)`;
- `displayedEntries`, recovering the numbers written in the paper;
- `argumentLevels`, returning the stored predecessor levels;
- `argumentTypes`, returning the corresponding singleton profiles;
- `arity`, the number of argument places;
- `height`, the maximum displayed level.

## 3. Category restrictions deferred to later syntax

The single datatype represents every type profile needed by the eventual
syntax, but the paper does not assign every symbol category to every profile.
In particular:

- variables and varieties include the distinguished type `(0)`;
- the function symbols listed in §1.2 have nonzero profiles;
- predicates are special variables of type `(1, ..., 1)`.

These restrictions should be enforced by the future syntax constructors, not
by splitting `TypeProfile` itself into several nearly identical datatypes.

## 4. Decisions deliberately postponed

This prototype does not decide:

- whether the final syntax will be intrinsically scoped;
- whether binders will use de Bruijn indices, a locally nameless method, or
  named syntax with alpha-equivalence;
- how variable symbols and function symbols will be indexed;
- whether formulas, varieties, and functionals should be mutually inductive;
- how the historical notion of *homologous* expressions will be related to the
  internal equality of Lean objects.

Those questions require small syntax experiments. The type-profile encoding is
intended to remain usable under any of the leading binding designs.
