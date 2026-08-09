# Syntax specification

## Status

This document records the source-level syntax conventions in §§1–3 of Gaisi
Takeuti's 1953 paper *On a generalized logic calculus*. The Lean code currently
contains executable prototypes for type profiles and source-level symbol
classes. It does **not** yet choose a binding representation or define the final
inductive types for varieties, formulas, or functionals.

The primary source is included in this repository as
[`Takeuti53.pdf`](../Takeuti53.pdf).

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

## 2. Current type-profile prototype

`TakeutiGLC/Syntax/TypeProfile.lean` uses the shifted encoding

```lean
inductive TypeProfile where
  | zero
  | higher (head : Nat) (tail : List Nat)
```

with intended correspondence

```text
TypeProfile.zero
    ↔ (0)

TypeProfile.higher n [n₂, ..., nᵢ]
    ↔ (n + 1, n₂ + 1, ..., nᵢ + 1).
```

The constructor `higher` stores predecessor levels rather than the positive
entries displayed in the paper. This makes a nonzero profile nonempty by
construction, prevents zero from occurring among its displayed entries, and
makes the accepted argument types available directly.

The prototype provides `monotype`, `displayedEntries`, `argumentLevels`,
`argumentTypes`, `arity`, and `height`.

## 3. Symbols (§1)

### 3.1 Variables (§1.1)

Takeuti distinguishes three classes of variables:

- **free variables**;
- **bound variables**;
- **special variables**.

All three classes occur at type `(0)` and at every nonzero profile
`(n₁, ..., nᵢ)` with positive entries. A variable of nonzero profile has one
argument place for each displayed entry.

A special variable of type `(1, ..., 1)` is called a **predicate**. Takeuti
lists equality, order, and membership as special predicate symbols of type
`(1, 1)`, using infix notation for them.

The prototype `TakeutiGLC/Syntax/Symbol.lean` records the three source-level
classes as `VariableKind` and represents a variable symbol by its class, type
profile, and an opaque numerical name. That number has no binding meaning.

### 3.2 Functions (§1.2)

Takeuti likewise distinguishes:

- **free functions**;
- **bound functions**;
- **special functions**.

The function symbols listed in §1.2 have only nonzero profiles. Special
functions include addition and multiplication of type `(1, 1)`.

`FunctionProfile` stores only nonzero profiles, again in predecessor-level
form, and `FunctionSymbol` records the function class, profile, and an opaque
name.

### 3.3 Logical symbols (§1.3)

Takeuti's five logical symbols are:

```text
¬    ∧    ∨    ∀    E
```

where `E` is his existential quantifier notation. The prototype uses the Lean
constructors `neg`, `conj`, `disj`, `all`, and `exists`.

## 4. Varieties and formulas (§2)

Takeuti calls any row of symbols a **figure** and recursively defines varieties
and formulas among figures. This section records the formation rules without
yet choosing Lean binders.

### 4.1 Base varieties (§§2.1–2.2)

Every free variable of type `(0)` is a variety of type `(0)`, and every special
variable of type `(0)` is a variety of type `(0)`.

Bound variables of type `(0)` are therefore not standalone varieties; their
occurrences arise through the binding constructions below.

### 4.2 Atomic formulas from variables (§§2.3–2.4)

Let `α` be a free variable of type

```text
(n₁ + 1, ..., nᵢ + 1)
```

and let `Vₖ` be a variety of type `(nₖ)` for every `k`. Filling the argument
places of `α` with the `Vₖ` produces a formula

```text
α[V₁, ..., Vᵢ].
```

The same formation rule applies to a special variable `σ` of that profile:

```text
σ[V₁, ..., Vᵢ]
```

is a formula.

There is no corresponding atomic-formula constructor for a bound variable as a
source-level symbol; bound-variable occurrences are introduced by the binding
rules.

### 4.3 Terms from function application (§2.5)

Let `f` be a **free or special** function of type

```text
(n₁ + 1, ..., nᵢ + 1)
```

and let `Vₖ : (nₖ)` for every argument place. Then

```text
f(V₁, ..., Vᵢ)
```

is a variety of type `(0)`, hence a term.

Bound functions are not used directly in this application clause; their
occurrences are introduced by function quantification in §2.9.

### 4.4 Higher-type varieties by abstraction (§2.6)

Take pairwise distinct free variables

```text
α¹ : (n₁), ..., αⁱ : (nᵢ)
```

and a formula `A` containing them. Choose pairwise distinct bound variables

```text
φ¹ : (n₁), ..., φⁱ : (nᵢ)
```

which do not occur in `A`. Replace every occurrence of each `αᵏ` by the
corresponding `φᵏ`, and prefix the resulting formula by the abstraction braces

```text
{φ¹, ..., φⁱ}.
```

The result is a variety of type

```text
(n₁ + 1, ..., nᵢ + 1).
```

This is the first formation rule whose faithful mechanization depends strongly
on the eventual representation of binders and freshness.

### 4.5 Propositional connectives (§2.7)

If `A` and `B` are formulas, then

```text
¬A
A ∧ B
A ∨ B
```

are formulas.

### 4.6 Quantification over variables (§2.8)

Let `α` be a free variable of type `(n₁, ..., nᵢ)` occurring in a formula
`A`. Choose a bound variable `φ` of the same type which does not occur in `A`.
Replace all occurrences of `α` in `A` by `φ`. Prefixing the result by either

```text
∀φ
Eφ
```

produces a formula.

Takeuti states immediately after this clause that a variable of type `(0)` is
henceforth to be regarded as a special case of a variable of general type.

### 4.7 Quantification over functions (§2.9)

Let `f` be a free function of type `(n₁, ..., nᵢ)` occurring in a formula
`A`. Choose a bound function `p` of the same type which does not occur in `A`.
Replace all occurrences of `f` in `A` by `p`. Prefixing the result by either

```text
∀p
Ep
```

produces a formula.

Thus GLC has two syntactically distinct families of binders: binders for
variables and binders for functions.

### 4.8 Auxiliary notions (§§2.10–2.16)

Takeuti additionally defines:

- a variety of type `(0)` to be a **term** (§2.10);
- the singleton type `(n)` to be writable simply as `n` (§2.11);
- abbreviated display conventions for typed symbols (§2.12);
- the **outermost symbol** of a formula as the logical symbol added at its final
  construction stage, when one exists (§2.13);
- the **outermost variable** of an atomic formula as the variable used at its
  final construction stage (§2.14);
- the **outermost function** of a function-built variety analogously (§2.15);
- a syntactic notion of **normal formula** in §2.16.

The normal-form condition is recorded here but intentionally not encoded in the
current symbol prototype; it depends on the final recursive syntax.

## 5. Several notations (§3)

### 5.1 Indicated occurrences (§3.1)

An expression such as `A(α)` means that some occurrences of the free variable
`α` in `A` have been **indicated**. They need not be all occurrences. Takeuti
extends the notation to several free variables and to free functions, and uses
it to describe replacement at only the indicated occurrences.

This is meta-notation about figures, not a new formula constructor.

### 5.2 Functionals (§3.2)

Let `T(α¹, ..., αⁱ)` be a term with free variables

```text
α¹ : (n₁), ..., αⁱ : (nᵢ).
```

Choose bound variables `φ¹, ..., φⁱ` of the corresponding types which do not
occur in the original term. After replacing the indicated free variables by
those bound variables, the abstraction

```text
{φ¹, ..., φⁱ} T(φ¹, ..., φⁱ)
```

is called a **functional** of type

```text
(n₁ + 1, ..., nᵢ + 1).
```

The shape resembles the abstraction used to form higher-type varieties in
§2.6, but a functional abstracts from a **term**, whereas §2.6 abstracts from a
**formula** to create a variety.

### 5.3 Full indication (§3.3)

For a formula, variety, or functional written as `A(α)`, Takeuti says the
notation is of **full indication** exactly when every occurrence of `α` in `A`
is among the indicated occurrences.

Indication and full indication become important in §5, where Takeuti develops
his substitution machinery. We therefore postpone their Lean representation
until the binding and substitution experiments.

## 6. Formation-rule summary

The source-level constructors can be summarized as follows.

| Source clause | Inputs | Output |
| --- | --- | --- |
| §2.1 | free variable of type `(0)` | variety `(0)` |
| §2.2 | special variable of type `(0)` | variety `(0)` |
| §2.3 | free variable of shifted profile + matching varieties | formula |
| §2.4 | special variable of shifted profile + matching varieties | formula |
| §2.5 | free/special function of shifted profile + matching varieties | variety `(0)` |
| §2.6 | formula + abstraction of pairwise distinct free variables | higher-type variety |
| §2.7 | formula(s) | formula via `¬`, `∧`, `∨` |
| §2.8 | formula + variable replacement | formula via `∀` or `E` |
| §2.9 | formula + function replacement | formula via `∀` or `E` |
| §3.2 | term + abstraction of free variables | functional |

This table is intended to drive the binding prototypes in the next Milestone 1
step.

## 7. Decisions deliberately postponed

This specification does not decide:

- whether the final syntax will be intrinsically scoped;
- whether binders will use de Bruijn indices, a locally nameless method, or
  named syntax with alpha-equivalence;
- whether free/special source symbols should share the same identifier type;
- whether formulas, varieties, and functionals should be mutually inductive;
- how indicated occurrences should be represented;
- how Takeuti's later notion of *homologous* expressions will be related to the
  internal equality of Lean objects.

The next step is to implement a very small common fragment with competing
binding representations and compare how naturally they express §§2.6, 2.8,
2.9, and 3.2.
