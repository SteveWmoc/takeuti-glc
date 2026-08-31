# Syntax specification

## Status

This document records the **source-level** syntax conventions in §§1–3 of Gaisi Takeuti's 1953 paper *On a generalized logic calculus*. It is intended to remain readable independently of the Lean implementation.

Milestone 1 completed the source transcription and selected a locally nameless internal representation. M2.1 implemented the stable name, raw-syntax, and structural-scope layers in `TakeutiGLC/Syntax/Name.lean`, `Core.lean`, and `Scope.lean`; M2.2 adds the independent variable/function typing contexts and extrinsic type-formation judgments in `Typing.lean`.

The typing relation enforces profile compatibility and the type-formational content of §§2–3. It is deliberately not yet a complete source-figure recognizer: §§2.8–2.9 require the quantified free variable or function to occur in the premiss formula, and §3.2 depends on the partial-indication convention of §3.1. Those occurrence-sensitive conditions are the next Milestone 2 layer.

The primary source is included in this repository as [`Takeuti53.pdf`](../Takeuti53.pdf). The implementation design is recorded separately in [`syntax-design.md`](syntax-design.md).

## 1. Type conventions in the paper

### 1.1 The distinguished type `(0)`

Takeuti treats `(0)` separately. Variables of type `(0)` have no argument place (§1.1.1–§1.1.3). Varieties of type `(0)` are called **terms** (§2.10).

### 1.2 Nonzero profiles

A nonzero type has the form

```text
(n₁, ..., nᵢ)
```

where `i ≥ 1` and every displayed entry `nₖ` is a positive integer (§1.1.4–§1.1.6 and §1.2.1–§1.2.3). A symbol of this type has `i` argument places.

Takeuti permits the abbreviation `n` for the singleton type `(n)` (§2.11). Thus `(0)` remains the distinguished base type, while `(1)`, `(2)`, and so on are one-place higher types.

### 1.3 Argument levels

The formation rules are stated using a shifted profile

```text
(n₁ + 1, ..., nᵢ + 1).
```

In §§2.3–2.5, the `k`th argument place of a variable or function of this type is filled by a variety of singleton type `(nₖ)`:

```text
symbol type:     (n₁ + 1, ..., nᵢ + 1)
argument types:  (n₁),     ..., (nᵢ)
```

The same shift appears in abstraction. Section 2.6 forms a variety of type `(n₁ + 1, ..., nᵢ + 1)` by abstracting variables of types `(n₁), ..., (nᵢ)`. Section 3.2 assigns that same shifted type to a functional formed by abstracting indicated variable occurrences from a term.

### 1.4 Height

Section 5.1 later defines the height of a variable, function, variety, or functional of type `(n₁, ..., nᵢ)` as the largest displayed number. The distinguished type `(0)` therefore has height `0`.

## 2. Lean type-profile representation

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

The constructor `higher` stores predecessor levels rather than the positive entries displayed in the paper. This makes a nonzero profile nonempty by construction, prevents zero from occurring among its displayed entries, and makes the required argument types directly recoverable.

The stable representation provides `monotype`, `displayedEntries`, `argumentLevels`, `argumentTypes`, `arity`, and `height`.

## 3. Symbols (§1)

### 3.1 Variables (§1.1)

Takeuti distinguishes three classes of variables:

- **free variables**;
- **bound variables**;
- **special variables**.

All three classes occur at type `(0)` and at every nonzero profile `(n₁, ..., nᵢ)` with positive entries. A variable of nonzero profile has one argument place for each displayed entry.

A special variable of type `(1, ..., 1)` is called a **predicate**. Takeuti lists equality, order, and membership as special predicate symbols of type `(1, 1)`, using infix notation for them.

`TakeutiGLC/Syntax/Symbol.lean` retains this three-way classification as a historical/source layer. Its numerical `index` fields are opaque names, not binding indices.

### 3.2 Functions (§1.2)

Takeuti likewise distinguishes:

- **free functions**;
- **bound functions**;
- **special functions**.

The function symbols listed in §1.2 have only nonzero profiles. Special functions include addition and multiplication of type `(1, 1)`.

`FunctionProfile` stores only nonzero profiles, again in predecessor-level form. `FunctionSymbol` records the historical class, profile, and an opaque source name.

### 3.3 Logical symbols (§1.3)

Takeuti's five logical symbols are

```text
¬    ∧    ∨    ∀    E
```

where `E` is his existential-quantifier notation.

## 4. Varieties and formulas (§2)

Takeuti calls any row of symbols a **figure** and recursively defines varieties and formulas among figures.

### 4.1 Base varieties (§§2.1–2.2)

Every free variable of type `(0)` is a variety of type `(0)`, and every special variable of type `(0)` is a variety of type `(0)`.

Bound variables of type `(0)` are not introduced as standalone source varieties. Bound occurrences arise through the binding constructions below.

### 4.2 Atomic formulas from variables (§§2.3–2.4)

Let `α` be a free variable of type

```text
(n₁ + 1, ..., nᵢ + 1)
```

and let `Vₖ` be a variety of type `(nₖ)` for every `k`. Filling the argument places of `α` with the `Vₖ` produces a formula

```text
α[V₁, ..., Vᵢ].
```

The same rule applies to a special variable `σ` of that profile.

There is no parallel source formation clause headed directly by a bound variable name; bound occurrences are created by abstraction or quantification.

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

Bound functions are introduced by function quantification rather than by the source-level application clause itself.

### 4.4 Higher-type varieties by abstraction (§2.6)

Take pairwise distinct free variables

```text
α¹ : (n₁), ..., αⁱ : (nᵢ)
```

and a formula `A`. The selected free variables need not occur in `A`; an absent variable gives a vacuous abstraction position. Choose pairwise distinct bound variables

```text
φ¹ : (n₁), ..., φⁱ : (nᵢ)
```

which do not occur in `A`. Replace **every occurrence** of each `αᵏ` by the corresponding `φᵏ`, and prefix the abstraction braces

```text
{φ¹, ..., φⁱ}.
```

The result is a variety of type

```text
(n₁ + 1, ..., nᵢ + 1).
```

Thus §2.6 permits vacuous abstraction positions and therefore constant higher-type varieties.

### 4.5 Propositional connectives (§2.7)

If `A` and `B` are formulas, then

```text
¬A
A ∧ B
A ∨ B
```

are formulas.

### 4.6 Quantification over variables (§2.8)

Let `α` be a free variable of type `(n₁, ..., nᵢ)` occurring in a formula `A`. Choose a bound variable `φ` of the same type that does not occur in `A`, replace all occurrences of `α` by `φ`, and prefix either

```text
∀φ
Eφ
```

to obtain a formula.

Takeuti immediately notes that a variable of type `(0)` is henceforth regarded as a special case of a variable of general type.

### 4.7 Quantification over functions (§2.9)

Let `f` be a free function of type `(n₁, ..., nᵢ)` occurring in a formula `A`. Choose a bound function `p` of the same type that does not occur in `A`, replace all occurrences of `f` by `p`, and prefix either

```text
∀p
Ep
```

to obtain a formula.

GLC therefore has two syntactically distinct binder families: variable binders and function binders.

### 4.8 Auxiliary notions (§§2.10–2.16)

Takeuti additionally defines:

- a variety of type `(0)` to be a **term** (§2.10);
- singleton `(n)` to be writable as `n` (§2.11);
- abbreviated display conventions for typed symbols (§2.12);
- the **outermost symbol** of a formula (§2.13);
- the **outermost variable** of an atomic formula (§2.14);
- the **outermost function** of a function-built variety (§2.15);
- a syntactic notion of **normal formula** (§2.16).

The stable raw syntax now makes the outermost constructor notions directly expressible. The §2.16 normality predicate remains downstream of the core syntax bootstrap.

## 5. Several notations (§3)

### 5.1 Indicated occurrences (§3.1)

An expression such as `A(α)` means that some occurrences of the free variable `α` in `A` have been **indicated**. They need not be all occurrences. Takeuti extends this notation to several free variables and to free functions, and uses it to describe replacement at only the indicated occurrences.

This is metanotation about an existing figure, not a new formula constructor.

### 5.2 Functionals (§3.2)

Let `T(α¹, ..., αⁱ)` be a term with free variables

```text
α¹ : (n₁), ..., αⁱ : (nᵢ).
```

Choose bound variables `φ¹, ..., φⁱ` of the corresponding types that do not occur in the original term. Replace the **indicated occurrences** of the `αᵏ` by the corresponding bound variables. The abstraction

```text
{φ¹, ..., φⁱ} T(φ¹, ..., φⁱ)
```

is a **functional** of type

```text
(n₁ + 1, ..., nᵢ + 1).
```

This differs importantly from §2.6: §2.6 replaces every occurrence of each selected free variable, whereas §3.2 follows the partial-indication convention of §3.1. Unindicated occurrences remain free.

A functional abstracts from a **term**; §2.6 abstracts from a **formula** to produce a variety.

### 5.3 Full indication (§3.3)

For a formula, variety, or functional written as `A(α)`, Takeuti calls the notation **full indication** exactly when every occurrence of `α` in `A` is indicated.

Indication becomes central in §5 substitution. The stable raw syntax deliberately does not add an `indicated` constructor; Milestone 2 will instead introduce auxiliary occurrence-selection data usable both by §3.2 translation and §5 operations.

## 6. Formation-rule summary

| Source clause | Inputs | Output |
| --- | --- | --- |
| §2.1 | free variable of type `(0)` | variety `(0)` |
| §2.2 | special variable of type `(0)` | variety `(0)` |
| §2.3 | free variable of shifted profile + matching varieties | formula |
| §2.4 | special variable of shifted profile + matching varieties | formula |
| §2.5 | free/special function of shifted profile + matching varieties | variety `(0)` |
| §2.6 | formula + simultaneous abstraction of pairwise distinct free variables | higher-type variety |
| §2.7 | formula(s) | formula via `¬`, `∧`, `∨` |
| §2.8 | formula + variable replacement | formula via `∀` or `E` |
| §2.9 | formula + function replacement | formula via `∀` or `E` |
| §3.2 | term + abstraction of indicated free-variable occurrences | functional |

## 7. Implementation decisions already resolved

The following questions were open when this specification was first drafted and are now fixed by [`syntax-design.md`](syntax-design.md):

- the stable core is locally nameless;
- variable and function binders use independent de Bruijn namespaces;
- free and special internal names are kind-free, while the historical `VariableSymbol`/`FunctionSymbol` layer remains available for source transcription;
- `Variety`, `Formula`, and `Functional` are the raw syntactic categories;
- a term is a variety assigned type `(0)` by `Variety.HasType`;
- simultaneous abstraction blocks are represented as genuine nonempty blocks;
- scope correctness is an explicit structural proposition;
- typing uses independent lists of bound-variable types and bound-function profiles, with de Bruijn lookup in the appropriate list;
- function applications type only as `(0)`, while abstraction nodes receive the shifted profile determined by their binder levels;
- functional bodies are required by `Functional.HasType` to be terms;
- bound source names do not survive in the core, so admissible bound renaming is intended to disappear under source-to-core translation.

Still open at the current Milestone 2 boundary are:

- occurrence-sensitive source well-formedness for the non-vacuity requirements of §§2.8–2.9;
- the concrete occurrence-selection datatype for indication;
- the stable opening/closing and renaming APIs;
- the full formal correspondence between Takeuti's later homology relation and equality of translated core objects.
