# Milestone 1 syntax design

## Status

This document records the binding and syntax architecture selected at the end of Milestone 1 and the permanent implementation choices that have since been realized in Milestone 2. It is the normative design record for the stable core unless later metatheory exposes a concrete defect.

M2.1–M2.3 have implemented the stable name, raw-syntax, structural-scope, typing, and occurrence layers in

```text
TakeutiGLC/Syntax/Name.lean
TakeutiGLC/Syntax/Core.lean
TakeutiGLC/Syntax/Scope.lean
TakeutiGLC/Syntax/Typing.lean
TakeutiGLC/Syntax/Occurrence.lean
```

The next implementation target is stable opening/closing, followed by renaming and weakening. The occurrence layer already supplies the auxiliary selection data needed for §3.2 partial abstraction and later §5 substitution.

This design is based on the source specification in [`syntax-spec.md`](syntax-spec.md) and the executable Milestone 1 experiments documented in [`binding-experiment.md`](binding-experiment.md) and [`opening-closing-experiment.md`](opening-closing-experiment.md).

## 1. Binding decision

The stable core uses **locally nameless syntax with two independent de Bruijn namespaces**.

- Free and special variables keep opaque names.
- Free and special functions keep opaque names.
- Bound variable occurrences are natural-number de Bruijn indices.
- Bound function occurrences are natural-number de Bruijn indices in a separate namespace.
- Variable binders affect only the variable namespace.
- Function binders affect only the function namespace.
- Takeuti's abstractions in §§2.6 and 3.2 bind a nonempty block of variables in one step.

This is a choice about binding and scope representation. It does **not** make the whole syntax intrinsically typed.

## 2. Why locally nameless

The intrinsically scoped experiment had a genuine advantage: an out-of-scope bound occurrence was unrepresentable. The M1.3b opening/closing experiment showed the price of that invariant, however:

- source and target datatype indices changed whenever a binder was crossed;
- ordinary recursive clauses carried cutoff proofs;
- bound indices required explicit `Fin` insertion and removal;
- abstraction blocks created arithmetic casts between definitionally different scope expressions;
- Lean's positivity checker forced a custom recursive argument spine instead of ordinary `List` arguments.

Takeuti's later development is dominated by syntax transformations—especially §5 substitution, §7 restriction, and §8 type elevation. The project therefore prefers a stable raw datatype plus explicit scope invariants over stronger raw datatypes plus pervasive dependent bookkeeping.

Raw indices may consequently dangle. `Syntax/Scope.lean` supplies the structural invariant separately.

## 3. Historical layer versus core layer

`TakeutiGLC/Syntax/Symbol.lean` records Takeuti's historical classification into free, bound, and special variables/functions. These source objects are useful for faithful transcription, but the internal syntax does not retain a redundant `kind` field on named occurrences.

The stable core instead uses kind-free names:

```lean
structure VariableName where
  profile : TypeProfile
  index : Nat

structure FunctionName where
  profile : FunctionProfile
  index : Nat
```

The occurrence constructor supplies the role:

```text
freeVar / atomFree        free variable occurrence
specialVar / atomSpecial  special variable occurrence
boundVar / atomBound      bound variable index

freeFunApp                free function occurrence
specialFunApp             special function occurrence
boundFunApp               bound function index
```

Historical bound names are used only while translating or presenting source notation; they are not part of the identity of a bound core occurrence.

## 4. Stable raw categories

The permanent raw syntax has three main categories:

- `Variety`;
- `Formula`;
- `Functional`.

A **term** is not a fourth raw category. Following §2.10, it is a variety assigned type `(0)` by the typing judgment.

The stable shape is deliberately recursive and ordinary:

```lean
mutual
  inductive Variety where
    | freeVar (name : VariableName)
    | specialVar (name : VariableName)
    | boundVar (index : Nat)
    | freeFunApp (name : FunctionName) (args : List Variety)
    | specialFunApp (name : FunctionName) (args : List Variety)
    | boundFunApp (index : Nat) (args : List Variety)
    | abstract (headLevel : Nat) (tailLevels : List Nat) (body : Formula)

  inductive Formula where
    | atomFree (name : VariableName) (args : List Variety)
    | atomSpecial (name : VariableName) (args : List Variety)
    | atomBound (index : Nat) (args : List Variety)
    | neg (body : Formula)
    | conj (left right : Formula)
    | disj (left right : Formula)
    | allVar (profile : TypeProfile) (body : Formula)
    | existsVar (profile : TypeProfile) (body : Formula)
    | allFun (profile : FunctionProfile) (body : Formula)
    | existsFun (profile : FunctionProfile) (body : Formula)
end

inductive Functional where
  | abstract (headLevel : Nat) (tailLevels : List Nat) (body : Variety)
```

Constructor names may evolve as the metatheory grows, but the represented source distinctions are architectural commitments.

## 5. Type profiles and typing

The shifted type-profile representation remains

```text
zero                    ↔ (0)
higher n [n₂, ..., nᵢ] ↔ (n+1, n₂+1, ..., nᵢ+1).
```

The stored predecessor levels are exactly the levels required for argument places in §§2.3–2.6 and §3.2.

Typing is **extrinsic**. `TakeutiGLC/Syntax/Typing.lean` implements independent lists of bound-variable types and bound-function profiles. The first element is de Bruijn index `0`; variable quantifiers extend only the variable context, function quantifiers extend only the function context, and an abstraction block prepends all of its variable types in display order.

The implemented judgments are

```text
Variety.HasType
Formula.WellFormed
VarietiesHaveTypes
Functional.HasType
```

They enforce base-variable typing, nonzero atomic heads, bound-index lookup, argument-profile compatibility, result type `(0)` for function applications, abstraction result profiles, independent binder contexts, and the term condition on functional bodies.

`Variety.IsTerm` is exactly `Variety.HasType ... .zero`, implementing §2.10.

Typing is intentionally separated from Takeuti's occurrence-sensitive conditions. M2.3 now layers the §§2.8–2.9 non-vacuity requirement on top of typing rather than baking it into the type relation.

## 6. Structural well-scopedness

M2.1 implemented structural well-scopedness as inductive propositions rather than datatype indices. The invariant tracks

```text
varDepth
funDepth
```

with the expected rules:

- a bound variable index `k` requires `k < varDepth`;
- a bound function index `k` requires `k < funDepth`;
- a variable quantifier increases only `varDepth`;
- a function quantifier increases only `funDepth`;
- an abstraction with `i` slots increases only `varDepth` by `i`;
- free and special names affect neither depth.

A closed core expression is well scoped at the empty two-depth scope. `TypingContext.scope` forgets stored profiles and retains exactly these two lengths.

A later metatheory lemma should prove that typing implies structural well-scopedness. The lightweight scope proposition remains useful because opening, closing, renaming, and substitution often need scope preservation independently of typing.

## 7. De Bruijn convention

A newly introduced unary binder occupies index `0` in its namespace. Existing indices at or beyond the insertion cutoff are shifted by one. Crossing a binder of the same namespace increments the cutoff; crossing a binder of the other namespace leaves it unchanged.

For a simultaneous Takeuti abstraction block

```text
{φ¹, ..., φⁱ}
```

the first displayed binder corresponds to block index `0`, the second to `1`, and so on. The block remains a single source-level binding construction. Repeated unary operations may be used internally without claiming that Takeuti's syntax contains nested unary abstractions.

Vacuous abstraction slots are permitted, as required by §2.6.

## 8. Source-to-core correspondence

### 8.1 Variables of type `(0)` — §§2.1–2.2

A free source variable of type `(0)` becomes `Variety.freeVar`; a special source variable becomes `Variety.specialVar`. Bound source names are not stored as named core occurrences.

### 8.2 Atomic formulas — §§2.3–2.4

Free and special higher-type variable applications become `Formula.atomFree` and `Formula.atomSpecial`. A variable bound by an enclosing source binder becomes `Formula.atomBound`. `Formula.WellFormed` checks the head profile and argument types.

### 8.3 Function application — §2.5

Applications of free and special functions become `freeFunApp` and `specialFunApp`; bound functions become `boundFunApp`. `Variety.HasType` requires matching argument profiles and assigns every such application type `(0)`.

### 8.4 Higher-type abstraction — §2.6

For

```text
{φ¹, ..., φⁱ} A
```

the printed bound names exist only during source translation. The variable environment is extended by an `i`-slot block with `φ¹` at index `0`, `φ²` at index `1`, and so on.

Section 2.6 replaces **every occurrence** of each selected free variable. A slot may nevertheless be vacuous if its selected variable does not occur in `A`.

The core node stores predecessor levels and the translated body. `Variety.HasType` assigns the shifted result profile when the body is well formed under the block-extended context.

### 8.5 Propositional connectives — §2.7

`¬`, `∧`, and `∨` translate structurally to `neg`, `conj`, and `disj`.

### 8.6 Variable quantification — §2.8

The binder profile is stored on the quantifier node and the source bound name disappears into the variable de Bruijn namespace. `Formula.WellFormed` checks the body under the extended typing context.

M2.3 adds `Formula.UsesInnermostVariableBinder`: after closing, the source requirement that the quantified free variable actually occurred is represented by use of the newly introduced variable index `0`, with the expected cutoff shifts under nested variable binders and abstraction blocks.

### 8.7 Function quantification — §2.9

The binder profile is stored on the function quantifier and only the function namespace is extended. `Formula.UsesInnermostFunctionBinder` analogously records the source non-vacuity requirement, shifting only across nested function binders.

`QuantifierSideConditions` propagates these requirements through nested syntax, and `WellFormedWithNonvacuousQuantifiers` combines them with the M2.2 typing layer.

### 8.8 Functionals — §3.2

A functional

```text
{φ¹, ..., φⁱ} T(α¹, ..., αⁱ)
```

uses the same **block-index convention** as §2.6 but a different occurrence-selection rule. Section 3.1 allows only some occurrences of a free variable to be indicated, and §3.2 abstracts exactly those indicated occurrences. Unindicated occurrences of the same free variable remain free.

The body translates as a `Variety`; `Functional.HasType` requires it to have type `(0)` under the block-extended variable context and assigns the corresponding shifted profile.

Stable closing will consume the M2.3 occurrence selections to perform this partial abstraction.

## 9. Indicated occurrences

Indication is metasyntactic data, not a raw syntax constructor. M2.3 makes this architectural decision executable.

`OccurrenceStep` records one structural navigation step and

```text
OccurrencePath := List OccurrenceStep
```

addresses one particular occurrence. The path vocabulary distinguishes argument positions, abstraction bodies, unary bodies, and the left/right branches of binary connectives. Resolution functions return the free variable or free function found at a path, or `none` for an invalid path or a path that does not end at an occurrence of the requested class.

Two finite selection structures represent §3.1 notation:

```text
VariableOccurrenceSelection
FunctionOccurrenceSelection
```

Each stores one free name and a finite set of occurrence paths. A `ValidFor...` predicate requires every selected path to resolve to that name. `FullyIndicates...` adds the converse condition that every occurrence of the name appears in the selection, formalizing §3.3.

This representation has three useful properties:

1. two occurrences of the same free name remain distinguishable;
2. invalid indication data is rejected by an explicit validity predicate rather than contaminating raw syntax;
3. the same selection mechanism can be consumed by §3.2 closing and later §5 indicated replacement.

The finite set is auxiliary metadata. It is not part of ordinary `Variety`, `Formula`, or `Functional` equality.

## 10. Homology and alpha-equivalence

The core stores no bound source names. Consequently, well-formed source expressions that differ only by admissible renaming of bound variables or bound functions should translate to the same core object.

When the historical source translation becomes executable, the intended theorem has the shape

```text
homologous source expressions  ->  equal core translations.
```

The project should not introduce a quotient by alpha-equivalence into ordinary core syntax unless later source details force it.

## 11. Current Milestone 2 module plan

Implemented:

```text
TakeutiGLC/Syntax/Name.lean
TakeutiGLC/Syntax/Core.lean
TakeutiGLC/Syntax/Scope.lean
TakeutiGLC/Syntax/Typing.lean
TakeutiGLC/Syntax/Occurrence.lean
```

Expected next modules, with exact names still adjustable:

```text
TakeutiGLC/Syntax/OpenClose.lean
TakeutiGLC/Syntax/Renaming.lean
TakeutiGLC/Syntax/Substitution.lean
```

Permanent metatheory should not depend on the experimental modules except where an explicit comparison theorem is useful.

## 12. Design commitments

The project currently treats the following as fixed unless later proof work supplies a concrete reason to revisit them:

1. shifted predecessor-level type profiles;
2. historical symbol classes separated from internal names;
3. locally nameless binding;
4. independent variable and function de Bruijn namespaces;
5. genuine nonempty simultaneous variable-abstraction blocks;
6. explicit structural well-scopedness rather than scope-indexed datatypes;
7. extrinsic typing with independent variable/function contexts;
8. terms as type-`(0)` varieties rather than a raw fourth category;
9. indicated occurrences as finite auxiliary structural-path selections;
10. quantifier non-vacuity represented by use of the newly introduced de Bruijn binder;
11. bound renaming erased at the source-to-core boundary.
