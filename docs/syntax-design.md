# Milestone 1 syntax design

## Status

This document records the binding and syntax architecture selected at the end of Milestone 1. It is the normative design record for the stable core unless later metatheory exposes a concrete defect.

The design is no longer merely prospective: M2.1 has implemented the stable name, raw-syntax, and structural-scope layers in

```text
TakeutiGLC/Syntax/Name.lean
TakeutiGLC/Syntax/Core.lean
TakeutiGLC/Syntax/Scope.lean
```

The next implementation target is the extrinsic typing/well-formedness judgment for §§2–3. Renaming, occurrence selection, stable opening/closing, and §5 substitution remain downstream.

This decision was based on the source specification in [`syntax-spec.md`](syntax-spec.md) and the executable Milestone 1 experiments documented in [`binding-experiment.md`](binding-experiment.md) and [`opening-closing-experiment.md`](opening-closing-experiment.md).

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

The stable core now realizes that choice: raw indices may be dangling, while `Syntax/Scope.lean` supplies the structural invariant separately.

## 3. Historical layer versus core layer

`TakeutiGLC/Syntax/Symbol.lean` records Takeuti's historical classification:

- free, bound, and special variables;
- free, bound, and special functions;
- source profiles and opaque numerical names.

Those source objects are useful for stating the paper faithfully, but the internal syntax does not retain a redundant `kind` field on named occurrences. M1.3a showed why: a constructor labelled `freeVar` could otherwise carry a historical symbol tagged `bound`.

The stable core therefore uses kind-free names:

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
boundFunApp                bound function index
```

Historical bound names are used only while translating or presenting source notation; they are not part of the identity of a bound core occurrence.

## 4. Stable raw categories

The permanent raw syntax has three main categories:

- `Variety`;
- `Formula`;
- `Functional`.

A **term** is not a fourth raw category. Following §2.10, it will be a variety assigned type `(0)` by the typing judgment.

The implemented raw shape is intentionally simple and uses ordinary recursive argument lists:

```lean
mutual
  inductive Variety where
    | freeVar (name : VariableName)
    | specialVar (name : VariableName)
    | boundVar (index : Nat)
    | freeFunApp (name : FunctionName) (args : List Variety)
    | specialFunApp (name : FunctionName) (args : List Variety)
    | boundFunApp (index : Nat) (args : List Variety)
    | abstract
        (headLevel : Nat)
        (tailLevels : List Nat)
        (body : Formula)

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
  | abstract
      (headLevel : Nat)
      (tailLevels : List Nat)
      (body : Variety)
```

Constructor names may evolve as the metatheory grows, but the source-to-core distinctions represented here are architectural commitments.

## 5. Type profiles and typing

The shifted type-profile representation remains:

```text
zero                    ↔ (0)
higher n [n₂, ..., nᵢ] ↔ (n+1, n₂+1, ..., nᵢ+1)
```

The stored predecessor levels are exactly the levels required for argument places in §§2.3–2.6 and §3.2.

Typing is intentionally **extrinsic** at the current boundary. The planned contexts have the conceptual form

```text
variable context : List TypeProfile
function context : List FunctionProfile
```

and a bound de Bruijn index is typed by lookup in the appropriate context. Free and special names carry their own profiles.

The typing/well-formedness judgment must enforce the source formation rules:

- argument arity and profile compatibility;
- result type `(0)` for function applications;
- abstraction result profiles;
- the term condition on functional bodies;
- variable-quantifier profile lookup in the variable namespace;
- function-quantifier profile lookup in the function namespace.

Making this judgment explicit keeps the raw recursion simple and exposes Takeuti's own formation conditions instead of burying them inside dependent constructor types.

## 6. Structural well-scopedness

M2.1 implemented structural well-scopedness as inductive propositions rather than datatype indices.

At minimum the invariant tracks two depths:

```text
varDepth
funDepth
```

with these rules:

- a bound variable index `k` requires `k < varDepth`;
- a bound function index `k` requires `k < funDepth`;
- a variable quantifier increases only `varDepth`;
- a function quantifier increases only `funDepth`;
- an abstraction with `i` slots increases only `varDepth` by `i`;
- free and special names affect neither depth.

A closed core expression is well scoped at the empty two-depth scope.

The later typed judgment may imply structural scope, but retaining a lightweight scope proposition is useful for generic opening, closing, renaming, and substitution lemmas.

## 7. De Bruijn convention

A newly introduced unary binder occupies index `0` in its namespace. Existing indices at or beyond the insertion cutoff are shifted by one. Crossing a binder of the same namespace increments the cutoff; crossing a binder of the other namespace leaves it unchanged.

For a simultaneous Takeuti abstraction block

```text
{φ¹, ..., φⁱ}
```

the first displayed binder corresponds to block index `0`, the second to `1`, and so on. The block remains a single source-level binding construction. Repeated unary closing may be used internally as an implementation technique without claiming that Takeuti's syntax contains nested unary abstractions.

Vacuous abstraction slots are permitted, as required by §2.6.

## 8. Source-to-core correspondence

### 8.1 Variables of type `(0)` — §§2.1–2.2

A free source variable of type `(0)` becomes `Variety.freeVar` after erasing its historical `free` tag into a kind-free `VariableName`.

A special source variable of type `(0)` becomes `Variety.specialVar`.

A bound source variable name is never stored as a named core occurrence; inside its binder it becomes the de Bruijn index determined by the current variable environment.

### 8.2 Atomic formulas — §§2.3–2.4

Free and special higher-type variable applications become `Formula.atomFree` and `Formula.atomSpecial` respectively. If the head denotes a variable bound by an enclosing source binder, it becomes `Formula.atomBound`.

The future typing judgment checks that argument varieties have the types prescribed by the head profile.

### 8.3 Function application — §2.5

Applications of free and special functions become `freeFunApp` and `specialFunApp`. A function occurrence bound by an enclosing function quantifier becomes `boundFunApp`.

The typing judgment will require matching argument profiles and result type `(0)`.

### 8.4 Higher-type abstraction — §2.6

For

```text
{φ¹, ..., φⁱ} A
```

the printed bound names are used only while translating `A`. The variable environment is extended by an `i`-slot block with `φ¹` at index `0`, `φ²` at index `1`, and so on.

Section 2.6 replaces **every occurrence** of the selected free variables. A slot may nevertheless be vacuous if its selected free variable does not occur in `A`.

The core node stores predecessor levels and the translated body, not the source binder names. Its type is `(n₁+1, ..., nᵢ+1)` according to the future typing judgment.

### 8.5 Propositional connectives — §2.7

`¬`, `∧`, and `∨` translate structurally to `neg`, `conj`, and `disj`.

### 8.6 Variable quantification — §2.8

For `∀φ A` or `Eφ A`, the binder profile is stored on the quantifier node. The source name extends only the variable environment at index `0`; the function environment is unchanged.

### 8.7 Function quantification — §2.9

For `∀p A` or `Ep A`, the binder profile is stored on the quantifier node. The source name extends only the function environment at index `0`; the variable environment is unchanged.

### 8.8 Functionals — §3.2

A functional

```text
{φ¹, ..., φⁱ} T(α¹, ..., αⁱ)
```

uses the same **block-index convention** as §2.6 but a different occurrence-selection rule.

Section 3.1 permits only some occurrences of a free variable to be indicated. Section 3.2 abstracts exactly those indicated occurrences. Therefore the source-to-core translation must receive auxiliary occurrence-selection data:

- indicated occurrences of `αᵏ` become the corresponding block index;
- unindicated occurrences of the same free variable remain free.

Full indication is the special case in which every occurrence is selected.

The body translates as a `Variety`; the typing judgment additionally requires it to be a term, i.e. to have type `(0)`.

## 9. Indicated occurrences

Indication is metasyntactic data, not a raw syntax constructor. The stable core therefore has no `indicated` node.

Milestone 2 must introduce an auxiliary occurrence-selection representation before a faithful executable source translation of §3.2 and before §5 substitution. Candidate encodings include occurrence paths, stable occurrence identifiers, a selection predicate, or an operation parameter. The exact representation is still open.

The architectural constraint is fixed: indication is an input to translations and operations, not part of ordinary raw syntax identity.

## 10. Homology and alpha-equivalence

The core stores no bound source names. Consequently, well-formed source expressions that differ only by admissible renaming of bound variables or bound functions should translate to the same core object.

When the historical source translation becomes executable, the intended theorem has the shape

```text
homologous source expressions  ->  equal core translations
```

The project should not introduce a quotient by alpha-equivalence into ordinary core syntax unless later source details force it.

## 11. Current Milestone 2 module plan

Implemented:

```text
TakeutiGLC/Syntax/Name.lean
TakeutiGLC/Syntax/Core.lean
TakeutiGLC/Syntax/Scope.lean
```

Expected next modules, with exact names still adjustable:

```text
TakeutiGLC/Syntax/Typing.lean
TakeutiGLC/Syntax/Occurrence.lean
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
7. initially extrinsic typing;
8. terms as type-`(0)` varieties rather than a raw fourth category;
9. indicated occurrences as auxiliary metasyntactic data;
10. bound renaming erased at the source-to-core boundary.
