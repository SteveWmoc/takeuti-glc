# Milestone 1 syntax design

## Status

This document closes Milestone 1 by recording the binding representation chosen
for the stable GLC syntax and the intended correspondence with Takeuti's
source-level notation.

The decision is based on the source specification in `docs/syntax-spec.md` and
the two executable experiments in `docs/binding-experiment.md` and
`docs/opening-closing-experiment.md`. It is a design record, not yet the final
syntax API. Milestone 2 will turn this design into the stable syntax,
well-scopedness, renaming, and substitution library.

## 1. Decision

The stable core will use **locally nameless syntax with two independent de
Bruijn namespaces**.

- Free and special variables keep opaque source names.
- Free and special functions keep opaque source names.
- Bound variable occurrences are natural-number de Bruijn indices.
- Bound function occurrences are natural-number de Bruijn indices in a
  separate namespace.
- Variable binders affect only the variable namespace.
- Function binders affect only the function namespace.
- Takeuti's abstractions in §§2.6 and 3.2 bind a nonempty block of variables in
  one step.

The stable core will therefore follow the shape of the current locally nameless
prototype rather than the intrinsically scoped `Fin`-indexed prototype.

This choice is specifically a choice about **binding and scope
representation**. It does not commit the project to making every typing
condition intrinsic in the datatype.

## 2. Why locally nameless

The intrinsically scoped experiment establishes a genuine advantage: an
out-of-scope bound occurrence is unrepresentable. However, the opening/closing
experiment shows that this invariant is paid for in almost every syntax
transformation:

- source and target types change when a binder is crossed;
- cutoff proofs accompany ordinary recursive clauses;
- bound indices require `Fin` insertion and removal;
- abstraction blocks create arithmetic casts between definitionally different
  scope expressions;
- the indexed mutual syntax requires a custom recursive argument spine rather
  than ordinary `List` arguments.

Takeuti's later development is dominated by transformations of syntax,
especially §5 substitution, §7 restriction, and §8 type elevation. Carrying
those dependent scope changes throughout the metatheory would make the binding
representation an active proof burden in precisely the parts of the paper where
we want the formalization to follow the mathematical recursion closely.

The locally nameless prototype leaves raw dangling indices representable, but
its opening and closing operations are ordinary recursive functions on a stable
datatype. Scope correctness can instead be isolated in a reusable
well-scopedness layer and proved preserved by the transformations that matter.

The design therefore prefers a simpler transformation language plus explicit
scope invariants over stronger raw datatypes plus pervasive dependent
bookkeeping.

## 3. Why not literal named syntax

A literal transcription with source names for bound variables and functions
would preserve the printed notation most directly, but it would make bound
renaming semantically visible in the raw syntax. Takeuti's later notion of
homologous expressions would then require either a pervasive alpha-equivalence
relation, quotients, or repeated renaming lemmas.

Both Milestone 1 binding prototypes avoid that problem by eliminating bound
source names from the core. The stable design retains that feature.

Historical bound names remain relevant only while translating or presenting
Takeuti's source notation; they are not part of the internal identity of a bound
occurrence.

## 4. Historical layer versus core layer

`TakeutiGLC/Syntax/Symbol.lean` records Takeuti's source-level classification:

- free, bound, and special variables;
- free, bound, and special functions;
- source profiles and opaque numerical names.

That historical layer is useful for faithfully describing the paper, but the
stable core must not store a redundant source `kind` tag inside an occurrence.
Milestone 1.3a showed that doing so permits contradictory raw objects such as a
constructor labelled `freeVar` carrying a source symbol tagged `bound`.

The core therefore uses kind-free names of the following conceptual shape:

```lean
structure VariableName where
  profile : TypeProfile
  index : Nat

structure FunctionName where
  profile : FunctionProfile
  index : Nat
```

The occurrence constructor carries the remaining role information:

```text
freeVar / atomFree       free variable occurrence
specialVar / atomSpecial special variable occurrence
boundVar / atomBound     bound variable index

freeFunApp               free function occurrence
specialFunApp            special function occurrence
boundFunApp               bound function index
```

The experimental `TakeutiGLC/Experiment/Names.lean` is the prototype for this
separation. Milestone 2 should move the stable version into the syntax layer
rather than importing the experiment as permanent infrastructure.

## 5. Raw core categories

The permanent raw syntax should retain three main syntactic categories:

- `Variety`;
- `Formula`;
- `Functional`.

A **term** is not a fourth raw category. Following §2.10, it is a variety whose
type is `(0)` according to the well-formedness/type judgment.

The core should use ordinary recursive argument lists. The intended raw shape
is essentially:

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

This is a design sketch, not an API promise. Milestone 2 may adjust constructor
names or package the nonempty block profile more directly, provided the
source-to-core correspondence below is preserved.

## 6. Type profiles and typing

The shifted `TypeProfile` representation chosen earlier in Milestone 1 remains
in force:

```text
zero                    ↔ (0)
higher n [n₂, ..., nᵢ] ↔ (n+1, n₂+1, ..., nᵢ+1)
```

The stored predecessor levels are exactly the levels required for the argument
places in §§2.3–2.6 and §3.2.

Binding will be locally nameless, but the entire syntax will **not** initially
be made intrinsically typed. Instead, Milestone 2 should define an extrinsic
well-formedness/type judgment carrying the profiles of currently bound
variables and functions.

Conceptually, the contexts have the form

```text
variable context : List TypeProfile
function context : List FunctionProfile
```

and a bound index is typed by looking it up in the appropriate context.
Free/special names carry their own profiles. The judgment then checks the exact
formation conditions from §§2–3: argument arities and types, abstraction
profiles, termhood of functional bodies, and the two quantifier families.

Keeping typing extrinsic at this stage has two advantages. It preserves the
simple recursive raw syntax selected by the binding experiments, and it lets us
formalize Takeuti's own formation conditions explicitly rather than hiding them
inside dependent constructor types before §5 substitution has been tested.

## 7. Local closure / well-scopedness

Raw locally nameless syntax can contain dangling bound indices. The stable
library must therefore define a structural scope judgment before substantial
metatheory begins.

At minimum it should track two depths:

```text
WellScoped variety/formula/functional varDepth funDepth
```

with the following clauses.

- A bound variable index `k` is valid exactly when `k < varDepth`.
- A bound function index `k` is valid exactly when `k < funDepth`.
- A variable quantifier checks its body at `varDepth + 1` and unchanged
  `funDepth`.
- A function quantifier checks its body at unchanged `varDepth` and
  `funDepth + 1`.
- An abstraction with `i` variable slots checks its body at
  `varDepth + i` and unchanged `funDepth`.
- Free and special names do not affect either depth.

A closed core expression is well scoped at depths `(0, 0)`.

The eventual typed well-formedness judgment may subsume much of this
information through profile contexts, but retaining a lightweight scope
predicate is useful for stating generic opening/closing and substitution lemmas
without carrying typing hypotheses unnecessarily.

## 8. De Bruijn convention

The permanent convention follows the M1.3b experiment.

A newly introduced single binder occupies index `0` in its namespace. Existing
indices at or beyond the insertion cutoff are shifted by one. Crossing a binder
of the same namespace increments the cutoff; crossing a binder of the other
namespace leaves it unchanged.

For a simultaneous Takeuti abstraction block

```text
{φ¹, ..., φⁱ}
```

the first displayed binder corresponds to index `0`, the second to index `1`,
and so on within that block. The block remains a single source-level binding
construction; using repeated single-name closing internally is an
implementation technique, not a claim that Takeuti's syntax contains nested
unary abstractions.

Vacuous abstraction slots are permitted, as required by §2.6.

## 9. Source-to-core correspondence

This section states the intended translation at the design level. A later
source AST, if introduced, should realize this correspondence explicitly.

### 9.1 Variables of type `(0)` — §§2.1–2.2

A free source variable of type `(0)` translates to `Variety.freeVar` after its
historical `free` tag is erased into a kind-free `VariableName`.

A special source variable of type `(0)` translates to `Variety.specialVar` in
the same way.

A source bound variable name is never translated as a named core occurrence;
inside the scope of its binder it translates to the de Bruijn index determined
by the current variable environment.

### 9.2 Atomic formulas — §§2.3–2.4

A free higher-type variable applied to matching varieties translates to
`Formula.atomFree name args`.

A special higher-type variable applied to matching varieties translates to
`Formula.atomSpecial name args`.

If the source occurrence denotes a variable bound by an enclosing Takeuti
binder, the head translates instead to `Formula.atomBound index args`.

The well-formedness judgment, not the raw constructor, verifies that the
argument varieties have the types prescribed by the head profile.

### 9.3 Function application — §2.5

Applications of free and special functions translate to `freeFunApp` and
`specialFunApp` respectively. A source function occurrence bound by an enclosing
function quantifier translates to `boundFunApp`.

A well-formed application has result type `(0)` and argument varieties matching
the predecessor levels stored in the function profile.

### 9.4 Higher-type abstraction — §2.6

For

```text
{φ¹, ..., φⁱ} A
```

the source bound names `φ¹, ..., φⁱ` are used only while translating `A`.
The variable environment is extended by an `i`-slot block with `φ¹` at index
`0`, `φ²` at index `1`, and so on. The core node stores the predecessor levels
`n₁, ..., nᵢ` and the translated body, but not the printed bound names.

The resulting variety receives type

```text
(n₁+1, ..., nᵢ+1)
```

through the typing judgment. A binder may be unused in the body.

### 9.5 Propositional connectives — §2.7

`¬`, `∧`, and `∨` translate structurally to `neg`, `conj`, and `disj`.

### 9.6 Variable quantification — §2.8

For `∀φ A` or `Eφ A`, the binder profile is stored on the core quantifier. The
source name `φ` extends only the variable environment at index `0` while `A` is
translated. The function environment is unchanged.

The resulting core node is `allVar profile body` or
`existsVar profile body`.

### 9.7 Function quantification — §2.9

For `∀p A` or `Ep A`, the binder profile is stored on the core quantifier. The
source name `p` extends only the function environment at index `0`; the variable
environment is unchanged.

The resulting core node is `allFun profile body` or
`existsFun profile body`.

### 9.8 Functionals — §3.2

A functional

```text
{φ¹, ..., φⁱ} T(α¹, ..., αⁱ)
```

uses the same **block-index convention** as §2.6, but not the same occurrence
replacement rule. Section 3.1 allows the notation `T(α¹, ..., αⁱ)` to indicate
only selected occurrences of each free variable, and §3.2 abstracts exactly
those indicated occurrences. The source-to-core translation must therefore
receive the auxiliary occurrence selection together with the source term.

While translating the body, the block environment assigns `φ¹` index `0`,
`φ²` index `1`, and so on. An indicated occurrence of `αᵏ` is translated to the
corresponding bound-variable index. An **unindicated** occurrence of that same
free source variable remains a free occurrence in the resulting core body.
Thus partial indication is preserved; full indication is only the special case
where every occurrence of each selected free variable is converted.

The body translates as a `Variety`, and the typing judgment additionally
requires that body to be a term, i.e. a variety of type `(0)`. The functional
receives type `(n₁+1, ..., nᵢ+1)` from the stored predecessor levels.

## 10. Indicated occurrences

Takeuti's notation `A(α)` in §3.1 marks selected occurrences; it is
meta-notation rather than another formula constructor. The stable raw syntax
will therefore **not** contain an `indicated` constructor.

Indication is nevertheless required already for the faithful source-to-core
translation of §3.2 functionals, not only later for §5 substitution. Milestone
2 should therefore introduce auxiliary occurrence-selection data over an
existing source or raw expression—for example occurrence positions, stable
occurrence identifiers, a selection predicate, or an operation parameter.
The representation must permit partial indication, including the possibility
that only some occurrences of a named free variable are selected, as well as
the full indication of §3.3.

The same auxiliary mechanism can then be reused by §5 substitution. This design
fixes the architectural boundary—indication is an input to translations and
operations, not a raw syntax constructor—without prematurely choosing the final
occurrence-selection datatype.

## 11. Homology and alpha-equivalence

The core representation has no bound source names. Consequently, two
well-formed source expressions that differ only by admissible renaming of bound
variables or bound functions should translate to the same core object.

This is the intended formal relationship between Takeuti's bound-name
insensitivity and the internal representation. When the historical source
translation is made executable, the key theorem should have the shape

```text
homologous source expressions  ->  equal core translations.
```

The project should not introduce a quotient by alpha-equivalence into ordinary
core syntax unless later source details force it. Milestone 1 gives no evidence
that such a quotient is necessary.

## 12. Stable-module plan for Milestone 2

The experiments remain useful evidence, but permanent metatheory should not
live under `TakeutiGLC/Experiment`.

A natural first Milestone 2 layout is:

```text
TakeutiGLC/Syntax/Name.lean
TakeutiGLC/Syntax/Core.lean
TakeutiGLC/Syntax/Scope.lean
TakeutiGLC/Syntax/OpenClose.lean
TakeutiGLC/Syntax/Renaming.lean
TakeutiGLC/Syntax/Substitution.lean
```

The exact file split may change. The important architectural boundary is that
source notation and experiments remain separate from the stable core and its
metatheory.

## 13. Milestone 1 conclusion

Milestone 1 has now fixed the following design points.

1. Takeuti profiles use the shifted predecessor-level representation already
   implemented in `TypeProfile` and `FunctionProfile`.
2. Historical free/bound/special symbol classes are retained for source
   description but erased appropriately at the core boundary.
3. The core binding representation is locally nameless.
4. Variable and function binders use independent de Bruijn namespaces.
5. Higher-type abstractions are genuine nonempty variable-binding blocks.
6. Scope validity is an explicit structural invariant rather than a datatype
   index.
7. Typing is initially an extrinsic context-indexed judgment.
8. Terms are type-`(0)` varieties, not a separate raw syntax category.
9. Indicated occurrences are auxiliary metasyntactic data used by translation
   and later substitution operations, not raw syntax.
10. Bound renaming should disappear under source-to-core translation, making
    ordinary core equality the intended target for Takeuti's homology.

With these decisions recorded, the project can enter Milestone 2 without
reopening the basic binding architecture unless §5 exposes a concrete defect.