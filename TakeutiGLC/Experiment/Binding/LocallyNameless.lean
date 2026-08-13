import TakeutiGLC.Syntax.Symbol

/-!
# Binding experiment: locally nameless syntax

This file is the locally nameless counterpart to
`TakeutiGLC.Experiment.DeBruijn`. Free and special source symbols retain opaque
names, while bound variable and function occurrences are represented by raw
de Bruijn indices.

Unlike the intrinsically scoped prototype, raw syntax is not indexed by context
depths. This keeps the recursive datatype stable across binders, but dangling
bound references are representable and must eventually be excluded by a local
closure / well-scopedness judgment.

As with the de Bruijn prototype, the experiment records binder profiles but does
not yet enforce all of Takeuti's typing side conditions.
-/

namespace TakeutiGLC.Experiment.LocallyNameless

/-- Number of variables bound by a nonempty Takeuti abstraction block. -/
def blockSize (tailLevels : List Nat) : Nat := tailLevels.length + 1

/-- Resulting Takeuti type of an abstraction block with predecessor levels. -/
def abstractionProfile (headLevel : Nat) (tailLevels : List Nat) : TypeProfile :=
  .higher headLevel tailLevels

mutual

/-- Raw locally nameless varieties. -/
inductive Variety where
  | freeVar (symbol : VariableSymbol)
  | specialVar (symbol : VariableSymbol)
  | boundVar (index : Nat)
  | freeFunApp (symbol : FunctionSymbol) (args : List Variety)
  | specialFunApp (symbol : FunctionSymbol) (args : List Variety)
  | boundFunApp (index : Nat) (args : List Variety)
  | abstract
      (headLevel : Nat)
      (tailLevels : List Nat)
      (body : Formula)

/-- Raw locally nameless formulas. -/
inductive Formula where
  | atomFree (symbol : VariableSymbol) (args : List Variety)
  | atomSpecial (symbol : VariableSymbol) (args : List Variety)
  | atomBound (index : Nat) (args : List Variety)
  | neg (body : Formula)
  | conj (left right : Formula)
  | disj (left right : Formula)
  | allVar (profile : TypeProfile) (body : Formula)
  | existsVar (profile : TypeProfile) (body : Formula)
  | allFun (profile : FunctionProfile) (body : Formula)
  | existsFun (profile : FunctionProfile) (body : Formula)

end

/-- Raw locally nameless functionals. -/
inductive Functional where
  | abstract
      (headLevel : Nat)
      (tailLevels : List Nat)
      (body : Variety)

/--
The two independent binder depths needed to interpret raw bound indices.
A complete locally nameless development would define local closure recursively
for varieties, formulas, and functionals relative to a value of this structure.
-/
structure Scope where
  varDepth : Nat
  funDepth : Nat
deriving DecidableEq, Repr

namespace Scope

/-- Enter one variable quantifier. -/
def underVar (scope : Scope) : Scope :=
  { scope with varDepth := Nat.succ scope.varDepth }

/-- Enter one function quantifier. -/
def underFun (scope : Scope) : Scope :=
  { scope with funDepth := Nat.succ scope.funDepth }

/-- Enter a nonempty variable-abstraction block. -/
def underBlock (scope : Scope) (tailLevels : List Nat) : Scope :=
  { scope with varDepth := blockSize tailLevels + scope.varDepth }

end Scope

/-- A raw bound-variable index is valid at a given scope when it is in range. -/
def BoundVariableInScope (scope : Scope) (index : Nat) : Prop :=
  index < scope.varDepth

/-- A raw bound-function index is valid at a given scope when it is in range. -/
def BoundFunctionInScope (scope : Scope) (index : Nat) : Prop :=
  index < scope.funDepth

/--
A deliberately dangling term. Its existence demonstrates the proof obligation
that the locally nameless representation moves out of the datatype itself.
-/
def danglingVariable : Variety := .boundVar 0

/-- The analogous dangling bound-function application. -/
def danglingFunction : Variety := .boundFunApp 0 []

@[simp] theorem boundVariable_not_in_empty_scope (index : Nat) :
    ¬ BoundVariableInScope ⟨0, 0⟩ index := by
  simp [BoundVariableInScope]

@[simp] theorem boundFunction_not_in_empty_scope (index : Nat) :
    ¬ BoundFunctionInScope ⟨0, 0⟩ index := by
  simp [BoundFunctionInScope]

end TakeutiGLC.Experiment.LocallyNameless
