import TakeutiGLC.Experiment.Binding.Name

/-!
# Binding experiment: locally nameless syntax

This file is the locally nameless counterpart to
`TakeutiGLC.Experiment.DeBruijn`. Free and special occurrences retain kind-free
opaque names, while bound variable and function occurrences use natural-number
de Bruijn indices.

Raw syntax is not indexed by context depth. This keeps recursive syntax stable
across binders, while scope correctness is expressed separately.
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

/-- Raw locally nameless formulas. -/
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

/-- Raw locally nameless functionals. -/
inductive Functional where
  | abstract
      (headLevel : Nat)
      (tailLevels : List Nat)
      (body : Variety)

/-- The two independent scope depths used to interpret raw indices. -/
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

/-- A raw variable index is valid when it is below the variable depth. -/
def BoundVariableInScope (scope : Scope) (index : Nat) : Prop :=
  index < scope.varDepth

/-- A raw function index is valid when it is below the function depth. -/
def BoundFunctionInScope (scope : Scope) (index : Nat) : Prop :=
  index < scope.funDepth

@[simp] theorem boundVariable_not_in_empty_scope (index : Nat) :
    ¬ BoundVariableInScope ⟨0, 0⟩ index := by
  simp [BoundVariableInScope]

@[simp] theorem boundFunction_not_in_empty_scope (index : Nat) :
    ¬ BoundFunctionInScope ⟨0, 0⟩ index := by
  simp [BoundFunctionInScope]

end TakeutiGLC.Experiment.LocallyNameless
