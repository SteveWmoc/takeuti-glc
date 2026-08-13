import TakeutiGLC.Experiment.Names

namespace TakeutiGLC.Experiment.LocallyNameless

def blockSize (tailLevels : List Nat) : Nat := tailLevels.length + 1

def abstractionProfile (headLevel : Nat) (tailLevels : List Nat) : TypeProfile :=
  .higher headLevel tailLevels

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

structure Scope where
  varDepth : Nat
  funDepth : Nat
deriving DecidableEq, Repr

namespace Scope

def underVar (scope : Scope) : Scope :=
  { scope with varDepth := Nat.succ scope.varDepth }

def underFun (scope : Scope) : Scope :=
  { scope with funDepth := Nat.succ scope.funDepth }

def underBlock (scope : Scope) (tailLevels : List Nat) : Scope :=
  { scope with varDepth := blockSize tailLevels + scope.varDepth }

end Scope

def BoundVariableInScope (scope : Scope) (index : Nat) : Prop :=
  index < scope.varDepth

def BoundFunctionInScope (scope : Scope) (index : Nat) : Prop :=
  index < scope.funDepth

@[simp] theorem boundVariable_not_in_empty_scope (index : Nat) :
    ¬ BoundVariableInScope ⟨0, 0⟩ index := by
  simp [BoundVariableInScope]

@[simp] theorem boundFunction_not_in_empty_scope (index : Nat) :
    ¬ BoundFunctionInScope ⟨0, 0⟩ index := by
  simp [BoundFunctionInScope]

end TakeutiGLC.Experiment.LocallyNameless
