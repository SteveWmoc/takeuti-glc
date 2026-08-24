import TakeutiGLC.Syntax.Core

/-!
# Structural scope for the stable GLC syntax

The locally nameless core deliberately permits raw natural-number bound
indices. This file isolates the corresponding scope invariant in a lightweight,
computable layer with separate depths for Takeuti's variable and function
binder namespaces.
-/

namespace TakeutiGLC

/-- The current depths of the independent variable and function namespaces. -/
structure Scope where
  varDepth : Nat
  funDepth : Nat
deriving DecidableEq, Repr

namespace Scope

/-- Empty variable and function scope. -/
def empty : Scope := ⟨0, 0⟩

/-- Enter one variable quantifier. -/
def underVar (scope : Scope) : Scope :=
  { scope with varDepth := Nat.succ scope.varDepth }

/-- Enter one function quantifier. -/
def underFun (scope : Scope) : Scope :=
  { scope with funDepth := Nat.succ scope.funDepth }

/-- Enter one nonempty Takeuti variable-abstraction block. -/
def underBlock (scope : Scope) (tailLevels : List Nat) : Scope :=
  { scope with varDepth := blockSize tailLevels + scope.varDepth }

@[simp] theorem empty_varDepth : empty.varDepth = 0 := rfl
@[simp] theorem empty_funDepth : empty.funDepth = 0 := rfl
@[simp] theorem underVar_varDepth (scope : Scope) :
    scope.underVar.varDepth = Nat.succ scope.varDepth := rfl
@[simp] theorem underVar_funDepth (scope : Scope) :
    scope.underVar.funDepth = scope.funDepth := rfl
@[simp] theorem underFun_varDepth (scope : Scope) :
    scope.underFun.varDepth = scope.varDepth := rfl
@[simp] theorem underFun_funDepth (scope : Scope) :
    scope.underFun.funDepth = Nat.succ scope.funDepth := rfl
@[simp] theorem underBlock_varDepth (scope : Scope) (tailLevels : List Nat) :
    (scope.underBlock tailLevels).varDepth =
      blockSize tailLevels + scope.varDepth := rfl
@[simp] theorem underBlock_funDepth (scope : Scope) (tailLevels : List Nat) :
    (scope.underBlock tailLevels).funDepth = scope.funDepth := rfl

end Scope

mutual

/-- Decide whether every bound occurrence in a variety is in scope. -/
def Variety.isWellScoped (scope : Scope) : Variety → Bool
  | .freeVar _ => true
  | .specialVar _ => true
  | .boundVar index => decide (index < scope.varDepth)
  | .freeFunApp _ args => args.all (Variety.isWellScoped scope)
  | .specialFunApp _ args => args.all (Variety.isWellScoped scope)
  | .boundFunApp index args =>
      decide (index < scope.funDepth) && args.all (Variety.isWellScoped scope)
  | .abstract _ tailLevels body =>
      Formula.isWellScoped (scope.underBlock tailLevels) body

/-- Decide whether every bound occurrence in a formula is in scope. -/
def Formula.isWellScoped (scope : Scope) : Formula → Bool
  | .atomFree _ args => args.all (Variety.isWellScoped scope)
  | .atomSpecial _ args => args.all (Variety.isWellScoped scope)
  | .atomBound index args =>
      decide (index < scope.varDepth) && args.all (Variety.isWellScoped scope)
  | .neg body => Formula.isWellScoped scope body
  | .conj left right =>
      Formula.isWellScoped scope left && Formula.isWellScoped scope right
  | .disj left right =>
      Formula.isWellScoped scope left && Formula.isWellScoped scope right
  | .allVar _ body => Formula.isWellScoped scope.underVar body
  | .existsVar _ body => Formula.isWellScoped scope.underVar body
  | .allFun _ body => Formula.isWellScoped scope.underFun body
  | .existsFun _ body => Formula.isWellScoped scope.underFun body

end

/-- Decide whether every bound occurrence in a functional is in scope. -/
def Functional.isWellScoped (scope : Scope) : Functional → Bool
  | .abstract _ tailLevels body =>
      Variety.isWellScoped (scope.underBlock tailLevels) body

/-- Propositional form of structural well-scopedness for varieties. -/
def Variety.WellScoped (scope : Scope) (variety : Variety) : Prop :=
  variety.isWellScoped scope = true

/-- Propositional form of structural well-scopedness for formulas. -/
def Formula.WellScoped (scope : Scope) (formula : Formula) : Prop :=
  formula.isWellScoped scope = true

/-- Propositional form of structural well-scopedness for functionals. -/
def Functional.WellScoped (scope : Scope) (functional : Functional) : Prop :=
  functional.isWellScoped scope = true

/-- A variety is closed when it is well scoped in the empty context. -/
def Variety.Closed (variety : Variety) : Prop :=
  variety.WellScoped Scope.empty

/-- A formula is closed when it is well scoped in the empty context. -/
def Formula.Closed (formula : Formula) : Prop :=
  formula.WellScoped Scope.empty

/-- A functional is closed when it is well scoped in the empty context. -/
def Functional.Closed (functional : Functional) : Prop :=
  functional.WellScoped Scope.empty

@[simp] theorem Variety.wellScoped_freeVar (scope : Scope) (name : VariableName) :
    (Variety.freeVar name).WellScoped scope := by
  rfl

@[simp] theorem Variety.wellScoped_specialVar (scope : Scope) (name : VariableName) :
    (Variety.specialVar name).WellScoped scope := by
  rfl

@[simp] theorem Variety.wellScoped_boundVar_iff (scope : Scope) (index : Nat) :
    (Variety.boundVar index).WellScoped scope ↔ index < scope.varDepth := by
  simp [Variety.WellScoped, Variety.isWellScoped]

@[simp] theorem Formula.wellScoped_atomBound_nil_iff (scope : Scope) (index : Nat) :
    (Formula.atomBound index []).WellScoped scope ↔ index < scope.varDepth := by
  simp [Formula.WellScoped, Formula.isWellScoped]

@[simp] theorem Variety.not_closed_boundVar (index : Nat) :
    ¬ (Variety.boundVar index).Closed := by
  simp [Variety.Closed]

@[simp] theorem Formula.not_closed_atomBound_nil (index : Nat) :
    ¬ (Formula.atomBound index []).Closed := by
  simp [Formula.Closed]

end TakeutiGLC
