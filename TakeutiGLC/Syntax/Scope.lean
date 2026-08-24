import TakeutiGLC.Syntax.Core

/-!
# Structural scope for the stable GLC syntax

The locally nameless core deliberately permits raw natural-number bound
indices. This file isolates the corresponding scope invariant in lightweight
inductive judgments with separate depths for Takeuti's variable and function
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

/-- Structural well-scopedness for varieties. -/
inductive Variety.WellScoped : Scope → Variety → Prop where
  | freeVar (scope : Scope) (name : VariableName) :
      Variety.WellScoped scope (.freeVar name)
  | specialVar (scope : Scope) (name : VariableName) :
      Variety.WellScoped scope (.specialVar name)
  | boundVar (scope : Scope) (index : Nat) (hindex : index < scope.varDepth) :
      Variety.WellScoped scope (.boundVar index)
  | freeFunApp (scope : Scope) (name : FunctionName) (args : List Variety)
      (hargs : VarietiesWellScoped scope args) :
      Variety.WellScoped scope (.freeFunApp name args)
  | specialFunApp (scope : Scope) (name : FunctionName) (args : List Variety)
      (hargs : VarietiesWellScoped scope args) :
      Variety.WellScoped scope (.specialFunApp name args)
  | boundFunApp (scope : Scope) (index : Nat) (args : List Variety)
      (hindex : index < scope.funDepth) (hargs : VarietiesWellScoped scope args) :
      Variety.WellScoped scope (.boundFunApp index args)
  | abstract (scope : Scope) (headLevel : Nat) (tailLevels : List Nat) (body : Formula)
      (hbody : Formula.WellScoped (scope.underBlock tailLevels) body) :
      Variety.WellScoped scope (.abstract headLevel tailLevels body)

/-- Structural well-scopedness for formulas. -/
inductive Formula.WellScoped : Scope → Formula → Prop where
  | atomFree (scope : Scope) (name : VariableName) (args : List Variety)
      (hargs : VarietiesWellScoped scope args) :
      Formula.WellScoped scope (.atomFree name args)
  | atomSpecial (scope : Scope) (name : VariableName) (args : List Variety)
      (hargs : VarietiesWellScoped scope args) :
      Formula.WellScoped scope (.atomSpecial name args)
  | atomBound (scope : Scope) (index : Nat) (args : List Variety)
      (hindex : index < scope.varDepth) (hargs : VarietiesWellScoped scope args) :
      Formula.WellScoped scope (.atomBound index args)
  | neg (scope : Scope) (body : Formula)
      (hbody : Formula.WellScoped scope body) :
      Formula.WellScoped scope (.neg body)
  | conj (scope : Scope) (left right : Formula)
      (hleft : Formula.WellScoped scope left)
      (hright : Formula.WellScoped scope right) :
      Formula.WellScoped scope (.conj left right)
  | disj (scope : Scope) (left right : Formula)
      (hleft : Formula.WellScoped scope left)
      (hright : Formula.WellScoped scope right) :
      Formula.WellScoped scope (.disj left right)
  | allVar (scope : Scope) (profile : TypeProfile) (body : Formula)
      (hbody : Formula.WellScoped scope.underVar body) :
      Formula.WellScoped scope (.allVar profile body)
  | existsVar (scope : Scope) (profile : TypeProfile) (body : Formula)
      (hbody : Formula.WellScoped scope.underVar body) :
      Formula.WellScoped scope (.existsVar profile body)
  | allFun (scope : Scope) (profile : FunctionProfile) (body : Formula)
      (hbody : Formula.WellScoped scope.underFun body) :
      Formula.WellScoped scope (.allFun profile body)
  | existsFun (scope : Scope) (profile : FunctionProfile) (body : Formula)
      (hbody : Formula.WellScoped scope.underFun body) :
      Formula.WellScoped scope (.existsFun profile body)

/-- Structural well-scopedness for lists of variety arguments. -/
inductive VarietiesWellScoped : Scope → List Variety → Prop where
  | nil (scope : Scope) : VarietiesWellScoped scope []
  | cons (scope : Scope) (head : Variety) (tail : List Variety)
      (hhead : Variety.WellScoped scope head)
      (htail : VarietiesWellScoped scope tail) :
      VarietiesWellScoped scope (head :: tail)

end

/-- Structural well-scopedness for functionals. -/
inductive Functional.WellScoped : Scope → Functional → Prop where
  | abstract (scope : Scope) (headLevel : Nat) (tailLevels : List Nat) (body : Variety)
      (hbody : Variety.WellScoped (scope.underBlock tailLevels) body) :
      Functional.WellScoped scope (.abstract headLevel tailLevels body)

/-- A variety is closed when it is well scoped in the empty context. -/
def Variety.Closed (variety : Variety) : Prop :=
  Variety.WellScoped Scope.empty variety

/-- A formula is closed when it is well scoped in the empty context. -/
def Formula.Closed (formula : Formula) : Prop :=
  Formula.WellScoped Scope.empty formula

/-- A functional is closed when it is well scoped in the empty context. -/
def Functional.Closed (functional : Functional) : Prop :=
  Functional.WellScoped Scope.empty functional

@[simp] theorem Variety.wellScoped_freeVar (scope : Scope) (name : VariableName) :
    Variety.WellScoped scope (.freeVar name) :=
  .freeVar scope name

@[simp] theorem Variety.wellScoped_specialVar (scope : Scope) (name : VariableName) :
    Variety.WellScoped scope (.specialVar name) :=
  .specialVar scope name

theorem Variety.wellScoped_boundVar (scope : Scope) (index : Nat)
    (hindex : index < scope.varDepth) :
    Variety.WellScoped scope (.boundVar index) :=
  .boundVar scope index hindex

@[simp] theorem Variety.closed_freeVar (name : VariableName) :
    Variety.Closed (.freeVar name) :=
  .freeVar Scope.empty name

@[simp] theorem Variety.closed_specialVar (name : VariableName) :
    Variety.Closed (.specialVar name) :=
  .specialVar Scope.empty name

end TakeutiGLC
