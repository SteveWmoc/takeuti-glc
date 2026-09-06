import Mathlib.Data.Finset.Basic
import TakeutiGLC.Syntax.Typing

/-!
# Occurrences, indication, and quantifier non-vacuity

Takeuti's §3.1 notation indicates selected occurrences of free variables or
free functions without changing the underlying figure. Sections 2.8–2.9 also
require the free symbol being quantified to occur in the premiss formula.

This module keeps both ideas outside raw syntax identity:

* `OccurrencePath` addresses a particular named occurrence structurally;
* finite selections record the paths indicated by §3.1;
* bound-occurrence predicates recognize whether a newly introduced de Bruijn
  binder is actually used, which supplies the non-vacuity side condition for
  §§2.8–2.9 after source-to-core translation.

The path representation is deliberately auxiliary. Invalid paths simply fail
to resolve, and a selection is valid for an expression exactly when each of its
stored paths resolves to the selected free name.
-/

namespace TakeutiGLC

/-- One structural step in an auxiliary occurrence address. -/
inductive OccurrenceStep where
  | argument (index : Nat)
  | abstractionBody
  | body
  | left
  | right
deriving DecidableEq, Repr

/-- A structural address used only for metasyntactic occurrence indication. -/
abbrev OccurrencePath := List OccurrenceStep

mutual

/-- Resolve a path to a free variable occurrence in a variety, if one is there. -/
def Variety.freeVariableAt : OccurrencePath → Variety → Option VariableName
  | [], .freeVar name => some name
  | .argument index :: rest, .freeFunApp _ args
  | .argument index :: rest, .specialFunApp _ args
  | .argument index :: rest, .boundFunApp _ args =>
      match args[index]? with
      | some arg => Variety.freeVariableAt rest arg
      | none => none
  | .abstractionBody :: rest, .abstract _ _ body => Formula.freeVariableAt rest body
  | _, _ => none

/-- Resolve a path to a free variable occurrence in a formula, if one is there. -/
def Formula.freeVariableAt : OccurrencePath → Formula → Option VariableName
  | [], .atomFree name _ => some name
  | .argument index :: rest, .atomFree _ args
  | .argument index :: rest, .atomSpecial _ args
  | .argument index :: rest, .atomBound _ args =>
      match args[index]? with
      | some arg => Variety.freeVariableAt rest arg
      | none => none
  | .body :: rest, .neg body
  | .body :: rest, .allVar _ body
  | .body :: rest, .existsVar _ body
  | .body :: rest, .allFun _ body
  | .body :: rest, .existsFun _ body => Formula.freeVariableAt rest body
  | .left :: rest, .conj left _
  | .left :: rest, .disj left _ => Formula.freeVariableAt rest left
  | .right :: rest, .conj _ right
  | .right :: rest, .disj _ right => Formula.freeVariableAt rest right
  | _, _ => none

end

mutual

/-- Resolve a path to a free function occurrence in a variety, if one is there. -/
def Variety.freeFunctionAt : OccurrencePath → Variety → Option FunctionName
  | [], .freeFunApp name _ => some name
  | .argument index :: rest, .freeFunApp _ args
  | .argument index :: rest, .specialFunApp _ args
  | .argument index :: rest, .boundFunApp _ args =>
      match args[index]? with
      | some arg => Variety.freeFunctionAt rest arg
      | none => none
  | .abstractionBody :: rest, .abstract _ _ body => Formula.freeFunctionAt rest body
  | _, _ => none

/-- Resolve a path to a free function occurrence in a formula, if one is there. -/
def Formula.freeFunctionAt : OccurrencePath → Formula → Option FunctionName
  | .argument index :: rest, .atomFree _ args
  | .argument index :: rest, .atomSpecial _ args
  | .argument index :: rest, .atomBound _ args =>
      match args[index]? with
      | some arg => Variety.freeFunctionAt rest arg
      | none => none
  | .body :: rest, .neg body
  | .body :: rest, .allVar _ body
  | .body :: rest, .existsVar _ body
  | .body :: rest, .allFun _ body
  | .body :: rest, .existsFun _ body => Formula.freeFunctionAt rest body
  | .left :: rest, .conj left _
  | .left :: rest, .disj left _ => Formula.freeFunctionAt rest left
  | .right :: rest, .conj _ right
  | .right :: rest, .disj _ right => Formula.freeFunctionAt rest right
  | _, _ => none

end

namespace Functional

/-- Resolve a path to a free variable occurrence in a functional body. -/
def freeVariableAt : OccurrencePath → Functional → Option VariableName
  | .abstractionBody :: rest, .abstract _ _ body => Variety.freeVariableAt rest body
  | _, _ => none

/-- Resolve a path to a free function occurrence in a functional body. -/
def freeFunctionAt : OccurrencePath → Functional → Option FunctionName
  | .abstractionBody :: rest, .abstract _ _ body => Variety.freeFunctionAt rest body
  | _, _ => none

end Functional

/-- Finite §3.1 indication data for occurrences of one free variable. -/
structure VariableOccurrenceSelection where
  name : VariableName
  paths : Finset OccurrencePath
deriving DecidableEq, Repr

/-- Finite §3.1 indication data for occurrences of one free function. -/
structure FunctionOccurrenceSelection where
  name : FunctionName
  paths : Finset OccurrencePath
deriving DecidableEq, Repr

namespace VariableOccurrenceSelection

/-- Every selected path resolves to the selected variable in this variety. -/
def ValidForVariety (selection : VariableOccurrenceSelection) (variety : Variety) : Prop :=
  ∀ path ∈ selection.paths, variety.freeVariableAt path = some selection.name

/-- Every selected path resolves to the selected variable in this formula. -/
def ValidForFormula (selection : VariableOccurrenceSelection) (formula : Formula) : Prop :=
  ∀ path ∈ selection.paths, formula.freeVariableAt path = some selection.name

/-- Every selected path resolves to the selected variable in this functional. -/
def ValidForFunctional (selection : VariableOccurrenceSelection) (functional : Functional) : Prop :=
  ∀ path ∈ selection.paths, functional.freeVariableAt path = some selection.name

/-- §3.3 full indication for a variety. -/
def FullyIndicatesVariety (selection : VariableOccurrenceSelection) (variety : Variety) : Prop :=
  selection.ValidForVariety variety ∧
    ∀ path, variety.freeVariableAt path = some selection.name → path ∈ selection.paths

/-- §3.3 full indication for a formula. -/
def FullyIndicatesFormula (selection : VariableOccurrenceSelection) (formula : Formula) : Prop :=
  selection.ValidForFormula formula ∧
    ∀ path, formula.freeVariableAt path = some selection.name → path ∈ selection.paths

/-- §3.3 full indication for a functional. -/
def FullyIndicatesFunctional
    (selection : VariableOccurrenceSelection) (functional : Functional) : Prop :=
  selection.ValidForFunctional functional ∧
    ∀ path, functional.freeVariableAt path = some selection.name → path ∈ selection.paths

end VariableOccurrenceSelection

namespace FunctionOccurrenceSelection

/-- Every selected path resolves to the selected function in this variety. -/
def ValidForVariety (selection : FunctionOccurrenceSelection) (variety : Variety) : Prop :=
  ∀ path ∈ selection.paths, variety.freeFunctionAt path = some selection.name

/-- Every selected path resolves to the selected function in this formula. -/
def ValidForFormula (selection : FunctionOccurrenceSelection) (formula : Formula) : Prop :=
  ∀ path ∈ selection.paths, formula.freeFunctionAt path = some selection.name

/-- Every selected path resolves to the selected function in this functional. -/
def ValidForFunctional (selection : FunctionOccurrenceSelection) (functional : Functional) : Prop :=
  ∀ path ∈ selection.paths, functional.freeFunctionAt path = some selection.name

/-- §3.3 full indication for a variety. -/
def FullyIndicatesVariety (selection : FunctionOccurrenceSelection) (variety : Variety) : Prop :=
  selection.ValidForVariety variety ∧
    ∀ path, variety.freeFunctionAt path = some selection.name → path ∈ selection.paths

/-- §3.3 full indication for a formula. -/
def FullyIndicatesFormula (selection : FunctionOccurrenceSelection) (formula : Formula) : Prop :=
  selection.ValidForFormula formula ∧
    ∀ path, formula.freeFunctionAt path = some selection.name → path ∈ selection.paths

/-- §3.3 full indication for a functional. -/
def FullyIndicatesFunctional
    (selection : FunctionOccurrenceSelection) (functional : Functional) : Prop :=
  selection.ValidForFunctional functional ∧
    ∀ path, functional.freeFunctionAt path = some selection.name → path ∈ selection.paths

end FunctionOccurrenceSelection

mutual

/-- A bound variable at `cutoff` occurs in a variety, accounting for nested binders. -/
inductive Variety.UsesBoundVariableAt (cutoff : Nat) : Variety → Prop where
  | boundVar {index : Nat} (hindex : index = cutoff) :
      Variety.UsesBoundVariableAt cutoff (.boundVar index)
  | freeFunArg {name : FunctionName} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundVariableAt cutoff arg) :
      Variety.UsesBoundVariableAt cutoff (.freeFunApp name args)
  | specialFunArg {name : FunctionName} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundVariableAt cutoff arg) :
      Variety.UsesBoundVariableAt cutoff (.specialFunApp name args)
  | boundFunArg {index : Nat} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundVariableAt cutoff arg) :
      Variety.UsesBoundVariableAt cutoff (.boundFunApp index args)
  | abstract {headLevel : Nat} {tailLevels : List Nat} {body : Formula}
      (hbody : Formula.UsesBoundVariableAt (cutoff + blockSize tailLevels) body) :
      Variety.UsesBoundVariableAt cutoff (.abstract headLevel tailLevels body)

/-- A bound variable at `cutoff` occurs in a formula, accounting for nested binders. -/
inductive Formula.UsesBoundVariableAt (cutoff : Nat) : Formula → Prop where
  | atomBound {index : Nat} {args : List Variety} (hindex : index = cutoff) :
      Formula.UsesBoundVariableAt cutoff (.atomBound index args)
  | atomFreeArg {name : VariableName} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundVariableAt cutoff arg) :
      Formula.UsesBoundVariableAt cutoff (.atomFree name args)
  | atomSpecialArg {name : VariableName} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundVariableAt cutoff arg) :
      Formula.UsesBoundVariableAt cutoff (.atomSpecial name args)
  | atomBoundArg {index : Nat} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundVariableAt cutoff arg) :
      Formula.UsesBoundVariableAt cutoff (.atomBound index args)
  | neg {body : Formula} (hbody : Formula.UsesBoundVariableAt cutoff body) :
      Formula.UsesBoundVariableAt cutoff (.neg body)
  | conjLeft {left right : Formula} (hleft : Formula.UsesBoundVariableAt cutoff left) :
      Formula.UsesBoundVariableAt cutoff (.conj left right)
  | conjRight {left right : Formula} (hright : Formula.UsesBoundVariableAt cutoff right) :
      Formula.UsesBoundVariableAt cutoff (.conj left right)
  | disjLeft {left right : Formula} (hleft : Formula.UsesBoundVariableAt cutoff left) :
      Formula.UsesBoundVariableAt cutoff (.disj left right)
  | disjRight {left right : Formula} (hright : Formula.UsesBoundVariableAt cutoff right) :
      Formula.UsesBoundVariableAt cutoff (.disj left right)
  | allVar {profile : TypeProfile} {body : Formula}
      (hbody : Formula.UsesBoundVariableAt (cutoff + 1) body) :
      Formula.UsesBoundVariableAt cutoff (.allVar profile body)
  | existsVar {profile : TypeProfile} {body : Formula}
      (hbody : Formula.UsesBoundVariableAt (cutoff + 1) body) :
      Formula.UsesBoundVariableAt cutoff (.existsVar profile body)
  | allFun {profile : FunctionProfile} {body : Formula}
      (hbody : Formula.UsesBoundVariableAt cutoff body) :
      Formula.UsesBoundVariableAt cutoff (.allFun profile body)
  | existsFun {profile : FunctionProfile} {body : Formula}
      (hbody : Formula.UsesBoundVariableAt cutoff body) :
      Formula.UsesBoundVariableAt cutoff (.existsFun profile body)

end

mutual

/-- A bound function at `cutoff` occurs in a variety, accounting for nested binders. -/
inductive Variety.UsesBoundFunctionAt (cutoff : Nat) : Variety → Prop where
  | boundFun {index : Nat} {args : List Variety} (hindex : index = cutoff) :
      Variety.UsesBoundFunctionAt cutoff (.boundFunApp index args)
  | freeFunArg {name : FunctionName} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundFunctionAt cutoff arg) :
      Variety.UsesBoundFunctionAt cutoff (.freeFunApp name args)
  | specialFunArg {name : FunctionName} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundFunctionAt cutoff arg) :
      Variety.UsesBoundFunctionAt cutoff (.specialFunApp name args)
  | boundFunArg {index : Nat} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundFunctionAt cutoff arg) :
      Variety.UsesBoundFunctionAt cutoff (.boundFunApp index args)
  | abstract {headLevel : Nat} {tailLevels : List Nat} {body : Formula}
      (hbody : Formula.UsesBoundFunctionAt cutoff body) :
      Variety.UsesBoundFunctionAt cutoff (.abstract headLevel tailLevels body)

/-- A bound function at `cutoff` occurs in a formula, accounting for nested binders. -/
inductive Formula.UsesBoundFunctionAt (cutoff : Nat) : Formula → Prop where
  | atomFreeArg {name : VariableName} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundFunctionAt cutoff arg) :
      Formula.UsesBoundFunctionAt cutoff (.atomFree name args)
  | atomSpecialArg {name : VariableName} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundFunctionAt cutoff arg) :
      Formula.UsesBoundFunctionAt cutoff (.atomSpecial name args)
  | atomBoundArg {index : Nat} {args : List Variety} {arg : Variety}
      (hmem : arg ∈ args) (harg : Variety.UsesBoundFunctionAt cutoff arg) :
      Formula.UsesBoundFunctionAt cutoff (.atomBound index args)
  | neg {body : Formula} (hbody : Formula.UsesBoundFunctionAt cutoff body) :
      Formula.UsesBoundFunctionAt cutoff (.neg body)
  | conjLeft {left right : Formula} (hleft : Formula.UsesBoundFunctionAt cutoff left) :
      Formula.UsesBoundFunctionAt cutoff (.conj left right)
  | conjRight {left right : Formula} (hright : Formula.UsesBoundFunctionAt cutoff right) :
      Formula.UsesBoundFunctionAt cutoff (.conj left right)
  | disjLeft {left right : Formula} (hleft : Formula.UsesBoundFunctionAt cutoff left) :
      Formula.UsesBoundFunctionAt cutoff (.disj left right)
  | disjRight {left right : Formula} (hright : Formula.UsesBoundFunctionAt cutoff right) :
      Formula.UsesBoundFunctionAt cutoff (.disj left right)
  | allVar {profile : TypeProfile} {body : Formula}
      (hbody : Formula.UsesBoundFunctionAt cutoff body) :
      Formula.UsesBoundFunctionAt cutoff (.allVar profile body)
  | existsVar {profile : TypeProfile} {body : Formula}
      (hbody : Formula.UsesBoundFunctionAt cutoff body) :
      Formula.UsesBoundFunctionAt cutoff (.existsVar profile body)
  | allFun {profile : FunctionProfile} {body : Formula}
      (hbody : Formula.UsesBoundFunctionAt (cutoff + 1) body) :
      Formula.UsesBoundFunctionAt cutoff (.allFun profile body)
  | existsFun {profile : FunctionProfile} {body : Formula}
      (hbody : Formula.UsesBoundFunctionAt (cutoff + 1) body) :
      Formula.UsesBoundFunctionAt cutoff (.existsFun profile body)

end

namespace Formula

/-- The innermost variable binder represented by a formula body is used. -/
def UsesInnermostVariableBinder (body : Formula) : Prop :=
  Formula.UsesBoundVariableAt 0 body

/-- The innermost function binder represented by a formula body is used. -/
def UsesInnermostFunctionBinder (body : Formula) : Prop :=
  Formula.UsesBoundFunctionAt 0 body

end Formula

mutual

/-- All quantifiers nested in a variety satisfy Takeuti's non-vacuity condition. -/
inductive Variety.QuantifierSideConditions : Variety → Prop where
  | freeVar (name : VariableName) : Variety.QuantifierSideConditions (.freeVar name)
  | specialVar (name : VariableName) : Variety.QuantifierSideConditions (.specialVar name)
  | boundVar (index : Nat) : Variety.QuantifierSideConditions (.boundVar index)
  | freeFunApp (name : FunctionName) (args : List Variety)
      (hargs : ∀ arg ∈ args, Variety.QuantifierSideConditions arg) :
      Variety.QuantifierSideConditions (.freeFunApp name args)
  | specialFunApp (name : FunctionName) (args : List Variety)
      (hargs : ∀ arg ∈ args, Variety.QuantifierSideConditions arg) :
      Variety.QuantifierSideConditions (.specialFunApp name args)
  | boundFunApp (index : Nat) (args : List Variety)
      (hargs : ∀ arg ∈ args, Variety.QuantifierSideConditions arg) :
      Variety.QuantifierSideConditions (.boundFunApp index args)
  | abstract (headLevel : Nat) (tailLevels : List Nat) (body : Formula)
      (hbody : Formula.QuantifierSideConditions body) :
      Variety.QuantifierSideConditions (.abstract headLevel tailLevels body)

/-- All quantifiers nested in a formula satisfy Takeuti's non-vacuity condition. -/
inductive Formula.QuantifierSideConditions : Formula → Prop where
  | atomFree (name : VariableName) (args : List Variety)
      (hargs : ∀ arg ∈ args, Variety.QuantifierSideConditions arg) :
      Formula.QuantifierSideConditions (.atomFree name args)
  | atomSpecial (name : VariableName) (args : List Variety)
      (hargs : ∀ arg ∈ args, Variety.QuantifierSideConditions arg) :
      Formula.QuantifierSideConditions (.atomSpecial name args)
  | atomBound (index : Nat) (args : List Variety)
      (hargs : ∀ arg ∈ args, Variety.QuantifierSideConditions arg) :
      Formula.QuantifierSideConditions (.atomBound index args)
  | neg (body : Formula) (hbody : Formula.QuantifierSideConditions body) :
      Formula.QuantifierSideConditions (.neg body)
  | conj (left right : Formula)
      (hleft : Formula.QuantifierSideConditions left)
      (hright : Formula.QuantifierSideConditions right) :
      Formula.QuantifierSideConditions (.conj left right)
  | disj (left right : Formula)
      (hleft : Formula.QuantifierSideConditions left)
      (hright : Formula.QuantifierSideConditions right) :
      Formula.QuantifierSideConditions (.disj left right)
  | allVar (profile : TypeProfile) (body : Formula)
      (hused : Formula.UsesInnermostVariableBinder body)
      (hbody : Formula.QuantifierSideConditions body) :
      Formula.QuantifierSideConditions (.allVar profile body)
  | existsVar (profile : TypeProfile) (body : Formula)
      (hused : Formula.UsesInnermostVariableBinder body)
      (hbody : Formula.QuantifierSideConditions body) :
      Formula.QuantifierSideConditions (.existsVar profile body)
  | allFun (profile : FunctionProfile) (body : Formula)
      (hused : Formula.UsesInnermostFunctionBinder body)
      (hbody : Formula.QuantifierSideConditions body) :
      Formula.QuantifierSideConditions (.allFun profile body)
  | existsFun (profile : FunctionProfile) (body : Formula)
      (hused : Formula.UsesInnermostFunctionBinder body)
      (hbody : Formula.QuantifierSideConditions body) :
      Formula.QuantifierSideConditions (.existsFun profile body)

end

namespace Functional

/-- All quantifiers nested in a functional body satisfy the §§2.8–2.9 side conditions. -/
def QuantifierSideConditions : Functional → Prop
  | .abstract _ _ body => Variety.QuantifierSideConditions body

end Functional

namespace Variety

/-- Typed variety formation together with all nested quantifier non-vacuity conditions. -/
def WellFormedWithNonvacuousQuantifiers
    (ctx : TypingContext) (variety : Variety) : Prop :=
  Variety.WellTyped ctx variety ∧ Variety.QuantifierSideConditions variety

end Variety

namespace Formula

/-- Typed formula formation together with all nested quantifier non-vacuity conditions. -/
def WellFormedWithNonvacuousQuantifiers
    (ctx : TypingContext) (formula : Formula) : Prop :=
  Formula.WellFormed ctx formula ∧ Formula.QuantifierSideConditions formula

end Formula

namespace Functional

/-- Typed functional formation together with all nested quantifier non-vacuity conditions. -/
def WellFormedWithNonvacuousQuantifiers
    (ctx : TypingContext) (functional : Functional) : Prop :=
  Functional.WellFormed ctx functional ∧ Functional.QuantifierSideConditions functional

end Functional

end TakeutiGLC
