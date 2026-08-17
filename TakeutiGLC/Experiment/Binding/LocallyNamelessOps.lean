import Mathlib.Tactic
import TakeutiGLC.Experiment.Binding.LocallyNameless

/-!
# Opening and closing for the locally nameless prototype

This file is part of Milestone 1.3b. It deliberately implements only the
binding operations needed to compare representations before the stable syntax
API is chosen.
-/

namespace TakeutiGLC.Experiment.LocallyNameless

/-- Insert one new de Bruijn slot at `cutoff`. -/
def insertIndex (cutoff index : Nat) : Nat :=
  if index < cutoff then index else index + 1

/--
Remove one de Bruijn slot at `cutoff`.

`none` denotes the occurrence of the slot being opened; `some i` denotes an
older bound occurrence after its index has been contracted.
-/
def removeIndex (cutoff index : Nat) : Option Nat :=
  if index < cutoff then
    some index
  else if index = cutoff then
    none
  else
    some (index - 1)

mutual

def closeVarietyVarAt (target : VariableName) (cutoff : Nat) : Variety → Variety
  | .freeVar name =>
      if name = target then .boundVar cutoff else .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar (insertIndex cutoff index)
  | .freeFunApp name args =>
      .freeFunApp name (args.map (closeVarietyVarAt target cutoff))
  | .specialFunApp name args =>
      .specialFunApp name (args.map (closeVarietyVarAt target cutoff))
  | .boundFunApp index args =>
      .boundFunApp index (args.map (closeVarietyVarAt target cutoff))
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (closeFormulaVarAt target (blockSize tailLevels + cutoff) body)

def closeFormulaVarAt (target : VariableName) (cutoff : Nat) : Formula → Formula
  | .atomFree name args =>
      if name = target then
        .atomBound cutoff (args.map (closeVarietyVarAt target cutoff))
      else
        .atomFree name (args.map (closeVarietyVarAt target cutoff))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (closeVarietyVarAt target cutoff))
  | .atomBound index args =>
      .atomBound (insertIndex cutoff index)
        (args.map (closeVarietyVarAt target cutoff))
  | .neg body => .neg (closeFormulaVarAt target cutoff body)
  | .conj left right =>
      .conj (closeFormulaVarAt target cutoff left)
        (closeFormulaVarAt target cutoff right)
  | .disj left right =>
      .disj (closeFormulaVarAt target cutoff left)
        (closeFormulaVarAt target cutoff right)
  | .allVar profile body =>
      .allVar profile (closeFormulaVarAt target (cutoff + 1) body)
  | .existsVar profile body =>
      .existsVar profile (closeFormulaVarAt target (cutoff + 1) body)
  | .allFun profile body =>
      .allFun profile (closeFormulaVarAt target cutoff body)
  | .existsFun profile body =>
      .existsFun profile (closeFormulaVarAt target cutoff body)

end

mutual

def openVarietyVarAt (target : VariableName) (cutoff : Nat) : Variety → Variety
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index =>
      match removeIndex cutoff index with
      | none => .freeVar target
      | some index' => .boundVar index'
  | .freeFunApp name args =>
      .freeFunApp name (args.map (openVarietyVarAt target cutoff))
  | .specialFunApp name args =>
      .specialFunApp name (args.map (openVarietyVarAt target cutoff))
  | .boundFunApp index args =>
      .boundFunApp index (args.map (openVarietyVarAt target cutoff))
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (openFormulaVarAt target (blockSize tailLevels + cutoff) body)

def openFormulaVarAt (target : VariableName) (cutoff : Nat) : Formula → Formula
  | .atomFree name args =>
      .atomFree name (args.map (openVarietyVarAt target cutoff))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (openVarietyVarAt target cutoff))
  | .atomBound index args =>
      match removeIndex cutoff index with
      | none => .atomFree target (args.map (openVarietyVarAt target cutoff))
      | some index' =>
          .atomBound index' (args.map (openVarietyVarAt target cutoff))
  | .neg body => .neg (openFormulaVarAt target cutoff body)
  | .conj left right =>
      .conj (openFormulaVarAt target cutoff left)
        (openFormulaVarAt target cutoff right)
  | .disj left right =>
      .disj (openFormulaVarAt target cutoff left)
        (openFormulaVarAt target cutoff right)
  | .allVar profile body =>
      .allVar profile (openFormulaVarAt target (cutoff + 1) body)
  | .existsVar profile body =>
      .existsVar profile (openFormulaVarAt target (cutoff + 1) body)
  | .allFun profile body =>
      .allFun profile (openFormulaVarAt target cutoff body)
  | .existsFun profile body =>
      .existsFun profile (openFormulaVarAt target cutoff body)

end

mutual

def closeVarietyFunAt (target : FunctionName) (cutoff : Nat) : Variety → Variety
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar index
  | .freeFunApp name args =>
      let args' := args.map (closeVarietyFunAt target cutoff)
      if name = target then .boundFunApp cutoff args' else .freeFunApp name args'
  | .specialFunApp name args =>
      .specialFunApp name (args.map (closeVarietyFunAt target cutoff))
  | .boundFunApp index args =>
      .boundFunApp (insertIndex cutoff index)
        (args.map (closeVarietyFunAt target cutoff))
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (closeFormulaFunAt target cutoff body)

def closeFormulaFunAt (target : FunctionName) (cutoff : Nat) : Formula → Formula
  | .atomFree name args =>
      .atomFree name (args.map (closeVarietyFunAt target cutoff))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (closeVarietyFunAt target cutoff))
  | .atomBound index args =>
      .atomBound index (args.map (closeVarietyFunAt target cutoff))
  | .neg body => .neg (closeFormulaFunAt target cutoff body)
  | .conj left right =>
      .conj (closeFormulaFunAt target cutoff left)
        (closeFormulaFunAt target cutoff right)
  | .disj left right =>
      .disj (closeFormulaFunAt target cutoff left)
        (closeFormulaFunAt target cutoff right)
  | .allVar profile body =>
      .allVar profile (closeFormulaFunAt target cutoff body)
  | .existsVar profile body =>
      .existsVar profile (closeFormulaFunAt target cutoff body)
  | .allFun profile body =>
      .allFun profile (closeFormulaFunAt target (cutoff + 1) body)
  | .existsFun profile body =>
      .existsFun profile (closeFormulaFunAt target (cutoff + 1) body)

end

mutual

def openVarietyFunAt (target : FunctionName) (cutoff : Nat) : Variety → Variety
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar index
  | .freeFunApp name args =>
      .freeFunApp name (args.map (openVarietyFunAt target cutoff))
  | .specialFunApp name args =>
      .specialFunApp name (args.map (openVarietyFunAt target cutoff))
  | .boundFunApp index args =>
      let args' := args.map (openVarietyFunAt target cutoff)
      match removeIndex cutoff index with
      | none => .freeFunApp target args'
      | some index' => .boundFunApp index' args'
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (openFormulaFunAt target cutoff body)

def openFormulaFunAt (target : FunctionName) (cutoff : Nat) : Formula → Formula
  | .atomFree name args =>
      .atomFree name (args.map (openVarietyFunAt target cutoff))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (openVarietyFunAt target cutoff))
  | .atomBound index args =>
      .atomBound index (args.map (openVarietyFunAt target cutoff))
  | .neg body => .neg (openFormulaFunAt target cutoff body)
  | .conj left right =>
      .conj (openFormulaFunAt target cutoff left)
        (openFormulaFunAt target cutoff right)
  | .disj left right =>
      .disj (openFormulaFunAt target cutoff left)
        (openFormulaFunAt target cutoff right)
  | .allVar profile body =>
      .allVar profile (openFormulaFunAt target cutoff body)
  | .existsVar profile body =>
      .existsVar profile (openFormulaFunAt target cutoff body)
  | .allFun profile body =>
      .allFun profile (openFormulaFunAt target (cutoff + 1) body)
  | .existsFun profile body =>
      .existsFun profile (openFormulaFunAt target (cutoff + 1) body)

end

def closeVarietyVar (target : VariableName) : Variety → Variety :=
  closeVarietyVarAt target 0

def closeFormulaVar (target : VariableName) : Formula → Formula :=
  closeFormulaVarAt target 0

def openVarietyVar (target : VariableName) : Variety → Variety :=
  openVarietyVarAt target 0

def openFormulaVar (target : VariableName) : Formula → Formula :=
  openFormulaVarAt target 0

def closeVarietyFun (target : FunctionName) : Variety → Variety :=
  closeVarietyFunAt target 0

def closeFormulaFun (target : FunctionName) : Formula → Formula :=
  closeFormulaFunAt target 0

def openVarietyFun (target : FunctionName) : Variety → Variety :=
  openVarietyFunAt target 0

def openFormulaFun (target : FunctionName) : Formula → Formula :=
  openFormulaFunAt target 0

/--
Close a simultaneous Takeuti variable-abstraction block. Repeated single-name
closing places the first source name at de Bruijn index `0`, the second at `1`,
and so on.
-/
def closeFormulaVarBlock (names : List VariableName) (body : Formula) : Formula :=
  names.foldr (fun name body' => closeFormulaVar name body') body

/-- Open a block previously closed by `closeFormulaVarBlock`. -/
def openFormulaVarBlock (names : List VariableName) (body : Formula) : Formula :=
  names.foldl (fun body' name => openFormulaVar name body') body

@[simp] theorem removeIndex_insertIndex (cutoff index : Nat) :
    removeIndex cutoff (insertIndex cutoff index) = some index := by
  by_cases h : index < cutoff
  · simp [insertIndex, removeIndex, h]
  · have hge : cutoff ≤ index := Nat.le_of_not_gt h
    have hnotlt : ¬ index + 1 < cutoff := by omega
    have hne : index + 1 ≠ cutoff := by omega
    simp [insertIndex, removeIndex, h, hnotlt, hne]

@[simp] theorem open_close_freeVar (target : VariableName) :
    openVarietyVar target (closeVarietyVar target (.freeVar target)) =
      .freeVar target := by
  simp [openVarietyVar, closeVarietyVar, openVarietyVarAt, closeVarietyVarAt,
    removeIndex]

@[simp] theorem open_close_boundVar (target : VariableName) (index : Nat) :
    openVarietyVar target (closeVarietyVar target (.boundVar index)) =
      .boundVar index := by
  simp [openVarietyVar, closeVarietyVar, openVarietyVarAt, closeVarietyVarAt,
    removeIndex, insertIndex]

@[simp] theorem open_close_freeFunApp_nil (target : FunctionName) :
    openVarietyFun target (closeVarietyFun target (.freeFunApp target [])) =
      .freeFunApp target [] := by
  simp [openVarietyFun, closeVarietyFun, openVarietyFunAt, closeVarietyFunAt,
    removeIndex]

end TakeutiGLC.Experiment.LocallyNameless
