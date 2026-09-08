import Mathlib.Tactic
import TakeutiGLC.Syntax.Occurrence

/-!
# Stable opening and closing operations

The locally nameless core stores bound variable and function occurrences as
natural-number de Bruijn indices in independent namespaces. This module
promotes the Milestone 1 opening/closing experiment to the stable syntax API.

A cutoff records how many binders of the relevant namespace have been crossed.
Closing inserts a fresh de Bruijn slot at that cutoff and replaces matching free
occurrences by the new bound occurrence. Opening removes the slot and restores
the supplied free name. Variable binders affect only the variable cutoff and
function binders affect only the function cutoff.
-/

namespace TakeutiGLC

/-- Insert one new de Bruijn slot at `cutoff`. -/
def insertIndex (cutoff index : Nat) : Nat :=
  if index < cutoff then index else index + 1

/--
Remove one de Bruijn slot at `cutoff`.

`none` denotes the occurrence of the slot being opened; `some i` denotes an
older bound occurrence after contraction.
-/
def removeIndex (cutoff index : Nat) : Option Nat :=
  if index < cutoff then
    some index
  else if index = cutoff then
    none
  else
    some (index - 1)

mutual

/-- Close all free occurrences of `target` as a variable in a variety. -/
def Variety.closeVarAt (target : VariableName) (cutoff : Nat) : Variety → Variety
  | .freeVar name =>
      if name = target then .boundVar cutoff else .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar (insertIndex cutoff index)
  | .freeFunApp name args =>
      .freeFunApp name (args.map (Variety.closeVarAt target cutoff))
  | .specialFunApp name args =>
      .specialFunApp name (args.map (Variety.closeVarAt target cutoff))
  | .boundFunApp index args =>
      .boundFunApp index (args.map (Variety.closeVarAt target cutoff))
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (Formula.closeVarAt target (blockSize tailLevels + cutoff) body)

/-- Close all free occurrences of `target` as a variable in a formula. -/
def Formula.closeVarAt (target : VariableName) (cutoff : Nat) : Formula → Formula
  | .atomFree name args =>
      if name = target then
        .atomBound cutoff (args.map (Variety.closeVarAt target cutoff))
      else
        .atomFree name (args.map (Variety.closeVarAt target cutoff))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (Variety.closeVarAt target cutoff))
  | .atomBound index args =>
      .atomBound (insertIndex cutoff index)
        (args.map (Variety.closeVarAt target cutoff))
  | .neg body => .neg (Formula.closeVarAt target cutoff body)
  | .conj left right =>
      .conj (Formula.closeVarAt target cutoff left)
        (Formula.closeVarAt target cutoff right)
  | .disj left right =>
      .disj (Formula.closeVarAt target cutoff left)
        (Formula.closeVarAt target cutoff right)
  | .allVar profile body =>
      .allVar profile (Formula.closeVarAt target (cutoff + 1) body)
  | .existsVar profile body =>
      .existsVar profile (Formula.closeVarAt target (cutoff + 1) body)
  | .allFun profile body =>
      .allFun profile (Formula.closeVarAt target cutoff body)
  | .existsFun profile body =>
      .existsFun profile (Formula.closeVarAt target cutoff body)

end

mutual

/-- Open the variable slot at `cutoff` in a variety with `target`. -/
def Variety.openVarAt (target : VariableName) (cutoff : Nat) : Variety → Variety
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index =>
      match removeIndex cutoff index with
      | none => .freeVar target
      | some index' => .boundVar index'
  | .freeFunApp name args =>
      .freeFunApp name (args.map (Variety.openVarAt target cutoff))
  | .specialFunApp name args =>
      .specialFunApp name (args.map (Variety.openVarAt target cutoff))
  | .boundFunApp index args =>
      .boundFunApp index (args.map (Variety.openVarAt target cutoff))
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (Formula.openVarAt target (blockSize tailLevels + cutoff) body)

/-- Open the variable slot at `cutoff` in a formula with `target`. -/
def Formula.openVarAt (target : VariableName) (cutoff : Nat) : Formula → Formula
  | .atomFree name args =>
      .atomFree name (args.map (Variety.openVarAt target cutoff))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (Variety.openVarAt target cutoff))
  | .atomBound index args =>
      match removeIndex cutoff index with
      | none => .atomFree target (args.map (Variety.openVarAt target cutoff))
      | some index' =>
          .atomBound index' (args.map (Variety.openVarAt target cutoff))
  | .neg body => .neg (Formula.openVarAt target cutoff body)
  | .conj left right =>
      .conj (Formula.openVarAt target cutoff left)
        (Formula.openVarAt target cutoff right)
  | .disj left right =>
      .disj (Formula.openVarAt target cutoff left)
        (Formula.openVarAt target cutoff right)
  | .allVar profile body =>
      .allVar profile (Formula.openVarAt target (cutoff + 1) body)
  | .existsVar profile body =>
      .existsVar profile (Formula.openVarAt target (cutoff + 1) body)
  | .allFun profile body =>
      .allFun profile (Formula.openVarAt target cutoff body)
  | .existsFun profile body =>
      .existsFun profile (Formula.openVarAt target cutoff body)

end

mutual

/-- Close all free occurrences of `target` as a function in a variety. -/
def Variety.closeFunAt (target : FunctionName) (cutoff : Nat) : Variety → Variety
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar index
  | .freeFunApp name args =>
      let args' := args.map (Variety.closeFunAt target cutoff)
      if name = target then .boundFunApp cutoff args' else .freeFunApp name args'
  | .specialFunApp name args =>
      .specialFunApp name (args.map (Variety.closeFunAt target cutoff))
  | .boundFunApp index args =>
      .boundFunApp (insertIndex cutoff index)
        (args.map (Variety.closeFunAt target cutoff))
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (Formula.closeFunAt target cutoff body)

/-- Close all free occurrences of `target` as a function in a formula. -/
def Formula.closeFunAt (target : FunctionName) (cutoff : Nat) : Formula → Formula
  | .atomFree name args =>
      .atomFree name (args.map (Variety.closeFunAt target cutoff))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (Variety.closeFunAt target cutoff))
  | .atomBound index args =>
      .atomBound index (args.map (Variety.closeFunAt target cutoff))
  | .neg body => .neg (Formula.closeFunAt target cutoff body)
  | .conj left right =>
      .conj (Formula.closeFunAt target cutoff left)
        (Formula.closeFunAt target cutoff right)
  | .disj left right =>
      .disj (Formula.closeFunAt target cutoff left)
        (Formula.closeFunAt target cutoff right)
  | .allVar profile body =>
      .allVar profile (Formula.closeFunAt target cutoff body)
  | .existsVar profile body =>
      .existsVar profile (Formula.closeFunAt target cutoff body)
  | .allFun profile body =>
      .allFun profile (Formula.closeFunAt target (cutoff + 1) body)
  | .existsFun profile body =>
      .existsFun profile (Formula.closeFunAt target (cutoff + 1) body)

end

mutual

/-- Open the function slot at `cutoff` in a variety with `target`. -/
def Variety.openFunAt (target : FunctionName) (cutoff : Nat) : Variety → Variety
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar index
  | .freeFunApp name args =>
      .freeFunApp name (args.map (Variety.openFunAt target cutoff))
  | .specialFunApp name args =>
      .specialFunApp name (args.map (Variety.openFunAt target cutoff))
  | .boundFunApp index args =>
      let args' := args.map (Variety.openFunAt target cutoff)
      match removeIndex cutoff index with
      | none => .freeFunApp target args'
      | some index' => .boundFunApp index' args'
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (Formula.openFunAt target cutoff body)

/-- Open the function slot at `cutoff` in a formula with `target`. -/
def Formula.openFunAt (target : FunctionName) (cutoff : Nat) : Formula → Formula
  | .atomFree name args =>
      .atomFree name (args.map (Variety.openFunAt target cutoff))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (Variety.openFunAt target cutoff))
  | .atomBound index args =>
      .atomBound index (args.map (Variety.openFunAt target cutoff))
  | .neg body => .neg (Formula.openFunAt target cutoff body)
  | .conj left right =>
      .conj (Formula.openFunAt target cutoff left)
        (Formula.openFunAt target cutoff right)
  | .disj left right =>
      .disj (Formula.openFunAt target cutoff left)
        (Formula.openFunAt target cutoff right)
  | .allVar profile body =>
      .allVar profile (Formula.openFunAt target cutoff body)
  | .existsVar profile body =>
      .existsVar profile (Formula.openFunAt target cutoff body)
  | .allFun profile body =>
      .allFun profile (Formula.openFunAt target (cutoff + 1) body)
  | .existsFun profile body =>
      .existsFun profile (Formula.openFunAt target (cutoff + 1) body)

end

namespace Variety

/-- Close a free variable into a fresh outer variable slot. -/
def closeVar (target : VariableName) : Variety → Variety := closeVarAt target 0

/-- Open the outermost variable slot with a free name. -/
def openVar (target : VariableName) : Variety → Variety := openVarAt target 0

/-- Close a free function into a fresh outer function slot. -/
def closeFun (target : FunctionName) : Variety → Variety := closeFunAt target 0

/-- Open the outermost function slot with a free name. -/
def openFun (target : FunctionName) : Variety → Variety := openFunAt target 0

/-- Close a simultaneous variable block, preserving display order at indices `0, 1, ...`. -/
def closeVarBlock (names : List VariableName) (body : Variety) : Variety :=
  names.foldr (fun name body' => body'.closeVar name) body

/-- Open a block previously closed by `closeVarBlock`. -/
def openVarBlock (names : List VariableName) (body : Variety) : Variety :=
  names.foldl (fun body' name => body'.openVar name) body

end Variety

namespace Formula

/-- Close a free variable into a fresh outer variable slot. -/
def closeVar (target : VariableName) : Formula → Formula := closeVarAt target 0

/-- Open the outermost variable slot with a free name. -/
def openVar (target : VariableName) : Formula → Formula := openVarAt target 0

/-- Close a free function into a fresh outer function slot. -/
def closeFun (target : FunctionName) : Formula → Formula := closeFunAt target 0

/-- Open the outermost function slot with a free name. -/
def openFun (target : FunctionName) : Formula → Formula := openFunAt target 0

/-- Close a simultaneous Takeuti variable-abstraction block. -/
def closeVarBlock (names : List VariableName) (body : Formula) : Formula :=
  names.foldr (fun name body' => body'.closeVar name) body

/-- Open a block previously closed by `closeVarBlock`. -/
def openVarBlock (names : List VariableName) (body : Formula) : Formula :=
  names.foldl (fun body' name => body'.openVar name) body

end Formula

namespace Functional

/-- Close a free variable outside a functional's own abstraction block. -/
def closeVarAt (target : VariableName) (cutoff : Nat) : Functional → Functional
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (body.closeVarAt target (blockSize tailLevels + cutoff))

/-- Open a variable slot outside a functional's own abstraction block. -/
def openVarAt (target : VariableName) (cutoff : Nat) : Functional → Functional
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (body.openVarAt target (blockSize tailLevels + cutoff))

/-- Close a free function outside a functional. -/
def closeFunAt (target : FunctionName) (cutoff : Nat) : Functional → Functional
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (body.closeFunAt target cutoff)

/-- Open a function slot outside a functional. -/
def openFunAt (target : FunctionName) (cutoff : Nat) : Functional → Functional
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (body.openFunAt target cutoff)

end Functional

@[simp] theorem removeIndex_insertIndex (cutoff index : Nat) :
    removeIndex cutoff (insertIndex cutoff index) = some index := by
  by_cases h : index < cutoff
  · simp [insertIndex, removeIndex, h]
  · have hge : cutoff ≤ index := Nat.le_of_not_gt h
    have hnotlt : ¬ index + 1 < cutoff := by omega
    have hne : index + 1 ≠ cutoff := by omega
    simp [insertIndex, removeIndex, h, hnotlt, hne]

@[simp] theorem Variety.openVar_closeVar_freeVar (target : VariableName) :
    (.freeVar target).closeVar target |>.openVar target = .freeVar target := by
  simp [Variety.openVar, Variety.closeVar, Variety.openVarAt, Variety.closeVarAt,
    removeIndex]

@[simp] theorem Variety.openVar_closeVar_boundVar (target : VariableName) (index : Nat) :
    (.boundVar index).closeVar target |>.openVar target = .boundVar index := by
  simp [Variety.openVar, Variety.closeVar, Variety.openVarAt, Variety.closeVarAt,
    removeIndex, insertIndex]

@[simp] theorem Variety.openFun_closeFun_freeFunApp_nil (target : FunctionName) :
    (.freeFunApp target []).closeFun target |>.openFun target = .freeFunApp target [] := by
  simp [Variety.openFun, Variety.closeFun, Variety.openFunAt, Variety.closeFunAt,
    removeIndex]

end TakeutiGLC
