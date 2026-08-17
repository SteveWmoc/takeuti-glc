import Mathlib.Tactic
import TakeutiGLC.Experiment.Binding.DeBruijn

/-!
# Opening and closing for the intrinsically scoped de Bruijn prototype

This file is the Milestone 1.3b counterpart to `LocallyNamelessOps`. The
operations are intentionally explicit about cutoffs and scope proofs so that
the engineering cost of intrinsic scoping can be compared rather than hidden.
-/

namespace TakeutiGLC.Experiment.DeBruijn

/-- Insert one new slot into a finite de Bruijn context. -/
def insertFin (cutoff : Nat) {depth : Nat} (_hcut : cutoff ≤ depth)
    (index : Fin depth) : Fin (Nat.succ depth) :=
  if h : index.val < cutoff then
    ⟨index.val, by omega⟩
  else
    ⟨index.val + 1, by omega⟩

/-- The finite index of the newly introduced binder. -/
def newFin (cutoff : Nat) {depth : Nat} (hcut : cutoff ≤ depth) :
    Fin (Nat.succ depth) :=
  ⟨cutoff, by omega⟩

/--
Remove one slot from a finite de Bruijn context. `none` marks the occurrence
of the slot being opened.
-/
def removeFin (cutoff : Nat) {depth : Nat} (hcut : cutoff ≤ depth)
    (index : Fin (Nat.succ depth)) : Option (Fin depth) :=
  if hlt : index.val < cutoff then
    some ⟨index.val, by omega⟩
  else if heq : index.val = cutoff then
    none
  else
    some ⟨index.val - 1, by omega⟩

mutual

def closeVarietyVarAt {varDepth funDepth : Nat} (target : VariableName)
    (cutoff : Nat) (hcut : cutoff ≤ varDepth) :
    Variety varDepth funDepth → Variety (Nat.succ varDepth) funDepth
  | .freeVar name =>
      if name = target then .boundVar (newFin cutoff hcut) else .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar (insertFin cutoff hcut index)
  | .freeFunApp name args =>
      .freeFunApp name (closeArgumentsVarAt target cutoff hcut args)
  | .specialFunApp name args =>
      .specialFunApp name (closeArgumentsVarAt target cutoff hcut args)
  | .boundFunApp index args =>
      .boundFunApp index (closeArgumentsVarAt target cutoff hcut args)
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (by
        simpa [Nat.add_assoc] using
          closeFormulaVarAt target (blockSize tailLevels + cutoff) (by omega) body)

def closeFormulaVarAt {varDepth funDepth : Nat} (target : VariableName)
    (cutoff : Nat) (hcut : cutoff ≤ varDepth) :
    Formula varDepth funDepth → Formula (Nat.succ varDepth) funDepth
  | .atomFree name args =>
      if name = target then
        .atomBound (newFin cutoff hcut)
          (closeArgumentsVarAt target cutoff hcut args)
      else
        .atomFree name (closeArgumentsVarAt target cutoff hcut args)
  | .atomSpecial name args =>
      .atomSpecial name (closeArgumentsVarAt target cutoff hcut args)
  | .atomBound index args =>
      .atomBound (insertFin cutoff hcut index)
        (closeArgumentsVarAt target cutoff hcut args)
  | .neg body => .neg (closeFormulaVarAt target cutoff hcut body)
  | .conj left right =>
      .conj (closeFormulaVarAt target cutoff hcut left)
        (closeFormulaVarAt target cutoff hcut right)
  | .disj left right =>
      .disj (closeFormulaVarAt target cutoff hcut left)
        (closeFormulaVarAt target cutoff hcut right)
  | .allVar profile body =>
      .allVar profile (closeFormulaVarAt target (cutoff + 1) (by omega) body)
  | .existsVar profile body =>
      .existsVar profile (closeFormulaVarAt target (cutoff + 1) (by omega) body)
  | .allFun profile body =>
      .allFun profile (closeFormulaVarAt target cutoff hcut body)
  | .existsFun profile body =>
      .existsFun profile (closeFormulaVarAt target cutoff hcut body)

def closeArgumentsVarAt {varDepth funDepth : Nat} (target : VariableName)
    (cutoff : Nat) (hcut : cutoff ≤ varDepth) :
    Arguments varDepth funDepth → Arguments (Nat.succ varDepth) funDepth
  | .nil => .nil
  | .cons head tail =>
      .cons (closeVarietyVarAt target cutoff hcut head)
        (closeArgumentsVarAt target cutoff hcut tail)

end

mutual

def openVarietyVarAt {varDepth funDepth : Nat} (target : VariableName)
    (cutoff : Nat) (hcut : cutoff ≤ varDepth) :
    Variety (Nat.succ varDepth) funDepth → Variety varDepth funDepth
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index =>
      match removeFin cutoff hcut index with
      | none => .freeVar target
      | some index' => .boundVar index'
  | .freeFunApp name args =>
      .freeFunApp name (openArgumentsVarAt target cutoff hcut args)
  | .specialFunApp name args =>
      .specialFunApp name (openArgumentsVarAt target cutoff hcut args)
  | .boundFunApp index args =>
      .boundFunApp index (openArgumentsVarAt target cutoff hcut args)
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (by
        have body' : Formula (Nat.succ (blockSize tailLevels + varDepth)) funDepth := by
          simpa [Nat.add_assoc] using body
        exact openFormulaVarAt target (blockSize tailLevels + cutoff) (by omega) body')

def openFormulaVarAt {varDepth funDepth : Nat} (target : VariableName)
    (cutoff : Nat) (hcut : cutoff ≤ varDepth) :
    Formula (Nat.succ varDepth) funDepth → Formula varDepth funDepth
  | .atomFree name args =>
      .atomFree name (openArgumentsVarAt target cutoff hcut args)
  | .atomSpecial name args =>
      .atomSpecial name (openArgumentsVarAt target cutoff hcut args)
  | .atomBound index args =>
      match removeFin cutoff hcut index with
      | none => .atomFree target (openArgumentsVarAt target cutoff hcut args)
      | some index' =>
          .atomBound index' (openArgumentsVarAt target cutoff hcut args)
  | .neg body => .neg (openFormulaVarAt target cutoff hcut body)
  | .conj left right =>
      .conj (openFormulaVarAt target cutoff hcut left)
        (openFormulaVarAt target cutoff hcut right)
  | .disj left right =>
      .disj (openFormulaVarAt target cutoff hcut left)
        (openFormulaVarAt target cutoff hcut right)
  | .allVar profile body =>
      .allVar profile (openFormulaVarAt target (cutoff + 1) (by omega) body)
  | .existsVar profile body =>
      .existsVar profile (openFormulaVarAt target (cutoff + 1) (by omega) body)
  | .allFun profile body =>
      .allFun profile (openFormulaVarAt target cutoff hcut body)
  | .existsFun profile body =>
      .existsFun profile (openFormulaVarAt target cutoff hcut body)

def openArgumentsVarAt {varDepth funDepth : Nat} (target : VariableName)
    (cutoff : Nat) (hcut : cutoff ≤ varDepth) :
    Arguments (Nat.succ varDepth) funDepth → Arguments varDepth funDepth
  | .nil => .nil
  | .cons head tail =>
      .cons (openVarietyVarAt target cutoff hcut head)
        (openArgumentsVarAt target cutoff hcut tail)

end

mutual

def closeVarietyFunAt {varDepth funDepth : Nat} (target : FunctionName)
    (cutoff : Nat) (hcut : cutoff ≤ funDepth) :
    Variety varDepth funDepth → Variety varDepth (Nat.succ funDepth)
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar index
  | .freeFunApp name args =>
      let args' := closeArgumentsFunAt target cutoff hcut args
      if name = target then .boundFunApp (newFin cutoff hcut) args'
      else .freeFunApp name args'
  | .specialFunApp name args =>
      .specialFunApp name (closeArgumentsFunAt target cutoff hcut args)
  | .boundFunApp index args =>
      .boundFunApp (insertFin cutoff hcut index)
        (closeArgumentsFunAt target cutoff hcut args)
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (closeFormulaFunAt target cutoff hcut body)

def closeFormulaFunAt {varDepth funDepth : Nat} (target : FunctionName)
    (cutoff : Nat) (hcut : cutoff ≤ funDepth) :
    Formula varDepth funDepth → Formula varDepth (Nat.succ funDepth)
  | .atomFree name args =>
      .atomFree name (closeArgumentsFunAt target cutoff hcut args)
  | .atomSpecial name args =>
      .atomSpecial name (closeArgumentsFunAt target cutoff hcut args)
  | .atomBound index args =>
      .atomBound index (closeArgumentsFunAt target cutoff hcut args)
  | .neg body => .neg (closeFormulaFunAt target cutoff hcut body)
  | .conj left right =>
      .conj (closeFormulaFunAt target cutoff hcut left)
        (closeFormulaFunAt target cutoff hcut right)
  | .disj left right =>
      .disj (closeFormulaFunAt target cutoff hcut left)
        (closeFormulaFunAt target cutoff hcut right)
  | .allVar profile body =>
      .allVar profile (closeFormulaFunAt target cutoff hcut body)
  | .existsVar profile body =>
      .existsVar profile (closeFormulaFunAt target cutoff hcut body)
  | .allFun profile body =>
      .allFun profile (closeFormulaFunAt target (cutoff + 1) (by omega) body)
  | .existsFun profile body =>
      .existsFun profile (closeFormulaFunAt target (cutoff + 1) (by omega) body)

def closeArgumentsFunAt {varDepth funDepth : Nat} (target : FunctionName)
    (cutoff : Nat) (hcut : cutoff ≤ funDepth) :
    Arguments varDepth funDepth → Arguments varDepth (Nat.succ funDepth)
  | .nil => .nil
  | .cons head tail =>
      .cons (closeVarietyFunAt target cutoff hcut head)
        (closeArgumentsFunAt target cutoff hcut tail)

end

mutual

def openVarietyFunAt {varDepth funDepth : Nat} (target : FunctionName)
    (cutoff : Nat) (hcut : cutoff ≤ funDepth) :
    Variety varDepth (Nat.succ funDepth) → Variety varDepth funDepth
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar index
  | .freeFunApp name args =>
      .freeFunApp name (openArgumentsFunAt target cutoff hcut args)
  | .specialFunApp name args =>
      .specialFunApp name (openArgumentsFunAt target cutoff hcut args)
  | .boundFunApp index args =>
      let args' := openArgumentsFunAt target cutoff hcut args
      match removeFin cutoff hcut index with
      | none => .freeFunApp target args'
      | some index' => .boundFunApp index' args'
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (openFormulaFunAt target cutoff hcut body)

def openFormulaFunAt {varDepth funDepth : Nat} (target : FunctionName)
    (cutoff : Nat) (hcut : cutoff ≤ funDepth) :
    Formula varDepth (Nat.succ funDepth) → Formula varDepth funDepth
  | .atomFree name args =>
      .atomFree name (openArgumentsFunAt target cutoff hcut args)
  | .atomSpecial name args =>
      .atomSpecial name (openArgumentsFunAt target cutoff hcut args)
  | .atomBound index args =>
      .atomBound index (openArgumentsFunAt target cutoff hcut args)
  | .neg body => .neg (openFormulaFunAt target cutoff hcut body)
  | .conj left right =>
      .conj (openFormulaFunAt target cutoff hcut left)
        (openFormulaFunAt target cutoff hcut right)
  | .disj left right =>
      .disj (openFormulaFunAt target cutoff hcut left)
        (openFormulaFunAt target cutoff hcut right)
  | .allVar profile body =>
      .allVar profile (openFormulaFunAt target cutoff hcut body)
  | .existsVar profile body =>
      .existsVar profile (openFormulaFunAt target cutoff hcut body)
  | .allFun profile body =>
      .allFun profile (openFormulaFunAt target (cutoff + 1) (by omega) body)
  | .existsFun profile body =>
      .existsFun profile (openFormulaFunAt target (cutoff + 1) (by omega) body)

def openArgumentsFunAt {varDepth funDepth : Nat} (target : FunctionName)
    (cutoff : Nat) (hcut : cutoff ≤ funDepth) :
    Arguments varDepth (Nat.succ funDepth) → Arguments varDepth funDepth
  | .nil => .nil
  | .cons head tail =>
      .cons (openVarietyFunAt target cutoff hcut head)
        (openArgumentsFunAt target cutoff hcut tail)

end

def closeVarietyVar {varDepth funDepth : Nat} (target : VariableName) :
    Variety varDepth funDepth → Variety (Nat.succ varDepth) funDepth :=
  closeVarietyVarAt target 0 (Nat.zero_le varDepth)

def closeFormulaVar {varDepth funDepth : Nat} (target : VariableName) :
    Formula varDepth funDepth → Formula (Nat.succ varDepth) funDepth :=
  closeFormulaVarAt target 0 (Nat.zero_le varDepth)

def openVarietyVar {varDepth funDepth : Nat} (target : VariableName) :
    Variety (Nat.succ varDepth) funDepth → Variety varDepth funDepth :=
  openVarietyVarAt target 0 (Nat.zero_le varDepth)

def openFormulaVar {varDepth funDepth : Nat} (target : VariableName) :
    Formula (Nat.succ varDepth) funDepth → Formula varDepth funDepth :=
  openFormulaVarAt target 0 (Nat.zero_le varDepth)

def closeVarietyFun {varDepth funDepth : Nat} (target : FunctionName) :
    Variety varDepth funDepth → Variety varDepth (Nat.succ funDepth) :=
  closeVarietyFunAt target 0 (Nat.zero_le funDepth)

def closeFormulaFun {varDepth funDepth : Nat} (target : FunctionName) :
    Formula varDepth funDepth → Formula varDepth (Nat.succ funDepth) :=
  closeFormulaFunAt target 0 (Nat.zero_le funDepth)

def openVarietyFun {varDepth funDepth : Nat} (target : FunctionName) :
    Variety varDepth (Nat.succ funDepth) → Variety varDepth funDepth :=
  openVarietyFunAt target 0 (Nat.zero_le funDepth)

def openFormulaFun {varDepth funDepth : Nat} (target : FunctionName) :
    Formula varDepth (Nat.succ funDepth) → Formula varDepth funDepth :=
  openFormulaFunAt target 0 (Nat.zero_le funDepth)

/-- Close a list of free variable names one at a time. -/
def closeFormulaVarBlock {varDepth funDepth : Nat} :
    (names : List VariableName) → Formula varDepth funDepth →
      Formula (varDepth + names.length) funDepth
  | [], body => body
  | name :: names, body =>
      closeFormulaVar name (closeFormulaVarBlock names body)

/-- Open a block previously closed by `closeFormulaVarBlock`. -/
def openFormulaVarBlock {varDepth funDepth : Nat} :
    (names : List VariableName) → Formula (varDepth + names.length) funDepth →
      Formula varDepth funDepth
  | [], body => body
  | name :: names, body =>
      openFormulaVarBlock names (openFormulaVar name body)

@[simp] theorem removeFin_insertFin {depth : Nat} (cutoff : Nat)
    (hcut : cutoff ≤ depth) (index : Fin depth) :
    removeFin cutoff hcut (insertFin cutoff hcut index) = some index := by
  by_cases h : index.val < cutoff
  · simp [insertFin, removeFin, h]
  · have hge : cutoff ≤ index.val := Nat.le_of_not_gt h
    have hnotlt : ¬ index.val + 1 < cutoff := by omega
    have hne : index.val + 1 ≠ cutoff := by omega
    simp [insertFin, removeFin, h, hnotlt, hne]

@[simp] theorem open_close_freeVar {varDepth funDepth : Nat}
    (target : VariableName) :
    openVarietyVar target
        (closeVarietyVar target (.freeVar target : Variety varDepth funDepth)) =
      .freeVar target := by
  simp [openVarietyVar, closeVarietyVar, openVarietyVarAt, closeVarietyVarAt,
    newFin, removeFin]

@[simp] theorem open_close_boundVar {varDepth funDepth : Nat}
    (target : VariableName) (index : Fin varDepth) :
    openVarietyVar target
        (closeVarietyVar target (.boundVar index : Variety varDepth funDepth)) =
      .boundVar index := by
  simp [openVarietyVar, closeVarietyVar, openVarietyVarAt, closeVarietyVarAt,
    insertFin, removeFin]

@[simp] theorem open_close_freeFunApp_nil {varDepth funDepth : Nat}
    (target : FunctionName) :
    openVarietyFun target
        (closeVarietyFun target
          (.freeFunApp target .nil : Variety varDepth funDepth)) =
      .freeFunApp target .nil := by
  simp [openVarietyFun, closeVarietyFun, openVarietyFunAt, closeVarietyFunAt,
    newFin, removeFin, openArgumentsFunAt, closeArgumentsFunAt]

end TakeutiGLC.Experiment.DeBruijn
