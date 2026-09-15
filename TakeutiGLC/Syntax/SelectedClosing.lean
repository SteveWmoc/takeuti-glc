import TakeutiGLC.Syntax.Renaming

/-!
# Selection-aware closing

Takeuti's §3.1 indication notation may select only some occurrences of a free
variable. Section 3.2 then abstracts exactly those indicated occurrences when
forming a functional; unindicated occurrences of the same free name remain
free.

The ordinary closing operations in `Syntax/OpenClose.lean` intentionally close
all occurrences of a name. This module adds the complementary path-sensitive
operation. The selected occurrence paths are auxiliary metadata from
`Syntax/Occurrence.lean`; they do not become part of raw syntax identity.

Closing still introduces a genuine de Bruijn slot, so pre-existing bound
variable indices are shifted even when the selection is empty. Variable and
function binder namespaces remain independent.
-/

namespace TakeutiGLC

mutual

/--
Close the selected free-variable occurrences in a variety while threading the
current structural path.
-/
def Variety.closeSelectedVarAtPath
    (selection : VariableOccurrenceSelection) (cutoff : Nat)
    (path : OccurrencePath) : Variety → Variety
  | .freeVar name =>
      if path ∈ selection.paths then
        if name = selection.name then .boundVar cutoff else .freeVar name
      else
        .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar (insertIndex cutoff index)
  | .freeFunApp name args =>
      .freeFunApp name
        (closeSelectedVarArgsAtPath selection cutoff path 0 args)
  | .specialFunApp name args =>
      .specialFunApp name
        (closeSelectedVarArgsAtPath selection cutoff path 0 args)
  | .boundFunApp index args =>
      .boundFunApp index
        (closeSelectedVarArgsAtPath selection cutoff path 0 args)
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (Formula.closeSelectedVarAtPath selection
          (blockSize tailLevels + cutoff)
          (path ++ [.abstractionBody]) body)

/--
Close the selected free-variable occurrences in a formula while threading the
current structural path.
-/
def Formula.closeSelectedVarAtPath
    (selection : VariableOccurrenceSelection) (cutoff : Nat)
    (path : OccurrencePath) : Formula → Formula
  | .atomFree name args =>
      let args' := closeSelectedVarArgsAtPath selection cutoff path 0 args
      if path ∈ selection.paths then
        if name = selection.name then .atomBound cutoff args' else .atomFree name args'
      else
        .atomFree name args'
  | .atomSpecial name args =>
      .atomSpecial name
        (closeSelectedVarArgsAtPath selection cutoff path 0 args)
  | .atomBound index args =>
      .atomBound (insertIndex cutoff index)
        (closeSelectedVarArgsAtPath selection cutoff path 0 args)
  | .neg body =>
      .neg (Formula.closeSelectedVarAtPath selection cutoff (path ++ [.body]) body)
  | .conj left right =>
      .conj
        (Formula.closeSelectedVarAtPath selection cutoff (path ++ [.left]) left)
        (Formula.closeSelectedVarAtPath selection cutoff (path ++ [.right]) right)
  | .disj left right =>
      .disj
        (Formula.closeSelectedVarAtPath selection cutoff (path ++ [.left]) left)
        (Formula.closeSelectedVarAtPath selection cutoff (path ++ [.right]) right)
  | .allVar profile body =>
      .allVar profile
        (Formula.closeSelectedVarAtPath selection (cutoff + 1) (path ++ [.body]) body)
  | .existsVar profile body =>
      .existsVar profile
        (Formula.closeSelectedVarAtPath selection (cutoff + 1) (path ++ [.body]) body)
  | .allFun profile body =>
      .allFun profile
        (Formula.closeSelectedVarAtPath selection cutoff (path ++ [.body]) body)
  | .existsFun profile body =>
      .existsFun profile
        (Formula.closeSelectedVarAtPath selection cutoff (path ++ [.body]) body)

/-- Close selected occurrences recursively in a list of variety arguments. -/
def closeSelectedVarArgsAtPath
    (selection : VariableOccurrenceSelection) (cutoff : Nat)
    (path : OccurrencePath) (index : Nat) : List Variety → List Variety
  | [] => []
  | arg :: args =>
      Variety.closeSelectedVarAtPath selection cutoff
          (path ++ [.argument index]) arg ::
        closeSelectedVarArgsAtPath selection cutoff path (index + 1) args

end

namespace Variety

/-- Close exactly the selected variable occurrences into a fresh slot at `cutoff`. -/
def closeSelectedVarAt
    (selection : VariableOccurrenceSelection) (cutoff : Nat) (variety : Variety) : Variety :=
  closeSelectedVarAtPath selection cutoff [] variety

/-- Close exactly the selected variable occurrences into a fresh outermost slot. -/
def closeSelectedVar
    (selection : VariableOccurrenceSelection) (variety : Variety) : Variety :=
  variety.closeSelectedVarAt selection 0

/--
Close a simultaneous block of indicated variable selections.

Selections are listed in Takeuti's display order. Folding from the right leaves
the first displayed selection at de Bruijn index `0`, matching `closeVarBlock`.
-/
def closeSelectedVarBlock
    (selections : List VariableOccurrenceSelection) (body : Variety) : Variety :=
  selections.foldr (fun selection body' => body'.closeSelectedVar selection) body

end Variety

namespace Formula

/-- Close exactly the selected variable occurrences into a fresh slot at `cutoff`. -/
def closeSelectedVarAt
    (selection : VariableOccurrenceSelection) (cutoff : Nat) (formula : Formula) : Formula :=
  closeSelectedVarAtPath selection cutoff [] formula

/-- Close exactly the selected variable occurrences into a fresh outermost slot. -/
def closeSelectedVar
    (selection : VariableOccurrenceSelection) (formula : Formula) : Formula :=
  formula.closeSelectedVarAt selection 0

/-- Close a simultaneous block of indicated selections in display order. -/
def closeSelectedVarBlock
    (selections : List VariableOccurrenceSelection) (body : Formula) : Formula :=
  selections.foldr (fun selection body' => body'.closeSelectedVar selection) body

end Formula

namespace Functional

/--
Close selected variable occurrences into a binder outside a functional's own
abstraction block. Functional occurrence paths begin with `abstractionBody`.
-/
def closeSelectedVarAt
    (selection : VariableOccurrenceSelection) (cutoff : Nat) : Functional → Functional
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (Variety.closeSelectedVarAtPath selection
          (blockSize tailLevels + cutoff) [.abstractionBody] body)

end Functional

end TakeutiGLC
