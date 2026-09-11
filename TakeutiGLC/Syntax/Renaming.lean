import Mathlib.Tactic
import TakeutiGLC.Syntax.OpenClose

/-!
# Renaming and weakening for the stable GLC syntax

The locally nameless core has two independent namespaces of bound indices:
variables and functions. A `Renaming` therefore carries one map for each
namespace. Free and special names are unaffected.

Renamings are lifted when syntax crosses a binder. A variable binder lifts only
the variable map, a function binder lifts only the function map, and a Takeuti
abstraction block lifts the variable map by the full block size.

Weakening is the special renaming that inserts one fresh slot at a chosen
cutoff. These operations are the structural substrate for the substitution
machinery developed later in Milestone 2.
-/

namespace TakeutiGLC

/-- A simultaneous renaming of the independent bound-variable and bound-function namespaces. -/
structure Renaming where
  varMap : Nat → Nat
  funMap : Nat → Nat

namespace Renaming

/-- Identity renaming in both namespaces. -/
def identity : Renaming :=
  ⟨fun index => index, fun index => index⟩

/-- Composition, applying `inner` first and `outer` second. -/
def comp (outer inner : Renaming) : Renaming :=
  ⟨fun index => outer.varMap (inner.varMap index),
   fun index => outer.funMap (inner.funMap index)⟩

/-- Lift one de Bruijn-index map under a fresh binder. -/
def liftIndex (rename : Nat → Nat) : Nat → Nat
  | 0 => 0
  | Nat.succ index => Nat.succ (rename index)

/-- Lift one index map under `count` fresh binders. -/
def liftIndexBy : Nat → (Nat → Nat) → Nat → Nat
  | 0, rename => rename
  | Nat.succ count, rename => liftIndex (liftIndexBy count rename)

/-- Lift a renaming under one variable quantifier. -/
def underVar (rename : Renaming) : Renaming :=
  { rename with varMap := liftIndex rename.varMap }

/-- Lift a renaming under one function quantifier. -/
def underFun (rename : Renaming) : Renaming :=
  { rename with funMap := liftIndex rename.funMap }

/-- Lift a renaming under a nonempty Takeuti variable-abstraction block. -/
def underBlock (rename : Renaming) (tailLevels : List Nat) : Renaming :=
  { rename with varMap := liftIndexBy (blockSize tailLevels) rename.varMap }

/-- Insert one fresh variable slot at `cutoff`, leaving the function namespace fixed. -/
def weakenVarAt (cutoff : Nat) : Renaming :=
  ⟨insertIndex cutoff, fun index => index⟩

/-- Insert one fresh function slot at `cutoff`, leaving the variable namespace fixed. -/
def weakenFunAt (cutoff : Nat) : Renaming :=
  ⟨fun index => index, insertIndex cutoff⟩

@[simp] theorem liftIndex_zero (rename : Nat → Nat) : liftIndex rename 0 = 0 := rfl

@[simp] theorem liftIndex_succ (rename : Nat → Nat) (index : Nat) :
    liftIndex rename (Nat.succ index) = Nat.succ (rename index) := rfl

@[simp] theorem liftIndexBy_zero (rename : Nat → Nat) :
    liftIndexBy 0 rename = rename := rfl

@[simp] theorem liftIndexBy_succ (count : Nat) (rename : Nat → Nat) :
    liftIndexBy (Nat.succ count) rename = liftIndex (liftIndexBy count rename) := rfl

@[simp] theorem identity_underVar : identity.underVar = identity := by
  apply Renaming.ext <;> funext index <;> cases index <;> rfl

@[simp] theorem identity_underFun : identity.underFun = identity := by
  apply Renaming.ext <;> funext index <;> cases index <;> rfl

end Renaming

mutual

/-- Rename bound indices in a variety. -/
def Variety.rename (rename : Renaming) : Variety → Variety
  | .freeVar name => .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar (rename.varMap index)
  | .freeFunApp name args =>
      .freeFunApp name (args.map (Variety.rename rename))
  | .specialFunApp name args =>
      .specialFunApp name (args.map (Variety.rename rename))
  | .boundFunApp index args =>
      .boundFunApp (rename.funMap index) (args.map (Variety.rename rename))
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (Formula.rename (rename.underBlock tailLevels) body)

/-- Rename bound indices in a formula. -/
def Formula.rename (rename : Renaming) : Formula → Formula
  | .atomFree name args =>
      .atomFree name (args.map (Variety.rename rename))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (Variety.rename rename))
  | .atomBound index args =>
      .atomBound (rename.varMap index) (args.map (Variety.rename rename))
  | .neg body => .neg (Formula.rename rename body)
  | .conj left right =>
      .conj (Formula.rename rename left) (Formula.rename rename right)
  | .disj left right =>
      .disj (Formula.rename rename left) (Formula.rename rename right)
  | .allVar profile body =>
      .allVar profile (Formula.rename rename.underVar body)
  | .existsVar profile body =>
      .existsVar profile (Formula.rename rename.underVar body)
  | .allFun profile body =>
      .allFun profile (Formula.rename rename.underFun body)
  | .existsFun profile body =>
      .existsFun profile (Formula.rename rename.underFun body)

end

namespace Functional

/-- Rename bound indices in a functional. -/
def rename (rename : Renaming) : Functional → Functional
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels (body.rename (rename.underBlock tailLevels))

end Functional

namespace Variety

/-- Insert one fresh variable slot at `cutoff`. -/
def weakenVarAt (cutoff : Nat) (variety : Variety) : Variety :=
  variety.rename (Renaming.weakenVarAt cutoff)

/-- Insert one fresh function slot at `cutoff`. -/
def weakenFunAt (cutoff : Nat) (variety : Variety) : Variety :=
  variety.rename (Renaming.weakenFunAt cutoff)

/-- Insert a fresh outermost variable slot. -/
def weakenVar : Variety → Variety := weakenVarAt 0

/-- Insert a fresh outermost function slot. -/
def weakenFun : Variety → Variety := weakenFunAt 0

end Variety

namespace Formula

/-- Insert one fresh variable slot at `cutoff`. -/
def weakenVarAt (cutoff : Nat) (formula : Formula) : Formula :=
  formula.rename (Renaming.weakenVarAt cutoff)

/-- Insert one fresh function slot at `cutoff`. -/
def weakenFunAt (cutoff : Nat) (formula : Formula) : Formula :=
  formula.rename (Renaming.weakenFunAt cutoff)

/-- Insert a fresh outermost variable slot. -/
def weakenVar : Formula → Formula := weakenVarAt 0

/-- Insert a fresh outermost function slot. -/
def weakenFun : Formula → Formula := weakenFunAt 0

end Formula

namespace Functional

/-- Insert one fresh variable slot outside the functional's own abstraction block. -/
def weakenVarAt (cutoff : Nat) (functional : Functional) : Functional :=
  functional.rename (Renaming.weakenVarAt cutoff)

/-- Insert one fresh function slot outside the functional. -/
def weakenFunAt (cutoff : Nat) (functional : Functional) : Functional :=
  functional.rename (Renaming.weakenFunAt cutoff)

/-- Insert a fresh outermost variable slot outside the functional. -/
def weakenVar : Functional → Functional := weakenVarAt 0

/-- Insert a fresh outermost function slot outside the functional. -/
def weakenFun : Functional → Functional := weakenFunAt 0

end Functional

@[simp] theorem Variety.rename_boundVar (rename : Renaming) (index : Nat) :
    (Variety.boundVar index).rename rename = .boundVar (rename.varMap index) := rfl

@[simp] theorem Variety.rename_boundFunApp_nil (rename : Renaming) (index : Nat) :
    (Variety.boundFunApp index []).rename rename = .boundFunApp (rename.funMap index) [] := rfl

@[simp] theorem Variety.weakenVar_boundVar (index : Nat) :
    (Variety.boundVar index).weakenVar = .boundVar (index + 1) := by
  simp [Variety.weakenVar, Variety.weakenVarAt, Renaming.weakenVarAt,
    Variety.rename, insertIndex]

@[simp] theorem Variety.weakenFun_boundFunApp_nil (index : Nat) :
    (Variety.boundFunApp index []).weakenFun = .boundFunApp (index + 1) [] := by
  simp [Variety.weakenFun, Variety.weakenFunAt, Renaming.weakenFunAt,
    Variety.rename, insertIndex]

end TakeutiGLC
