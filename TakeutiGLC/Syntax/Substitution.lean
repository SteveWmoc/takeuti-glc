import TakeutiGLC.Syntax.SelectedClosing

/-!
# Height-zero variable substitution

Takeuti begins the complete-substitution construction in §5.2 with variables
of height zero. In that case the substituted variable is a free variable of
type `(0)` and the replacement is a term.

The stable locally nameless core does not need the source-level fresh bound
names used in Takeuti's clauses 5.2.5 and 5.2.8. Instead, when substitution
crosses a binder, the replacement is weakened in exactly that binder
namespace. Crossing a Takeuti abstraction block weakens it by the whole block
size. This is the capture-avoiding content of the height-zero construction.

The functions below are raw syntax transformations. Their intended
source-faithful use has

* `target.profile = TypeProfile.zero`, and
* the replacement well typed as a term.

Typing and scope preservation are separate metatheorems.
-/

namespace TakeutiGLC

namespace Variety

/-- Weaken a variety by `count` fresh outer variable binders. -/
def weakenVarBy : Nat → Variety → Variety
  | 0, variety => variety
  | Nat.succ count, variety => weakenVarBy count variety.weakenVar

/-- Weaken a variety by `count` fresh outer function binders. -/
def weakenFunBy : Nat → Variety → Variety
  | 0, variety => variety
  | Nat.succ count, variety => weakenFunBy count variety.weakenFun

@[simp] theorem weakenVarBy_zero (variety : Variety) :
    variety.weakenVarBy 0 = variety := rfl

@[simp] theorem weakenVarBy_succ (count : Nat) (variety : Variety) :
    variety.weakenVarBy (Nat.succ count) = (variety.weakenVar).weakenVarBy count := rfl

@[simp] theorem weakenFunBy_zero (variety : Variety) :
    variety.weakenFunBy 0 = variety := rfl

@[simp] theorem weakenFunBy_succ (count : Nat) (variety : Variety) :
    variety.weakenFunBy (Nat.succ count) = (variety.weakenFun).weakenFunBy count := rfl

end Variety

mutual

/--
Capture-avoiding substitution of a term for a free height-zero variable in a
variety.

The replacement is not recursively substituted into itself, matching Takeuti's
clause 5.2.3.
-/
def Variety.substituteBaseVar
    (target : VariableName) (replacement : Variety) : Variety → Variety
  | .freeVar name =>
      if name = target then replacement else .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar index
  | .freeFunApp name args =>
      .freeFunApp name (args.map (Variety.substituteBaseVar target replacement))
  | .specialFunApp name args =>
      .specialFunApp name (args.map (Variety.substituteBaseVar target replacement))
  | .boundFunApp index args =>
      .boundFunApp index (args.map (Variety.substituteBaseVar target replacement))
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (Formula.substituteBaseVar target
          (replacement.weakenVarBy (blockSize tailLevels)) body)

/-- Capture-avoiding height-zero variable substitution in a formula. -/
def Formula.substituteBaseVar
    (target : VariableName) (replacement : Variety) : Formula → Formula
  | .atomFree name args =>
      .atomFree name (args.map (Variety.substituteBaseVar target replacement))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (Variety.substituteBaseVar target replacement))
  | .atomBound index args =>
      .atomBound index (args.map (Variety.substituteBaseVar target replacement))
  | .neg body =>
      .neg (Formula.substituteBaseVar target replacement body)
  | .conj left right =>
      .conj
        (Formula.substituteBaseVar target replacement left)
        (Formula.substituteBaseVar target replacement right)
  | .disj left right =>
      .disj
        (Formula.substituteBaseVar target replacement left)
        (Formula.substituteBaseVar target replacement right)
  | .allVar profile body =>
      .allVar profile
        (Formula.substituteBaseVar target replacement.weakenVar body)
  | .existsVar profile body =>
      .existsVar profile
        (Formula.substituteBaseVar target replacement.weakenVar body)
  | .allFun profile body =>
      .allFun profile
        (Formula.substituteBaseVar target replacement.weakenFun body)
  | .existsFun profile body =>
      .existsFun profile
        (Formula.substituteBaseVar target replacement.weakenFun body)

end

namespace Functional

/--
Capture-avoiding height-zero variable substitution through a functional.

The functional's own abstraction block is already bound in the body, so a
replacement entering that body is weakened by the full block size.
-/
def substituteBaseVar
    (target : VariableName) (replacement : Variety) : Functional → Functional
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (Variety.substituteBaseVar target
          (replacement.weakenVarBy (blockSize tailLevels)) body)

end Functional

namespace Variety

@[simp] theorem substituteBaseVar_self
    (target : VariableName) (replacement : Variety) :
    Variety.substituteBaseVar target replacement (Variety.freeVar target) = replacement := by
  simp [Variety.substituteBaseVar]

@[simp] theorem substituteBaseVar_other
    (target name : VariableName) (replacement : Variety) (h : name ≠ target) :
    Variety.substituteBaseVar target replacement (Variety.freeVar name) = .freeVar name := by
  simp [Variety.substituteBaseVar, h]

@[simp] theorem substituteBaseVar_special
    (target name : VariableName) (replacement : Variety) :
    Variety.substituteBaseVar target replacement (Variety.specialVar name) = .specialVar name := by
  simp [Variety.substituteBaseVar]

@[simp] theorem substituteBaseVar_bound
    (target : VariableName) (replacement : Variety) (index : Nat) :
    Variety.substituteBaseVar target replacement (Variety.boundVar index) = .boundVar index := by
  simp [Variety.substituteBaseVar]

end Variety

namespace Formula

@[simp] theorem substituteBaseVar_allVar
    (target : VariableName) (replacement : Variety)
    (profile : TypeProfile) (body : Formula) :
    (Formula.allVar profile body).substituteBaseVar target replacement =
      .allVar profile (body.substituteBaseVar target replacement.weakenVar) := by
  simp [Formula.substituteBaseVar]

@[simp] theorem substituteBaseVar_allFun
    (target : VariableName) (replacement : Variety)
    (profile : FunctionProfile) (body : Formula) :
    (Formula.allFun profile body).substituteBaseVar target replacement =
      .allFun profile (body.substituteBaseVar target replacement.weakenFun) := by
  simp [Formula.substituteBaseVar]

end Formula

namespace Functional

@[simp] theorem substituteBaseVar_abstract
    (target : VariableName) (replacement : Variety)
    (headLevel : Nat) (tailLevels : List Nat) (body : Variety) :
    (Functional.abstract headLevel tailLevels body).substituteBaseVar target replacement =
      .abstract headLevel tailLevels
        (Variety.substituteBaseVar target
          (replacement.weakenVarBy (blockSize tailLevels)) body) := by
  simp [Functional.substituteBaseVar]

end Functional

end TakeutiGLC
