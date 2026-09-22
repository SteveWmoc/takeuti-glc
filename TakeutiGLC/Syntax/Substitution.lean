import TakeutiGLC.Syntax.Instantiation

/-!
# Complete variable substitution

Takeuti begins the complete-substitution construction in §5.2 with variables
of height zero. In that case the substituted variable is a free variable of
type `(0)` and the replacement is a term.

The stable locally nameless core does not need the source-level fresh bound
names used in Takeuti's clauses 5.2.5 and 5.2.8. Instead, when substitution
crosses a binder, the replacement is weakened in exactly that binder
namespace. Crossing a Takeuti abstraction block weakens it by the whole block
size. This is the capture-avoiding content of the height-zero construction.

The functions below implement **complete** substitution: every occurrence of
the target free variable is replaced. Takeuti introduces substitution at only
indicated occurrences later, in §5.6; that selection-aware operation is not
conflated with the §5.2 complete-substitution kernel here.

The functions below are raw syntax transformations. Their intended
source-faithful use has

* `target.profile = TypeProfile.zero`, and
* the replacement well typed as a term.

Typing and scope preservation are separate metatheorems.

M2.8 also implements the first genuinely higher-type induction stage: targets
of height one. Such a target has profile `(1, ..., 1)`, so its replacement is
an abstraction over base-type variables. A target atomic occurrence is reduced
by recursively transforming its arguments and instantiating the replacement
abstraction with those arguments. The raw height-one operation returns
`Option` so malformed raw syntax or a mismatched replacement is rejected
instead of silently producing a figure that has no source-level meaning.
-/

namespace TakeutiGLC

mutual

/--
Capture-avoiding substitution of a term for a free height-zero variable in a
variety.

The replacement is not recursively substituted into itself, matching Takeuti's
clause 5.2.3.
-/
def Variety.completeSubstituteBaseVar
    (target : VariableName) (replacement : Variety) : Variety → Variety
  | .freeVar name =>
      if name = target then replacement else .freeVar name
  | .specialVar name => .specialVar name
  | .boundVar index => .boundVar index
  | .freeFunApp name args =>
      .freeFunApp name (args.map (Variety.completeSubstituteBaseVar target replacement))
  | .specialFunApp name args =>
      .specialFunApp name (args.map (Variety.completeSubstituteBaseVar target replacement))
  | .boundFunApp index args =>
      .boundFunApp index (args.map (Variety.completeSubstituteBaseVar target replacement))
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (Formula.completeSubstituteBaseVar target
          (replacement.weakenVarBy (blockSize tailLevels)) body)

/-- Capture-avoiding height-zero variable substitution in a formula. -/
def Formula.completeSubstituteBaseVar
    (target : VariableName) (replacement : Variety) : Formula → Formula
  | .atomFree name args =>
      .atomFree name (args.map (Variety.completeSubstituteBaseVar target replacement))
  | .atomSpecial name args =>
      .atomSpecial name (args.map (Variety.completeSubstituteBaseVar target replacement))
  | .atomBound index args =>
      .atomBound index (args.map (Variety.completeSubstituteBaseVar target replacement))
  | .neg body =>
      .neg (Formula.completeSubstituteBaseVar target replacement body)
  | .conj left right =>
      .conj
        (Formula.completeSubstituteBaseVar target replacement left)
        (Formula.completeSubstituteBaseVar target replacement right)
  | .disj left right =>
      .disj
        (Formula.completeSubstituteBaseVar target replacement left)
        (Formula.completeSubstituteBaseVar target replacement right)
  | .allVar profile body =>
      .allVar profile
        (Formula.completeSubstituteBaseVar target replacement.weakenVar body)
  | .existsVar profile body =>
      .existsVar profile
        (Formula.completeSubstituteBaseVar target replacement.weakenVar body)
  | .allFun profile body =>
      .allFun profile
        (Formula.completeSubstituteBaseVar target replacement.weakenFun body)
  | .existsFun profile body =>
      .existsFun profile
        (Formula.completeSubstituteBaseVar target replacement.weakenFun body)

end

namespace Functional

/--
Capture-avoiding height-zero variable substitution through a functional.

The functional's own abstraction block is already bound in the body, so a
replacement entering that body is weakened by the full block size.
-/
def completeSubstituteBaseVar
    (target : VariableName) (replacement : Variety) : Functional → Functional
  | .abstract headLevel tailLevels body =>
      .abstract headLevel tailLevels
        (Variety.completeSubstituteBaseVar target
          (replacement.weakenVarBy (blockSize tailLevels)) body)

end Functional

namespace Variety

@[simp] theorem completeSubstituteBaseVar_self
    (target : VariableName) (replacement : Variety) :
    Variety.completeSubstituteBaseVar target replacement (Variety.freeVar target) = replacement := by
  simp [Variety.completeSubstituteBaseVar]

@[simp] theorem completeSubstituteBaseVar_other
    (target name : VariableName) (replacement : Variety) (h : name ≠ target) :
    Variety.completeSubstituteBaseVar target replacement (Variety.freeVar name) = .freeVar name := by
  simp [Variety.completeSubstituteBaseVar, h]

@[simp] theorem completeSubstituteBaseVar_special
    (target name : VariableName) (replacement : Variety) :
    Variety.completeSubstituteBaseVar target replacement (Variety.specialVar name) = .specialVar name := by
  simp [Variety.completeSubstituteBaseVar]

@[simp] theorem completeSubstituteBaseVar_bound
    (target : VariableName) (replacement : Variety) (index : Nat) :
    Variety.completeSubstituteBaseVar target replacement (Variety.boundVar index) = .boundVar index := by
  simp [Variety.completeSubstituteBaseVar]

end Variety

namespace Formula

@[simp] theorem completeSubstituteBaseVar_allVar
    (target : VariableName) (replacement : Variety)
    (profile : TypeProfile) (body : Formula) :
    (Formula.allVar profile body).completeSubstituteBaseVar target replacement =
      .allVar profile (body.completeSubstituteBaseVar target replacement.weakenVar) := by
  simp [Formula.completeSubstituteBaseVar]

@[simp] theorem completeSubstituteBaseVar_allFun
    (target : VariableName) (replacement : Variety)
    (profile : FunctionProfile) (body : Formula) :
    (Formula.allFun profile body).completeSubstituteBaseVar target replacement =
      .allFun profile (body.completeSubstituteBaseVar target replacement.weakenFun) := by
  simp [Formula.completeSubstituteBaseVar]

end Formula

namespace Functional

@[simp] theorem completeSubstituteBaseVar_abstract
    (target : VariableName) (replacement : Variety)
    (headLevel : Nat) (tailLevels : List Nat) (body : Variety) :
    (Functional.abstract headLevel tailLevels body).completeSubstituteBaseVar target replacement =
      .abstract headLevel tailLevels
        (Variety.completeSubstituteBaseVar target
          (replacement.weakenVarBy (blockSize tailLevels)) body) := by
  simp [Functional.completeSubstituteBaseVar]

end Functional

mutual

/--
Capture-avoiding complete substitution for a free variable of height one.

The source-faithful case has `target.profile.height = 1` and a replacement
abstraction of the same profile. Matching atomic occurrences are beta-reduced
by instantiating the replacement's base-variable block with recursively
transformed arguments.
-/
def Variety.completeSubstituteHeightOneVar?
    (target : VariableName) (replacement : Variety) : Variety → Option Variety
  | .freeVar name =>
      if name = target then none else some (.freeVar name)
  | .specialVar name => some (.specialVar name)
  | .boundVar index => some (.boundVar index)
  | .freeFunApp name args => do
      let args' ← completeSubstituteHeightOneVarArgs? target replacement args
      some (.freeFunApp name args')
  | .specialFunApp name args => do
      let args' ← completeSubstituteHeightOneVarArgs? target replacement args
      some (.specialFunApp name args')
  | .boundFunApp index args => do
      let args' ← completeSubstituteHeightOneVarArgs? target replacement args
      some (.boundFunApp index args')
  | .abstract headLevel tailLevels body => do
      let body' ← Formula.completeSubstituteHeightOneVar? target
        (replacement.weakenVarBy (blockSize tailLevels)) body
      some (.abstract headLevel tailLevels body')

/-- Capture-avoiding height-one complete substitution in a formula. -/
def Formula.completeSubstituteHeightOneVar?
    (target : VariableName) (replacement : Variety) : Formula → Option Formula
  | .atomFree name args => do
      let args' ← completeSubstituteHeightOneVarArgs? target replacement args
      if name = target then
        match replacement with
        | .abstract headLevel tailLevels replacementBody =>
            if target.profile.height = 1 then
              if abstractionProfile headLevel tailLevels = target.profile then
                if args'.length = blockSize tailLevels then
                  Formula.instantiateBaseVarBlock? args' replacementBody
                else
                  none
              else
                none
            else
              none
        | _ => none
      else
        some (.atomFree name args')
  | .atomSpecial name args => do
      let args' ← completeSubstituteHeightOneVarArgs? target replacement args
      some (.atomSpecial name args')
  | .atomBound index args => do
      let args' ← completeSubstituteHeightOneVarArgs? target replacement args
      some (.atomBound index args')
  | .neg body => do
      let body' ← Formula.completeSubstituteHeightOneVar? target replacement body
      some (.neg body')
  | .conj left right => do
      let left' ← Formula.completeSubstituteHeightOneVar? target replacement left
      let right' ← Formula.completeSubstituteHeightOneVar? target replacement right
      some (.conj left' right')
  | .disj left right => do
      let left' ← Formula.completeSubstituteHeightOneVar? target replacement left
      let right' ← Formula.completeSubstituteHeightOneVar? target replacement right
      some (.disj left' right')
  | .allVar profile body => do
      let body' ← Formula.completeSubstituteHeightOneVar? target replacement.weakenVar body
      some (.allVar profile body')
  | .existsVar profile body => do
      let body' ← Formula.completeSubstituteHeightOneVar? target replacement.weakenVar body
      some (.existsVar profile body')
  | .allFun profile body => do
      let body' ← Formula.completeSubstituteHeightOneVar? target replacement.weakenFun body
      some (.allFun profile body')
  | .existsFun profile body => do
      let body' ← Formula.completeSubstituteHeightOneVar? target replacement.weakenFun body
      some (.existsFun profile body')

/-- Height-one complete substitution recursively through a variety argument list. -/
def completeSubstituteHeightOneVarArgs?
    (target : VariableName) (replacement : Variety) :
    List Variety → Option (List Variety)
  | [] => some []
  | arg :: args => do
      let arg' ← Variety.completeSubstituteHeightOneVar? target replacement arg
      let args' ← completeSubstituteHeightOneVarArgs? target replacement args
      some (arg' :: args')

end

namespace Functional

/-- Capture-avoiding height-one complete substitution through a functional. -/
def completeSubstituteHeightOneVar?
    (target : VariableName) (replacement : Variety) : Functional → Option Functional
  | .abstract headLevel tailLevels body => do
      let body' ← Variety.completeSubstituteHeightOneVar? target
        (replacement.weakenVarBy (blockSize tailLevels)) body
      some (.abstract headLevel tailLevels body')

end Functional

namespace Formula

/--
Regression test for the first higher-type beta-reduction case.

A type-`(1)` variable replaced by the abstraction `{x} P[x]` reduces
`α[t]` to `P[t]`.
-/
theorem completeSubstituteHeightOneVar_beta
    (predicate : VariableName) (argument : Variety) :
    let target : VariableName := ⟨.higher 0 [], 0⟩
    let replacement : Variety :=
      .abstract 0 [] (.atomSpecial predicate [.boundVar 0])
    Formula.completeSubstituteHeightOneVar? target replacement
      (.atomFree target [argument]) =
        some (.atomSpecial predicate [argument]) := by
  simp [Formula.completeSubstituteHeightOneVar?, completeSubstituteHeightOneVarArgs?,
    Formula.instantiateBaseVarBlock?, Formula.instantiateBaseVarBlockAt?,
    instantiateBaseVarBlockArgsAt?, Variety.instantiateBaseVarBlockAt?,
    Variety.liftIntoScope, abstractionProfile, blockSize]

end Formula


end TakeutiGLC
