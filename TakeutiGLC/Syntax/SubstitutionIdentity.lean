import TakeutiGLC.Syntax.Substitution

/-!
# Substitution for an absent free variable

The first algebraic slice for complete substitution: when the target has no
free occurrence, substitution succeeds and returns exactly the original raw
syntax. No typing or scope assumptions on the expression or replacement are
needed. Both variable and function binders are covered.

This is a supporting law for the remaining Takeuti §5.2 identity/commutation
metatheory; it does not yet assert §§5.2.33–5.2.35.
-/

namespace TakeutiGLC

mutual

/-- Structural absence of a named free variable, including atomic heads. -/
def Variety.FreeVariableAbsent (target : VariableName) : Variety → Prop
  | .freeVar name => name ≠ target
  | .specialVar _ | .boundVar _ => True
  | .freeFunApp _ args | .specialFunApp _ args | .boundFunApp _ args =>
      FreeVariableAbsentArgs target args
  | .abstract _ _ body => body.FreeVariableAbsent target

/-- Structural absence counts free atomic heads as well as argument occurrences. -/
def Formula.FreeVariableAbsent (target : VariableName) : Formula → Prop
  | .atomFree name args => name ≠ target ∧ FreeVariableAbsentArgs target args
  | .atomSpecial _ args | .atomBound _ args => FreeVariableAbsentArgs target args
  | .neg body | .allVar _ body | .existsVar _ body
  | .allFun _ body | .existsFun _ body => body.FreeVariableAbsent target
  | .conj left right | .disj left right =>
      left.FreeVariableAbsent target ∧ right.FreeVariableAbsent target

/-- Absence from every argument, traversing higher-type abstractions too. -/
def FreeVariableAbsentArgs (target : VariableName) : List Variety → Prop
  | [] => True
  | arg :: args => arg.FreeVariableAbsent target ∧ FreeVariableAbsentArgs target args

end

/-- A functional has no free target occurrence exactly when its body has none. -/
def Functional.FreeVariableAbsent (target : VariableName) : Functional → Prop
  | .abstract _ _ body => body.FreeVariableAbsent target

/-- The recursive argument predicate is ordinary absence from each list member. -/
theorem freeVariableAbsentArgs_iff_forall
    (target : VariableName) (args : List Variety) :
    FreeVariableAbsentArgs target args ↔ ∀ arg ∈ args, arg.FreeVariableAbsent target := by
  induction args with
  | nil => simp [FreeVariableAbsentArgs]
  | cons arg args ih => simp [FreeVariableAbsentArgs, ih]

mutual

/-- Substitution for an absent variable succeeds and fixes a variety. -/
theorem Variety.completeSubstituteVar_of_absent
    (target : VariableName) (replacement : Variety) (variety : Variety)
    (h : variety.FreeVariableAbsent target) :
    Variety.completeSubstituteVar? target replacement variety = some variety := by
  cases variety with
  | freeVar name =>
      simp only [Variety.FreeVariableAbsent] at h
      simp [Variety.completeSubstituteVar?, h]
  | specialVar name => rfl
  | boundVar index => rfl
  | freeFunApp name args =>
      simp only [Variety.FreeVariableAbsent] at h
      simp [Variety.completeSubstituteVar?, completeSubstituteVarArgs_of_absent target replacement args h]
  | specialFunApp name args =>
      simp only [Variety.FreeVariableAbsent] at h
      simp [Variety.completeSubstituteVar?, completeSubstituteVarArgs_of_absent target replacement args h]
  | boundFunApp index args =>
      simp only [Variety.FreeVariableAbsent] at h
      simp [Variety.completeSubstituteVar?, completeSubstituteVarArgs_of_absent target replacement args h]
  | abstract head tail body =>
      simp only [Variety.FreeVariableAbsent] at h
      simp [Variety.completeSubstituteVar?, Formula.completeSubstituteVar_of_absent target
        (replacement.weakenVarBy (blockSize tail)) body h]
termination_by sizeOf variety

/-- Substitution for an absent variable succeeds and fixes a formula. -/
theorem Formula.completeSubstituteVar_of_absent
    (target : VariableName) (replacement : Variety) (formula : Formula)
    (h : formula.FreeVariableAbsent target) :
    formula.completeSubstituteVar? target replacement = some formula := by
  cases formula with
  | atomFree name args =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, h.1,
        completeSubstituteVarArgs_of_absent target replacement args h.2]
  | atomSpecial name args =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, completeSubstituteVarArgs_of_absent target replacement args h]
  | atomBound index args =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, completeSubstituteVarArgs_of_absent target replacement args h]
  | neg body =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteVar_of_absent target replacement body h]
  | conj left right =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteVar_of_absent target replacement left h.1,
        Formula.completeSubstituteVar_of_absent target replacement right h.2]
  | disj left right =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteVar_of_absent target replacement left h.1,
        Formula.completeSubstituteVar_of_absent target replacement right h.2]
  | allVar profile body =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteVar_of_absent target replacement.weakenVar body h]
  | existsVar profile body =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteVar_of_absent target replacement.weakenVar body h]
  | allFun profile body =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteVar_of_absent target replacement.weakenFun body h]
  | existsFun profile body =>
      simp only [Formula.FreeVariableAbsent] at h
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteVar_of_absent target replacement.weakenFun body h]
termination_by sizeOf formula

/-- Substitution for an absent variable succeeds and fixes an argument list. -/
theorem completeSubstituteVarArgs_of_absent
    (target : VariableName) (replacement : Variety) (args : List Variety)
    (h : FreeVariableAbsentArgs target args) :
    completeSubstituteVarArgs? target replacement args = some args := by
  cases args with
  | nil => rfl
  | cons arg args =>
      simp only [FreeVariableAbsentArgs] at h
      simp [completeSubstituteVarArgs?, Variety.completeSubstituteVar_of_absent target replacement arg h.1,
        completeSubstituteVarArgs_of_absent target replacement args h.2]
termination_by sizeOf args

end

/-- Substitution for an absent variable succeeds and fixes a functional. -/
theorem Functional.completeSubstituteVar_of_absent
    (target : VariableName) (replacement : Variety) (functional : Functional)
    (h : functional.FreeVariableAbsent target) :
    functional.completeSubstituteVar? target replacement = some functional := by
  cases functional with
  | abstract head tail body =>
      simp only [Functional.FreeVariableAbsent] at h
      simp [Functional.completeSubstituteVar?, Variety.completeSubstituteVar_of_absent target
        (replacement.weakenVarBy (blockSize tail)) body h]

/--
Regression: a special occurrence with the same name remains untouched beneath
mixed binders and an abstraction, even with a malformed replacement.
-/
theorem Formula.completeSubstituteVar_absent_mixedBinders
    (target : VariableName) (functionProfile : FunctionProfile) :
    let formula : Formula := .allFun functionProfile
      (.existsVar target.profile
        (.atomSpecial target [.abstract 0 [] (.atomSpecial target [])]))
    formula.completeSubstituteVar? target (.boundVar 999) = some formula := by
  apply Formula.completeSubstituteVar_of_absent
  simp [Formula.FreeVariableAbsent, Variety.FreeVariableAbsent, FreeVariableAbsentArgs]

/-- Regression: a free atomic head counts as an occurrence even with no arguments. -/
theorem Formula.not_freeVariableAbsent_atomFree (target : VariableName) :
    ¬ (Formula.atomFree target []).FreeVariableAbsent target := by
  simp [Formula.FreeVariableAbsent]

end TakeutiGLC
