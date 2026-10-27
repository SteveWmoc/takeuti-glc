import TakeutiGLC.Syntax.Substitution

/-!
# Height-zero complete-substitution identities

This module proves the height-zero stages of Takeuti §§5.2.33–5.2.34 for the
unified arbitrary-height driver. A base variable represents its own identity
variety, so substituting it for itself fixes every well-typed expression.
Substitution into the variable itself returns the replacement.

Formation matters: the raw syntax permits a base variable as an atomic head,
where the partial substitution driver correctly fails. The identity theorem
therefore uses the extrinsic formation judgments. Higher-type identities need
identity abstractions and hereditary beta/eta reasoning and remain separate.
-/

namespace TakeutiGLC

namespace Variety

/-- Weakening bound variables leaves a named free variable unchanged. -/
@[simp] theorem weakenVar_freeVar (name : VariableName) :
    (Variety.freeVar name).weakenVar = .freeVar name := by
  simp [Variety.weakenVar, Variety.weakenVarAt, Variety.rename]

/-- Weakening bound functions leaves a named free variable unchanged. -/
@[simp] theorem weakenFun_freeVar (name : VariableName) :
    (Variety.freeVar name).weakenFun = .freeVar name := by
  simp [Variety.weakenFun, Variety.weakenFunAt, Variety.rename]

/-- A complete abstraction block cannot capture a named free variable. -/
@[simp] theorem weakenVarBy_freeVar (name : VariableName) (count : Nat) :
    (Variety.freeVar name).weakenVarBy count = .freeVar name := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [weakenVarBy_succ, weakenVar_freeVar] using ih

/-- Takeuti §5.2.34 at height zero: the matching occurrence returns its replacement. -/
@[simp] theorem completeSubstituteVar_freeVar_base
    (target : VariableName) (replacement : Variety)
    (htarget : target.profile = .zero) :
    Variety.completeSubstituteVar? target replacement (.freeVar target) =
      some replacement := by
  simp [Variety.completeSubstituteVar?, htarget]

end Variety

mutual

/-- Takeuti §5.2.33 at height zero for a typed variety of any profile. -/
theorem Variety.HasType.completeSubstituteVar_self_base
    {ctx : TypingContext} {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile)
    (target : VariableName) (htarget : target.profile = .zero) :
    Variety.completeSubstituteVar? target (.freeVar target) variety = some variety := by
  cases h with
  | freeVar _ name _ =>
      by_cases hname : name = target <;>
        simp [Variety.completeSubstituteVar?, hname, htarget]
  | specialVar _ name _ => rfl
  | boundVar _ index _ => rfl
  | freeFunApp _ name args hargs =>
      simp [Variety.completeSubstituteVar?,
        hargs.completeSubstituteVar_self_base target htarget]
  | specialFunApp _ name args hargs =>
      simp [Variety.completeSubstituteVar?,
        hargs.completeSubstituteVar_self_base target htarget]
  | boundFunApp _ index functionProfile args _ hargs =>
      simp [Variety.completeSubstituteVar?,
        hargs.completeSubstituteVar_self_base target htarget]
  | abstract _ head tail body hbody =>
      simp [Variety.completeSubstituteVar?,
        hbody.completeSubstituteVar_self_base target htarget]
termination_by sizeOf variety

/-- Takeuti §5.2.33 at height zero for a well-formed formula. -/
theorem Formula.WellFormed.completeSubstituteVar_self_base
    {ctx : TypingContext} {formula : Formula}
    (h : Formula.WellFormed ctx formula)
    (target : VariableName) (htarget : target.profile = .zero) :
    Formula.completeSubstituteVar? target (.freeVar target) formula = some formula := by
  cases h with
  | atomFree _ name args hnonzero hargs =>
      have hname : name ≠ target := by
        intro heq
        subst name
        exact hnonzero htarget
      simp [Formula.completeSubstituteVar?, hname,
        hargs.completeSubstituteVar_self_base target htarget]
  | atomSpecial _ name args _ hargs =>
      simp [Formula.completeSubstituteVar?,
        hargs.completeSubstituteVar_self_base target htarget]
  | atomBound _ index profile args _ _ hargs =>
      simp [Formula.completeSubstituteVar?,
        hargs.completeSubstituteVar_self_base target htarget]
  | neg _ body hbody =>
      simp [Formula.completeSubstituteVar?,
        hbody.completeSubstituteVar_self_base target htarget]
  | conj _ left right hleft hright =>
      simp [Formula.completeSubstituteVar?,
        hleft.completeSubstituteVar_self_base target htarget,
        hright.completeSubstituteVar_self_base target htarget]
  | disj _ left right hleft hright =>
      simp [Formula.completeSubstituteVar?,
        hleft.completeSubstituteVar_self_base target htarget,
        hright.completeSubstituteVar_self_base target htarget]
  | allVar _ profile body hbody =>
      simp [Formula.completeSubstituteVar?,
        hbody.completeSubstituteVar_self_base target htarget]
  | existsVar _ profile body hbody =>
      simp [Formula.completeSubstituteVar?,
        hbody.completeSubstituteVar_self_base target htarget]
  | allFun _ profile body hbody =>
      simp [Formula.completeSubstituteVar?,
        hbody.completeSubstituteVar_self_base target htarget]
  | existsFun _ profile body hbody =>
      simp [Formula.completeSubstituteVar?,
        hbody.completeSubstituteVar_self_base target htarget]
termination_by sizeOf formula

/-- Height-zero identity acts pointwise on typed argument lists. -/
theorem VarietiesHaveTypes.completeSubstituteVar_self_base
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes ctx args profiles)
    (target : VariableName) (htarget : target.profile = .zero) :
    completeSubstituteVarArgs? target (.freeVar target) args = some args := by
  cases h with
  | nil _ => rfl
  | cons _ head headType tail tailTypes hhead htail =>
      simp [completeSubstituteVarArgs?,
        hhead.completeSubstituteVar_self_base target htarget,
        htail.completeSubstituteVar_self_base target htarget]
termination_by sizeOf args

end

/-- Height-zero identity also crosses a functional's abstraction block. -/
theorem Functional.HasType.completeSubstituteVar_self_base
    {ctx : TypingContext} {functional : Functional} {profile : TypeProfile}
    (h : Functional.HasType ctx functional profile)
    (target : VariableName) (htarget : target.profile = .zero) :
    Functional.completeSubstituteVar? target (.freeVar target) functional =
      some functional := by
  cases h with
  | abstract head tail body hbody =>
      simp [Functional.completeSubstituteVar?,
        hbody.completeSubstituteVar_self_base target htarget]

/-- The term-facing API inherits the height-zero identity theorem. -/
theorem Variety.IsTerm.completeSubstituteVar_self_base
    {ctx : TypingContext} {variety : Variety}
    (h : Variety.IsTerm ctx variety)
    (target : VariableName) (htarget : target.profile = .zero) :
    Variety.completeSubstituteVar? target (.freeVar target) variety = some variety :=
  Variety.HasType.completeSubstituteVar_self_base h target htarget

/-- Existential well-typing suffices; the caller need not choose a result profile. -/
theorem Variety.WellTyped.completeSubstituteVar_self_base
    {ctx : TypingContext} {variety : Variety}
    (h : Variety.WellTyped ctx variety)
    (target : VariableName) (htarget : target.profile = .zero) :
    Variety.completeSubstituteVar? target (.freeVar target) variety = some variety := by
  obtain ⟨_, htyped⟩ := h
  exact htyped.completeSubstituteVar_self_base target htarget

/-- The functional formation API inherits the same identity theorem. -/
theorem Functional.WellFormed.completeSubstituteVar_self_base
    {ctx : TypingContext} {functional : Functional}
    (h : Functional.WellFormed ctx functional)
    (target : VariableName) (htarget : target.profile = .zero) :
    Functional.completeSubstituteVar? target (.freeVar target) functional = some functional :=
  Functional.HasType.completeSubstituteVar_self_base h target htarget

/-- Raw base atomic heads are not formed formulas, so identity must not accept them. -/
theorem Formula.completeSubstituteVar_self_base_malformed
    (target : VariableName) (htarget : target.profile = .zero) :
    Formula.completeSubstituteVar? target (.freeVar target) (.atomFree target []) =
      none := by
  simp [Formula.completeSubstituteVar?, completeSubstituteVarArgs?, htarget]

/-- Regression: identity crosses both binder families and an abstraction to a real occurrence. -/
theorem Formula.completeSubstituteVar_self_base_mixedBinders
    (functionProfile : FunctionProfile) :
    let target : VariableName := ⟨.zero, 0⟩
    let formula : Formula := .allFun functionProfile
      (.existsVar .zero (.atomSpecial ⟨.higher 1 [], 1⟩
        [.abstract 0 [] (.atomSpecial ⟨.higher 0 [], 2⟩ [.freeVar target])]))
    Formula.completeSubstituteVar? target (.freeVar target) formula = some formula := by
  dsimp only
  apply Formula.WellFormed.completeSubstituteVar_self_base
    (ctx := .empty) (target := ⟨.zero, 0⟩) (htarget := rfl)
  apply Formula.WellFormed.allFun
  apply Formula.WellFormed.existsVar
  apply Formula.WellFormed.atomSpecial
  · decide
  · apply VarietiesHaveTypes.cons
    · apply Variety.HasType.abstract
      apply Formula.WellFormed.atomSpecial
      · decide
      · exact .cons _ _ _ _ _ (.freeVar _ _ rfl) (.nil _)
    · exact .nil _

/-- Higher-type free-variable nodes need identity abstractions instead of this base law. -/
theorem Variety.completeSubstituteVar_self_higher_freeVar_malformed
    (target : VariableName) (htarget : target.profile ≠ .zero) :
    Variety.completeSubstituteVar? target (.freeVar target) (.freeVar target) =
      none := by
  simp [Variety.completeSubstituteVar?, htarget]

end TakeutiGLC
