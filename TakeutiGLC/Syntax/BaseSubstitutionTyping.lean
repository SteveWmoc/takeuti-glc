import TakeutiGLC.Syntax.SubstitutionTyping

/-!
# Totality and formation preservation for base substitution

For a type-`(0)` target and a well-typed source, the unified partial driver
agrees with the total `completeSubstituteBaseVar` transformation. This proves
success without a typing assumption on the replacement. If the replacement
is a term in the source context, formation preservation follows with no
successful-run hypothesis.

The compatibility theorem needs source formation: malformed raw syntax may
use a base variable as an atomic head, which the unified driver rejects.
Higher-type totality and the remaining identity/commutation laws are separate.
-/

namespace TakeutiGLC

mutual

/-- On a typed variety, the base case of the unified driver is the total kernel. -/
theorem Variety.HasType.completeSubstituteVar_eq_base
    {ctx : TypingContext} {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile)
    (target : VariableName) (replacement : Variety)
    (htarget : target.profile = .zero) :
    Variety.completeSubstituteVar? target replacement variety =
      some (Variety.completeSubstituteBaseVar target replacement variety) := by
  cases h with
  | freeVar _ name _ =>
      by_cases hname : name = target <;>
        simp [Variety.completeSubstituteVar?, hname, htarget]
  | specialVar _ name _ =>
      simp only [Variety.completeSubstituteVar?, Variety.completeSubstituteBaseVar]
  | boundVar _ index _ =>
      simp only [Variety.completeSubstituteVar?, Variety.completeSubstituteBaseVar]
  | freeFunApp _ name args hargs =>
      simp [Variety.completeSubstituteVar?, Variety.completeSubstituteBaseVar,
        hargs.completeSubstituteVar_eq_base target replacement htarget]
  | specialFunApp _ name args hargs =>
      simp [Variety.completeSubstituteVar?, Variety.completeSubstituteBaseVar,
        hargs.completeSubstituteVar_eq_base target replacement htarget]
  | boundFunApp _ index functionProfile args _ hargs =>
      simp [Variety.completeSubstituteVar?, Variety.completeSubstituteBaseVar,
        hargs.completeSubstituteVar_eq_base target replacement htarget]
  | abstract _ head tail body hbody =>
      simp [Variety.completeSubstituteVar?, Variety.completeSubstituteBaseVar,
        hbody.completeSubstituteVar_eq_base target
          (replacement.weakenVarBy (blockSize tail)) htarget]
termination_by sizeOf variety

/-- On a formed formula, base substitution always succeeds with the total result. -/
theorem Formula.WellFormed.completeSubstituteVar_eq_base
    {ctx : TypingContext} {formula : Formula}
    (h : Formula.WellFormed ctx formula)
    (target : VariableName) (replacement : Variety)
    (htarget : target.profile = .zero) :
    Formula.completeSubstituteVar? target replacement formula =
      some (Formula.completeSubstituteBaseVar target replacement formula) := by
  cases h with
  | atomFree _ name args hnonzero hargs =>
      have hname : name ≠ target := by
        intro heq
        subst name
        exact hnonzero htarget
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteBaseVar, hname,
        hargs.completeSubstituteVar_eq_base target replacement htarget]
  | atomSpecial _ name args _ hargs =>
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteBaseVar,
        hargs.completeSubstituteVar_eq_base target replacement htarget]
  | atomBound _ index profile args _ _ hargs =>
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteBaseVar,
        hargs.completeSubstituteVar_eq_base target replacement htarget]
  | neg _ body hbody =>
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteBaseVar,
        hbody.completeSubstituteVar_eq_base target replacement htarget]
  | conj _ left right hleft hright =>
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteBaseVar,
        hleft.completeSubstituteVar_eq_base target replacement htarget,
        hright.completeSubstituteVar_eq_base target replacement htarget]
  | disj _ left right hleft hright =>
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteBaseVar,
        hleft.completeSubstituteVar_eq_base target replacement htarget,
        hright.completeSubstituteVar_eq_base target replacement htarget]
  | allVar _ profile body hbody =>
      simp [Formula.completeSubstituteVar?,
        hbody.completeSubstituteVar_eq_base target replacement.weakenVar htarget]
  | existsVar _ profile body hbody =>
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteBaseVar,
        hbody.completeSubstituteVar_eq_base target replacement.weakenVar htarget]
  | allFun _ profile body hbody =>
      simp [Formula.completeSubstituteVar?,
        hbody.completeSubstituteVar_eq_base target replacement.weakenFun htarget]
  | existsFun _ profile body hbody =>
      simp [Formula.completeSubstituteVar?, Formula.completeSubstituteBaseVar,
        hbody.completeSubstituteVar_eq_base target replacement.weakenFun htarget]
termination_by sizeOf formula

/-- The argument-list driver agrees with mapping the total base kernel. -/
theorem VarietiesHaveTypes.completeSubstituteVar_eq_base
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes ctx args profiles)
    (target : VariableName) (replacement : Variety)
    (htarget : target.profile = .zero) :
    completeSubstituteVarArgs? target replacement args =
      some (args.map (Variety.completeSubstituteBaseVar target replacement)) := by
  cases h with
  | nil _ => rfl
  | cons _ head headType tail tailTypes hhead htail =>
      simp [completeSubstituteVarArgs?,
        hhead.completeSubstituteVar_eq_base target replacement htarget,
        htail.completeSubstituteVar_eq_base target replacement htarget]
termination_by sizeOf args

end

/-- The functional driver agrees with the total kernel through its binder block. -/
theorem Functional.HasType.completeSubstituteVar_eq_base
    {ctx : TypingContext} {functional : Functional} {profile : TypeProfile}
    (h : Functional.HasType ctx functional profile)
    (target : VariableName) (replacement : Variety)
    (htarget : target.profile = .zero) :
    Functional.completeSubstituteVar? target replacement functional =
      some (Functional.completeSubstituteBaseVar target replacement functional) := by
  cases h with
  | abstract head tail body hbody =>
      simp [Functional.completeSubstituteVar?, Functional.completeSubstituteBaseVar,
        hbody.completeSubstituteVar_eq_base target
          (replacement.weakenVarBy (blockSize tail)) htarget]

/-- Total base substitution preserves any variety profile when replacing by a term. -/
theorem Variety.HasType.completeSubstituteBaseVar
    {ctx : TypingContext} {variety replacement : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    Variety.HasType ctx
      (Variety.completeSubstituteBaseVar target replacement variety) profile := by
  apply Variety.HasType.completeSubstituteVar (target := target) (replacement := replacement)
    (by simpa [Variety.IsTerm, htarget] using hreplacement) h
  exact h.completeSubstituteVar_eq_base target replacement htarget

/-- Total base substitution preserves formula formation without a run hypothesis. -/
theorem Formula.WellFormed.completeSubstituteBaseVar
    {ctx : TypingContext} {formula : Formula} {replacement : Variety}
    (h : Formula.WellFormed ctx formula)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    Formula.WellFormed ctx
      (Formula.completeSubstituteBaseVar target replacement formula) := by
  apply Formula.WellFormed.completeSubstituteVar (target := target) (replacement := replacement)
    (by simpa [Variety.IsTerm, htarget] using hreplacement) h
  exact h.completeSubstituteVar_eq_base target replacement htarget

/-- Mapping total base substitution preserves all argument profiles. -/
theorem VarietiesHaveTypes.completeSubstituteBaseVar
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    {replacement : Variety}
    (h : VarietiesHaveTypes ctx args profiles)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    VarietiesHaveTypes ctx
      (args.map (Variety.completeSubstituteBaseVar target replacement)) profiles := by
  apply VarietiesHaveTypes.completeSubstituteVar (target := target) (replacement := replacement)
    (by simpa [Variety.IsTerm, htarget] using hreplacement) h
  exact h.completeSubstituteVar_eq_base target replacement htarget

/-- Total base substitution preserves a functional's profile. -/
theorem Functional.HasType.completeSubstituteBaseVar
    {ctx : TypingContext} {functional : Functional} {profile : TypeProfile}
    {replacement : Variety}
    (h : Functional.HasType ctx functional profile)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    Functional.HasType ctx
      (Functional.completeSubstituteBaseVar target replacement functional) profile := by
  apply Functional.HasType.completeSubstituteVar (target := target) (replacement := replacement)
    (by simpa [Variety.IsTerm, htarget] using hreplacement) h
  exact h.completeSubstituteVar_eq_base target replacement htarget

/-- The term interface needs no successful-run hypothesis for total base substitution. -/
theorem Variety.IsTerm.completeSubstituteBaseVar
    {ctx : TypingContext} {term replacement : Variety}
    (h : Variety.IsTerm ctx term)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    Variety.IsTerm ctx (Variety.completeSubstituteBaseVar target replacement term) :=
  Variety.HasType.completeSubstituteBaseVar h target htarget hreplacement

/-- Total base substitution also preserves existential well-typing. -/
theorem Variety.WellTyped.completeSubstituteBaseVar
    {ctx : TypingContext} {variety replacement : Variety}
    (h : Variety.WellTyped ctx variety)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    Variety.WellTyped ctx
      (Variety.completeSubstituteBaseVar target replacement variety) := by
  obtain ⟨profile, htype⟩ := h
  exact ⟨profile, htype.completeSubstituteBaseVar target htarget hreplacement⟩

/-- Total base substitution preserves the functional formation interface. -/
theorem Functional.WellFormed.completeSubstituteBaseVar
    {ctx : TypingContext} {functional : Functional} {replacement : Variety}
    (h : Functional.WellFormed ctx functional)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    Functional.WellFormed ctx
      (Functional.completeSubstituteBaseVar target replacement functional) := by
  have htype := Functional.HasType.completeSubstituteBaseVar h target htarget hreplacement
  cases functional with
  | abstract head tail body =>
      simpa [Functional.WellFormed, Functional.completeSubstituteBaseVar,
        Functional.profile] using htype

/-- The partial driver has a successful, typed result for every base substitution. -/
theorem Variety.HasType.completeSubstituteVar_base_total
    {ctx : TypingContext} {variety replacement : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    ∃ result, Variety.completeSubstituteVar? target replacement variety = some result ∧
      Variety.HasType ctx result profile :=
  ⟨_, h.completeSubstituteVar_eq_base target replacement htarget,
    h.completeSubstituteBaseVar target htarget hreplacement⟩

/-- A well-formed source and a term replacement always produce a well-formed formula. -/
theorem Formula.WellFormed.completeSubstituteVar_base_total
    {ctx : TypingContext} {formula : Formula} {replacement : Variety}
    (h : Formula.WellFormed ctx formula)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    ∃ result, Formula.completeSubstituteVar? target replacement formula = some result ∧
      Formula.WellFormed ctx result :=
  ⟨_, h.completeSubstituteVar_eq_base target replacement htarget,
    h.completeSubstituteBaseVar target htarget hreplacement⟩

/-- The same successful-result guarantee holds for a typed argument list. -/
theorem VarietiesHaveTypes.completeSubstituteVar_base_total
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    {replacement : Variety}
    (h : VarietiesHaveTypes ctx args profiles)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    ∃ results, completeSubstituteVarArgs? target replacement args = some results ∧
      VarietiesHaveTypes ctx results profiles :=
  ⟨_, h.completeSubstituteVar_eq_base target replacement htarget,
    h.completeSubstituteBaseVar target htarget hreplacement⟩

/-- Base substitution also always succeeds with a typed functional result. -/
theorem Functional.HasType.completeSubstituteVar_base_total
    {ctx : TypingContext} {functional : Functional} {profile : TypeProfile}
    {replacement : Variety}
    (h : Functional.HasType ctx functional profile)
    (target : VariableName) (htarget : target.profile = .zero)
    (hreplacement : Variety.IsTerm ctx replacement) :
    ∃ result, Functional.completeSubstituteVar? target replacement functional = some result ∧
      Functional.HasType ctx result profile :=
  ⟨_, h.completeSubstituteVar_eq_base target replacement htarget,
    h.completeSubstituteBaseVar target htarget hreplacement⟩

/--
Regression: a replacement referring to both outer bound namespaces crosses
variable/function quantifiers and a full abstraction block without capture.
The resulting variable index is `2` and the function index is `1`.
-/
theorem Formula.completeSubstituteVar_base_boundReplacement :
    let ctx : TypingContext := ⟨[.zero], [⟨0, []⟩]⟩
    let target : VariableName := ⟨.zero, 0⟩
    let replacement : Variety := .boundFunApp 0 [.boundVar 0]
    let source : Formula := .allVar .zero (.allFun ⟨0, []⟩
      (.atomSpecial ⟨.higher 1 [], 1⟩
        [.abstract 0 [] (.atomSpecial ⟨.higher 0 [], 2⟩ [.freeVar target])]))
    let result : Formula := .allVar .zero (.allFun ⟨0, []⟩
      (.atomSpecial ⟨.higher 1 [], 1⟩
        [.abstract 0 [] (.atomSpecial ⟨.higher 0 [], 2⟩
          [.boundFunApp 1 [.boundVar 2]])]))
    Formula.completeSubstituteVar? target replacement source = some result ∧
      Formula.WellFormed ctx result := by
  dsimp only
  have hsource : Formula.WellFormed ⟨[.zero], [⟨0, []⟩]⟩
      (.allVar .zero (.allFun ⟨0, []⟩ (.atomSpecial ⟨.higher 1 [], 1⟩
        [.abstract 0 [] (.atomSpecial ⟨.higher 0 [], 2⟩
          [.freeVar ⟨.zero, 0⟩])]))) := by
    apply Formula.WellFormed.allVar
    apply Formula.WellFormed.allFun
    apply Formula.WellFormed.atomSpecial
    · decide
    · apply VarietiesHaveTypes.cons
      · apply Variety.HasType.abstract
        apply Formula.WellFormed.atomSpecial
        · decide
        · exact .cons _ _ _ _ _ (.freeVar _ _ rfl) (.nil _)
      · exact .nil _
  have hreplacement : Variety.IsTerm ⟨[.zero], [⟨0, []⟩]⟩
      (.boundFunApp 0 [.boundVar 0]) :=
    .boundFunApp _ 0 ⟨0, []⟩ _ rfl
      (.cons _ _ _ _ _ (.boundVar _ _ rfl) (.nil _))
  have hrun := hsource.completeSubstituteVar_eq_base
    ⟨.zero, 0⟩ (.boundFunApp 0 [.boundVar 0]) rfl
  have hresult := hsource.completeSubstituteBaseVar ⟨.zero, 0⟩ rfl hreplacement
  simpa [Formula.completeSubstituteBaseVar, Variety.completeSubstituteBaseVar,
    Variety.weakenVarBy, Variety.weakenVar, Variety.weakenFun,
    Variety.weakenVarAt, Variety.weakenFunAt, Variety.rename,
    Renaming.weakenVarAt, Renaming.weakenFunAt, insertIndex, blockSize]
    using And.intro hrun hresult

end TakeutiGLC
