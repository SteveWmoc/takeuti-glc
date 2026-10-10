import Mathlib.Tactic
import TakeutiGLC.Syntax.TypedWeakening
import TakeutiGLC.Syntax.HereditaryInstantiation

/-!
# Typing for hereditary variable-block instantiation

This file develops the formation-preservation metatheory for the hereditary
instantiation kernel used by arbitrary-height complete substitution.
-/

namespace TakeutiGLC

/-- The target context after a removable variable block, under local prefixes. -/
def instantiationTargetContext
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile) : TypingContext :=
  { variableTypes := variablePrefix ++ ctx.variableTypes
    functionProfiles := functionPrefix ++ ctx.functionProfiles }

/-- The source context before a removable variable block is instantiated. -/
def instantiationSourceContext
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) : TypingContext :=
  { variableTypes :=
      variablePrefix ++ levels.map TypeProfile.monotype ++ ctx.variableTypes
    functionProfiles := functionPrefix ++ ctx.functionProfiles }

namespace TypingContext

theorem instantiation_variableAt_before
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) {index : Nat}
    (hindex : index < variablePrefix.length) :
    (instantiationSourceContext ctx variablePrefix functionPrefix levels).variableAt index =
      (instantiationTargetContext ctx variablePrefix functionPrefix).variableAt index := by
  simp [instantiationSourceContext, instantiationTargetContext, variableAt, hindex]

theorem instantiation_variableAt_block
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) {relative level : Nat}
    (hlevel : levels[relative]? = some level) :
    (instantiationSourceContext ctx variablePrefix functionPrefix levels).variableAt
      (variablePrefix.length + relative) =
        some (TypeProfile.monotype level) := by
  simp [instantiationSourceContext, variableAt, hlevel]

theorem instantiation_variableAt_after
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) (index : Nat) :
    (instantiationSourceContext ctx variablePrefix functionPrefix levels).variableAt
      (variablePrefix.length + levels.length + index) =
    (instantiationTargetContext ctx variablePrefix functionPrefix).variableAt
      (variablePrefix.length + index) := by
  simp [instantiationSourceContext, instantiationTargetContext, variableAt]

theorem instantiation_functionAt
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) (index : Nat) :
    (instantiationSourceContext ctx variablePrefix functionPrefix levels).functionAt index =
    (instantiationTargetContext ctx variablePrefix functionPrefix).functionAt index := rfl

end TypingContext

namespace VarietiesHaveTypes

/-- Pointwise typing forces the argument and profile lists to have equal length. -/
theorem length_eq
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes ctx args profiles) :
    args.length = profiles.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simp [ih]

/-- Recover the typed argument at a known profile-list position. -/
theorem get?_hasType
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes ctx args profiles)
    {index : Nat} {profile : TypeProfile}
    (hprofile : profiles[index]? = some profile) :
    ∃ argument,
      args[index]? = some argument ∧ Variety.HasType ctx argument profile := by
  induction h generalizing index profile with
  | nil =>
      simp at hprofile
  | cons ctx head headType tail tailTypes hhead htail ih =>
      cases index with
      | zero =>
          simp at hprofile
          subst profile
          exact ⟨head, by simp, hhead⟩
      | succ index =>
          simp at hprofile
          obtain ⟨argument, hargument, htype⟩ := ih hprofile
          exact ⟨argument, by simpa using hargument, htype⟩

end VarietiesHaveTypes

/--
Typing-preservation contract for the lower-height callback used by one
hereditary-instantiation step.
-/
def LowerVarBlockInstantiation.PreservesTyping
    (lower : LowerVarBlockInstantiation) : Prop :=
  ∀ {ctx : TypingContext} {levels : List Nat} {replacements : List Variety}
    {body result : Formula},
    Formula.WellFormed
      { ctx with
        variableTypes := levels.map TypeProfile.monotype ++ ctx.variableTypes }
      body →
    VarietiesHaveTypes ctx replacements (levels.map TypeProfile.monotype) →
    lower levels replacements body = some result →
    Formula.WellFormed ctx result

end TakeutiGLC
