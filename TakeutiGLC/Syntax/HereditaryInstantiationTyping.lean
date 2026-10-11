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

namespace List

theorem length_le_of_getElem?_eq_none
    {α : Type} {items : List α} {index : Nat}
    (h : items[index]? = none) :
    items.length ≤ index := by
  by_contra hnot
  have hlt : index < items.length := Nat.lt_of_not_ge hnot
  have hsome : items[index]? = some items[index] := by
    simp [hlt]
  rw [h] at hsome
  simp at hsome

theorem lt_length_of_getElem?_eq_some
    {α : Type} {items : List α} {index : Nat} {item : α}
    (h : items[index]? = some item) :
    index < items.length := by
  by_contra hnot
  have hnone : items[index]? = none := by
    simp [Nat.le_of_not_gt hnot]
  rw [hnone] at h
  simp at h

theorem getElem?_append_left_of_lt
    {α : Type} (left right : List α) {index : Nat}
    (hindex : index < left.length) :
    (left ++ right)[index]? = left[index]? := by
  induction left generalizing index with
  | nil =>
      simp at hindex
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simp at hindex
          simpa using ih (index := index) hindex

theorem getElem?_append_right
    {α : Type} (left right : List α) (index : Nat) :
    (left ++ right)[left.length + index]? = right[index]? := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      simpa [Nat.succ_add] using ih

theorem getElem?_map
    {α β : Type} (f : α → β) (items : List α) (index : Nat) :
    (items.map f)[index]? = (items[index]?).map f := by
  induction items generalizing index with
  | nil => simp
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

end List
namespace TypingContext

theorem instantiation_variableAt_before
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) {index : Nat}
    (hindex : index < variablePrefix.length) :
    (instantiationSourceContext ctx variablePrefix functionPrefix levels).variableAt index =
      (instantiationTargetContext ctx variablePrefix functionPrefix).variableAt index := by
  dsimp [TypingContext.variableAt, instantiationSourceContext,
    instantiationTargetContext]
  rw [List.append_assoc]
  calc
    (variablePrefix ++
        (levels.map TypeProfile.monotype ++ ctx.variableTypes))[index]? =
        variablePrefix[index]? :=
      List.getElem?_append_left_of_lt _ _ hindex
    _ = (variablePrefix ++ ctx.variableTypes)[index]? := by
      symm
      exact List.getElem?_append_left_of_lt _ _ hindex

theorem instantiation_variableAt_block
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) {relative level : Nat}
    (hlevel : levels[relative]? = some level) :
    (instantiationSourceContext ctx variablePrefix functionPrefix levels).variableAt
      (variablePrefix.length + relative) =
        some (TypeProfile.monotype level) := by
  dsimp [TypingContext.variableAt, instantiationSourceContext]
  rw [List.append_assoc]
  have hrelative : relative < levels.length :=
    List.lt_length_of_getElem?_eq_some hlevel
  calc
    (variablePrefix ++
        (levels.map TypeProfile.monotype ++ ctx.variableTypes))[
          variablePrefix.length + relative]? =
        (levels.map TypeProfile.monotype ++ ctx.variableTypes)[relative]? :=
      List.getElem?_append_right _ _ relative
    _ = (levels.map TypeProfile.monotype)[relative]? :=
      List.getElem?_append_left_of_lt _ _ (by
        simpa only [List.length_map] using hrelative)
    _ = (levels[relative]?).map TypeProfile.monotype :=
      List.getElem?_map TypeProfile.monotype levels relative
    _ = some (TypeProfile.monotype level) := by rw [hlevel]; rfl

theorem instantiation_variableAt_after
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) (index : Nat) :
    (instantiationSourceContext ctx variablePrefix functionPrefix levels).variableAt
      (variablePrefix.length + levels.length + index) =
    (instantiationTargetContext ctx variablePrefix functionPrefix).variableAt
      (variablePrefix.length + index) := by
  dsimp [TypingContext.variableAt, instantiationSourceContext,
    instantiationTargetContext]
  rw [List.append_assoc]
  calc
    (variablePrefix ++
        (levels.map TypeProfile.monotype ++ ctx.variableTypes))[
          variablePrefix.length + levels.length + index]? =
        (levels.map TypeProfile.monotype ++ ctx.variableTypes)[levels.length + index]? := by
      simpa [Nat.add_assoc] using
        (List.getElem?_append_right variablePrefix
          (levels.map TypeProfile.monotype ++ ctx.variableTypes)
          (levels.length + index))
    _ = ctx.variableTypes[index]? := by
      simpa using
        (List.getElem?_append_right (levels.map TypeProfile.monotype)
          ctx.variableTypes index)
    _ = (variablePrefix ++ ctx.variableTypes)[variablePrefix.length + index]? := by
      symm
      exact List.getElem?_append_right variablePrefix ctx.variableTypes index

theorem instantiation_functionAt
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) (index : Nat) :
    (instantiationSourceContext ctx variablePrefix functionPrefix levels).functionAt index =
    (instantiationTargetContext ctx variablePrefix functionPrefix).functionAt index := rfl

theorem instantiation_variableAt_after_of_none
    (ctx : TypingContext)
    (variablePrefix : List TypeProfile)
    (functionPrefix : List FunctionProfile)
    (levels : List Nat) {index : Nat}
    (hprefix : variablePrefix.length ≤ index)
    (hnone : levels[index - variablePrefix.length]? = none) :
    (instantiationTargetContext ctx variablePrefix functionPrefix).variableAt
        (index - levels.length) =
      (instantiationSourceContext ctx variablePrefix functionPrefix levels).variableAt index := by
  have hlevels : levels.length ≤ index - variablePrefix.length :=
    List.length_le_of_getElem?_eq_none hnone
  let outer := index - variablePrefix.length - levels.length
  have hindex :
      index = variablePrefix.length + levels.length + outer := by
    dsimp [outer]
    omega
  have htarget :
      index - levels.length = variablePrefix.length + outer := by
    dsimp [outer]
    omega
  rw [htarget, hindex]
  exact
    (instantiation_variableAt_after
      ctx variablePrefix functionPrefix levels outer).symm

end TypingContext

namespace VarietiesHaveTypes

/-- Recover the typed argument at a known profile-list position. -/
theorem get?_hasType
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes ctx args profiles)
    {index : Nat} {profile : TypeProfile}
    (hprofile : profiles[index]? = some profile) :
    ∃ argument,
      args[index]? = some argument ∧ Variety.HasType ctx argument profile := by
  cases h with
  | nil _ =>
      simp at hprofile
  | cons _ head headType tail tailTypes hhead htail =>
      cases index with
      | zero =>
          simp at hprofile
          subst profile
          exact ⟨head, by simp, hhead⟩
      | succ index =>
          simp at hprofile
          obtain ⟨argument, hargument, htype⟩ :=
            VarietiesHaveTypes.get?_hasType htail hprofile
          exact ⟨argument, by simpa using hargument, htype⟩
termination_by args.length

/-- A singleton expected profile forces a singleton typed argument list. -/
theorem singleton_inv
    {ctx : TypingContext} {args : List Variety} {profile : TypeProfile}
    (h : VarietiesHaveTypes ctx args [profile]) :
    ∃ argument, args = [argument] ∧ Variety.HasType ctx argument profile := by
  cases h with
  | cons _ head headType tail tailTypes hhead htail =>
      cases htail with
      | nil _ =>
          exact ⟨head, rfl, hhead⟩

end VarietiesHaveTypes

namespace Variety.HasType

/--
The raw `liftIntoScope` operation preserves a variety's type when its numeric
depths are realized by concrete variable/function prefixes.
-/
theorem liftIntoPrefixes
    {ctx : TypingContext} {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile)
    (variablePrefix : List TypeProfile) (functionPrefix : List FunctionProfile) :
    Variety.HasType
      { variableTypes := variablePrefix ++ ctx.variableTypes
        functionProfiles := functionPrefix ++ ctx.functionProfiles }
      (variety.liftIntoScope variablePrefix.length functionPrefix.length) profile := by
  have hvar := h.weakenVarPrefix variablePrefix
  have hfun := hvar.weakenFunPrefix functionPrefix
  simpa [Variety.liftIntoScope] using hfun

/-- A variety of positive singleton type is necessarily a one-place abstraction. -/
theorem monotype_succ_inv
    {ctx : TypingContext} {variety : Variety} {level : Nat}
    (h : Variety.HasType ctx variety (TypeProfile.monotype (Nat.succ level))) :
    ∃ body,
      variety = .abstract level [] body ∧
      Formula.WellFormed (ctx.underBlock level []) body := by
  cases h with
  | abstract _ headLevel tailLevels body hbody =>
      exact ⟨body, rfl, hbody⟩

end Variety.HasType

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



mutual

/-- One hereditary-instantiation traversal preserves the type of a variety. -/
theorem Variety.HasType.instantiateVarBlockStep
    {lower : LowerVarBlockInstantiation}
    (hlower : LowerVarBlockInstantiation.PreservesTyping lower)
    {ctx : TypingContext}
    {variablePrefix : List TypeProfile}
    {functionPrefix : List FunctionProfile}
    {levels : List Nat} {replacements : List Variety}
    (hreplacements :
      VarietiesHaveTypes ctx replacements (levels.map TypeProfile.monotype))
    {variety result : Variety} {profile : TypeProfile}
    (h :
      Variety.HasType
        (instantiationSourceContext ctx variablePrefix functionPrefix levels)
        variety profile)
    (hrun :
      Variety.instantiateVarBlockStep? lower levels replacements
        variablePrefix.length functionPrefix.length variety = some result) :
    Variety.HasType
      (instantiationTargetContext ctx variablePrefix functionPrefix)
      result profile := by
  cases h with
  | freeVar _ name hprofile =>
      simp [Variety.instantiateVarBlockStep?] at hrun
      subst result
      exact .freeVar _ name hprofile
  | specialVar _ name hprofile =>
      simp [Variety.instantiateVarBlockStep?] at hrun
      subst result
      exact .specialVar _ name hprofile
  | boundVar _ index hlookup =>
      by_cases hcut : index < variablePrefix.length
      · simp [Variety.instantiateVarBlockStep?, hcut] at hrun
        subst result
        apply Variety.HasType.boundVar
        rw [← TypingContext.instantiation_variableAt_before
          ctx variablePrefix functionPrefix levels hcut]
        exact hlookup
      · have hprefix : variablePrefix.length ≤ index := Nat.le_of_not_gt hcut
        cases hlevel : levels[index - variablePrefix.length]? with
        | none =>
            simp [Variety.instantiateVarBlockStep?, hcut, hlevel] at hrun
            subst result
            apply Variety.HasType.boundVar
            rw [TypingContext.instantiation_variableAt_after_of_none
              ctx variablePrefix functionPrefix levels hprefix hlevel]
            exact hlookup
        | some level =>
            cases level with
            | zero =>
                have hprofileAt :
                    (levels.map TypeProfile.monotype)[index - variablePrefix.length]? =
                      some .zero := by
                  simpa using congrArg (Option.map TypeProfile.monotype) hlevel
                obtain ⟨replacement, hreplacementAt, hreplacementType⟩ :=
                  hreplacements.get?_hasType hprofileAt
                simp [Variety.instantiateVarBlockStep?, hcut, hlevel,
                  hreplacementAt] at hrun
                subst result
                exact hreplacementType.liftIntoPrefixes variablePrefix functionPrefix
            | succ predecessor =>
                have hindex :
                    index = variablePrefix.length + (index - variablePrefix.length) := by
                  omega
                have hslot :=
                  TypingContext.instantiation_variableAt_block
                    ctx variablePrefix functionPrefix levels hlevel
                rw [← hindex] at hslot
                have hzero :
                    TypeProfile.monotype (Nat.succ predecessor) = .zero :=
                  Option.some.inj (hslot.symm.trans hlookup)
                simp at hzero
  | freeFunApp _ name args hargs =>
      cases hargsrun :
          instantiateVarBlockStepArgs? lower levels replacements
            variablePrefix.length functionPrefix.length args with
      | none =>
          simp [Variety.instantiateVarBlockStep?, hargsrun] at hrun
      | some args' =>
          simp [Variety.instantiateVarBlockStep?, hargsrun] at hrun
          subst result
          exact .freeFunApp _ name args'
            (VarietiesHaveTypes.instantiateVarBlockStep
              hlower hreplacements hargs hargsrun)
  | specialFunApp _ name args hargs =>
      cases hargsrun :
          instantiateVarBlockStepArgs? lower levels replacements
            variablePrefix.length functionPrefix.length args with
      | none =>
          simp [Variety.instantiateVarBlockStep?, hargsrun] at hrun
      | some args' =>
          simp [Variety.instantiateVarBlockStep?, hargsrun] at hrun
          subst result
          exact .specialFunApp _ name args'
            (VarietiesHaveTypes.instantiateVarBlockStep
              hlower hreplacements hargs hargsrun)
  | boundFunApp _ index functionProfile args hlookup hargs =>
      cases hargsrun :
          instantiateVarBlockStepArgs? lower levels replacements
            variablePrefix.length functionPrefix.length args with
      | none =>
          simp [Variety.instantiateVarBlockStep?, hargsrun] at hrun
      | some args' =>
          simp [Variety.instantiateVarBlockStep?, hargsrun] at hrun
          subst result
          have hlookup' :
              (instantiationTargetContext ctx variablePrefix functionPrefix).functionAt index =
                some functionProfile := by
            rw [← TypingContext.instantiation_functionAt
              ctx variablePrefix functionPrefix levels index]
            exact hlookup
          exact .boundFunApp _ index functionProfile args' hlookup'
            (VarietiesHaveTypes.instantiateVarBlockStep
              hlower hreplacements hargs hargsrun)
  | abstract _ headLevel tailLevels body hbody =>
      let added := abstractionBinderTypes headLevel tailLevels
      have hbody' :
          Formula.WellFormed
            (instantiationSourceContext ctx
              (added ++ variablePrefix) functionPrefix levels) body := by
        simpa [instantiationSourceContext, TypingContext.underBlock,
          added, List.append_assoc] using hbody
      cases hbodyrun :
          Formula.instantiateVarBlockStep? lower levels replacements
            (variablePrefix.length + blockSize tailLevels)
            functionPrefix.length body with
      | none =>
          simp [Variety.instantiateVarBlockStep?, hbodyrun] at hrun
      | some body' =>
          simp [Variety.instantiateVarBlockStep?, hbodyrun] at hrun
          subst result
          have hcutoff :
              (added ++ variablePrefix).length =
                variablePrefix.length + blockSize tailLevels := by
            simp [added, abstractionBinderTypes, blockSize]
            omega
          have hbodyrun' :
              Formula.instantiateVarBlockStep? lower levels replacements
                (added ++ variablePrefix).length functionPrefix.length body =
                  some body' := by
            rw [hcutoff]
            exact hbodyrun
          have htyped :=
            Formula.WellFormed.instantiateVarBlockStep
              hlower hreplacements hbody' hbodyrun'
          exact .abstract _ headLevel tailLevels body' (by
            simpa [instantiationTargetContext, TypingContext.underBlock,
              added, List.append_assoc] using htyped)

/-- One hereditary-instantiation traversal preserves well-formed formulas. -/
theorem Formula.WellFormed.instantiateVarBlockStep
    {lower : LowerVarBlockInstantiation}
    (hlower : LowerVarBlockInstantiation.PreservesTyping lower)
    {ctx : TypingContext}
    {variablePrefix : List TypeProfile}
    {functionPrefix : List FunctionProfile}
    {levels : List Nat} {replacements : List Variety}
    (hreplacements :
      VarietiesHaveTypes ctx replacements (levels.map TypeProfile.monotype))
    {formula result : Formula}
    (h :
      Formula.WellFormed
        (instantiationSourceContext ctx variablePrefix functionPrefix levels)
        formula)
    (hrun :
      Formula.instantiateVarBlockStep? lower levels replacements
        variablePrefix.length functionPrefix.length formula = some result) :
    Formula.WellFormed
      (instantiationTargetContext ctx variablePrefix functionPrefix) result := by
  cases h with
  | atomFree _ name args hnonzero hargs =>
      cases hargsrun :
          instantiateVarBlockStepArgs? lower levels replacements
            variablePrefix.length functionPrefix.length args with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hargsrun] at hrun
      | some args' =>
          simp [Formula.instantiateVarBlockStep?, hargsrun] at hrun
          subst result
          exact .atomFree _ name args' hnonzero
            (VarietiesHaveTypes.instantiateVarBlockStep
              hlower hreplacements hargs hargsrun)
  | atomSpecial _ name args hnonzero hargs =>
      cases hargsrun :
          instantiateVarBlockStepArgs? lower levels replacements
            variablePrefix.length functionPrefix.length args with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hargsrun] at hrun
      | some args' =>
          simp [Formula.instantiateVarBlockStep?, hargsrun] at hrun
          subst result
          exact .atomSpecial _ name args' hnonzero
            (VarietiesHaveTypes.instantiateVarBlockStep
              hlower hreplacements hargs hargsrun)
  | atomBound _ index profile args hlookup hnonzero hargs =>
      cases hargsrun :
          instantiateVarBlockStepArgs? lower levels replacements
            variablePrefix.length functionPrefix.length args with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hargsrun] at hrun
      | some args' =>
          have hargs' :=
            VarietiesHaveTypes.instantiateVarBlockStep
              hlower hreplacements hargs hargsrun
          by_cases hcut : index < variablePrefix.length
          · simp [Formula.instantiateVarBlockStep?, hargsrun, hcut] at hrun
            subst result
            have hlookup' :
                (instantiationTargetContext ctx variablePrefix functionPrefix).variableAt index =
                  some profile := by
              rw [← TypingContext.instantiation_variableAt_before
                ctx variablePrefix functionPrefix levels hcut]
              exact hlookup
            exact .atomBound _ index profile args' hlookup' hnonzero hargs'
          · have hprefix : variablePrefix.length ≤ index := Nat.le_of_not_gt hcut
            cases hlevel : levels[index - variablePrefix.length]? with
            | none =>
                simp [Formula.instantiateVarBlockStep?, hargsrun, hcut, hlevel] at hrun
                subst result
                have hlookup' :
                    (instantiationTargetContext ctx variablePrefix functionPrefix).variableAt
                        (index - levels.length) = some profile := by
                  rw [TypingContext.instantiation_variableAt_after_of_none
                    ctx variablePrefix functionPrefix levels hprefix hlevel]
                  exact hlookup
                exact .atomBound _ (index - levels.length) profile args'
                  hlookup' hnonzero hargs'
            | some level =>
                cases level with
                | zero =>
                    simp [Formula.instantiateVarBlockStep?, hargsrun, hcut, hlevel] at hrun
                | succ predecessor =>
                    have hindex :
                        index = variablePrefix.length +
                          (index - variablePrefix.length) := by
                      omega
                    have hslot :=
                      TypingContext.instantiation_variableAt_block
                        ctx variablePrefix functionPrefix levels hlevel
                    rw [← hindex] at hslot
                    have hprofileEq :
                        profile = TypeProfile.monotype (Nat.succ predecessor) :=
                      Option.some.inj (hlookup.symm.trans hslot)
                    subst profile
                    have hreplacementProfile :
                        (levels.map TypeProfile.monotype)[index - variablePrefix.length]? =
                          some (TypeProfile.monotype (Nat.succ predecessor)) := by
                      simpa using congrArg (Option.map TypeProfile.monotype) hlevel
                    obtain ⟨replacement, hreplacementAt, hreplacementType⟩ :=
                      hreplacements.get?_hasType hreplacementProfile
                    have hreplacementLift :=
                      hreplacementType.liftIntoPrefixes variablePrefix functionPrefix
                    obtain ⟨replacementBody, hreplacementShape, hreplacementBody⟩ :=
                      hreplacementLift.monotype_succ_inv
                    have hargsSingleton :
                        VarietiesHaveTypes
                          (instantiationTargetContext ctx variablePrefix functionPrefix)
                          args' [TypeProfile.monotype predecessor] := by
                      simpa using hargs'
                    obtain ⟨argument, hargsShape, hargument⟩ :=
                      hargsSingleton.singleton_inv
                    subst args'
                    have hrun' := hrun
                    simp [Formula.instantiateVarBlockStep?, hargsrun, hcut, hlevel,
                      hreplacementAt, hreplacementShape] at hrun'
                    have hlowerRun :
                        lower [predecessor] [argument] replacementBody = some result := by
                      simpa [abstractionProfile] using hrun'
                    have hbodyForLower :
                        Formula.WellFormed
                          { (instantiationTargetContext ctx variablePrefix functionPrefix) with
                            variableTypes :=
                              [TypeProfile.monotype predecessor] ++
                                (instantiationTargetContext ctx
                                  variablePrefix functionPrefix).variableTypes }
                          replacementBody := by
                      simpa [TypingContext.underBlock, abstractionBinderTypes,
                        instantiationTargetContext] using hreplacementBody
                    exact hlower
                      (ctx := instantiationTargetContext
                        ctx variablePrefix functionPrefix)
                      (levels := [predecessor])
                      (replacements := [argument])
                      (body := replacementBody)
                      (result := result)
                      hbodyForLower
                      (.cons _ argument (TypeProfile.monotype predecessor) [] []
                        hargument (.nil _))
                      hlowerRun
  | neg _ body hbody =>
      cases hbodyrun :
          Formula.instantiateVarBlockStep? lower levels replacements
            variablePrefix.length functionPrefix.length body with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
          subst result
          exact .neg _ body'
            (Formula.WellFormed.instantiateVarBlockStep
              hlower hreplacements hbody hbodyrun)
  | conj _ left right hleft hright =>
      cases hleftrun :
          Formula.instantiateVarBlockStep? lower levels replacements
            variablePrefix.length functionPrefix.length left with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hleftrun] at hrun
      | some left' =>
          cases hrightrun :
              Formula.instantiateVarBlockStep? lower levels replacements
                variablePrefix.length functionPrefix.length right with
          | none =>
              simp [Formula.instantiateVarBlockStep?, hleftrun, hrightrun] at hrun
          | some right' =>
              simp [Formula.instantiateVarBlockStep?, hleftrun, hrightrun] at hrun
              subst result
              exact .conj _ left' right'
                (Formula.WellFormed.instantiateVarBlockStep
                  hlower hreplacements hleft hleftrun)
                (Formula.WellFormed.instantiateVarBlockStep
                  hlower hreplacements hright hrightrun)
  | disj _ left right hleft hright =>
      cases hleftrun :
          Formula.instantiateVarBlockStep? lower levels replacements
            variablePrefix.length functionPrefix.length left with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hleftrun] at hrun
      | some left' =>
          cases hrightrun :
              Formula.instantiateVarBlockStep? lower levels replacements
                variablePrefix.length functionPrefix.length right with
          | none =>
              simp [Formula.instantiateVarBlockStep?, hleftrun, hrightrun] at hrun
          | some right' =>
              simp [Formula.instantiateVarBlockStep?, hleftrun, hrightrun] at hrun
              subst result
              exact .disj _ left' right'
                (Formula.WellFormed.instantiateVarBlockStep
                  hlower hreplacements hleft hleftrun)
                (Formula.WellFormed.instantiateVarBlockStep
                  hlower hreplacements hright hrightrun)
  | allVar _ binderProfile body hbody =>
      let added : List TypeProfile := [binderProfile]
      have hbody' :
          Formula.WellFormed
            (instantiationSourceContext ctx
              (added ++ variablePrefix) functionPrefix levels) body := by
        simpa [instantiationSourceContext, TypingContext.underVar,
          added, List.append_assoc] using hbody
      cases hbodyrun :
          Formula.instantiateVarBlockStep? lower levels replacements
            (variablePrefix.length + 1) functionPrefix.length body with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
          subst result
          have hbodyrun' :
              Formula.instantiateVarBlockStep? lower levels replacements
                (added ++ variablePrefix).length functionPrefix.length body =
                  some body' := by
            simpa [added, Nat.add_comm] using hbodyrun
          have htyped :=
            Formula.WellFormed.instantiateVarBlockStep
              hlower hreplacements hbody' hbodyrun'
          exact .allVar _ binderProfile body' (by
            simpa [instantiationTargetContext, TypingContext.underVar,
              added, List.append_assoc] using htyped)
  | existsVar _ binderProfile body hbody =>
      let added : List TypeProfile := [binderProfile]
      have hbody' :
          Formula.WellFormed
            (instantiationSourceContext ctx
              (added ++ variablePrefix) functionPrefix levels) body := by
        simpa [instantiationSourceContext, TypingContext.underVar,
          added, List.append_assoc] using hbody
      cases hbodyrun :
          Formula.instantiateVarBlockStep? lower levels replacements
            (variablePrefix.length + 1) functionPrefix.length body with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
          subst result
          have hbodyrun' :
              Formula.instantiateVarBlockStep? lower levels replacements
                (added ++ variablePrefix).length functionPrefix.length body =
                  some body' := by
            simpa [added, Nat.add_comm] using hbodyrun
          have htyped :=
            Formula.WellFormed.instantiateVarBlockStep
              hlower hreplacements hbody' hbodyrun'
          exact .existsVar _ binderProfile body' (by
            simpa [instantiationTargetContext, TypingContext.underVar,
              added, List.append_assoc] using htyped)
  | allFun _ binderProfile body hbody =>
      let added : List FunctionProfile := [binderProfile]
      have hbody' :
          Formula.WellFormed
            (instantiationSourceContext ctx variablePrefix
              (added ++ functionPrefix) levels) body := by
        simpa [instantiationSourceContext, TypingContext.underFun,
          added, List.append_assoc] using hbody
      cases hbodyrun :
          Formula.instantiateVarBlockStep? lower levels replacements
            variablePrefix.length (functionPrefix.length + 1) body with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
          subst result
          have hbodyrun' :
              Formula.instantiateVarBlockStep? lower levels replacements
                variablePrefix.length (added ++ functionPrefix).length body =
                  some body' := by
            simpa [added, Nat.add_comm] using hbodyrun
          have htyped :=
            Formula.WellFormed.instantiateVarBlockStep
              hlower hreplacements hbody' hbodyrun'
          exact .allFun _ binderProfile body' (by
            simpa [instantiationTargetContext, TypingContext.underFun,
              added, List.append_assoc] using htyped)
  | existsFun _ binderProfile body hbody =>
      let added : List FunctionProfile := [binderProfile]
      have hbody' :
          Formula.WellFormed
            (instantiationSourceContext ctx variablePrefix
              (added ++ functionPrefix) levels) body := by
        simpa [instantiationSourceContext, TypingContext.underFun,
          added, List.append_assoc] using hbody
      cases hbodyrun :
          Formula.instantiateVarBlockStep? lower levels replacements
            variablePrefix.length (functionPrefix.length + 1) body with
      | none =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.instantiateVarBlockStep?, hbodyrun] at hrun
          subst result
          have hbodyrun' :
              Formula.instantiateVarBlockStep? lower levels replacements
                variablePrefix.length (added ++ functionPrefix).length body =
                  some body' := by
            simpa [added, Nat.add_comm] using hbodyrun
          have htyped :=
            Formula.WellFormed.instantiateVarBlockStep
              hlower hreplacements hbody' hbodyrun'
          exact .existsFun _ binderProfile body' (by
            simpa [instantiationTargetContext, TypingContext.underFun,
              added, List.append_assoc] using htyped)

/-- One hereditary-instantiation traversal preserves pointwise argument typing. -/
theorem VarietiesHaveTypes.instantiateVarBlockStep
    {lower : LowerVarBlockInstantiation}
    (hlower : LowerVarBlockInstantiation.PreservesTyping lower)
    {ctx : TypingContext}
    {variablePrefix : List TypeProfile}
    {functionPrefix : List FunctionProfile}
    {levels : List Nat} {replacements : List Variety}
    (hreplacements :
      VarietiesHaveTypes ctx replacements (levels.map TypeProfile.monotype))
    {args results : List Variety} {profiles : List TypeProfile}
    (h :
      VarietiesHaveTypes
        (instantiationSourceContext ctx variablePrefix functionPrefix levels)
        args profiles)
    (hrun :
      instantiateVarBlockStepArgs? lower levels replacements
        variablePrefix.length functionPrefix.length args = some results) :
    VarietiesHaveTypes
      (instantiationTargetContext ctx variablePrefix functionPrefix)
      results profiles := by
  cases h with
  | nil _ =>
      simp [instantiateVarBlockStepArgs?] at hrun
      subst results
      exact .nil _
  | cons _ head headType tail tailTypes hhead htail =>
      cases hheadrun :
          Variety.instantiateVarBlockStep? lower levels replacements
            variablePrefix.length functionPrefix.length head with
      | none =>
          simp [instantiateVarBlockStepArgs?, hheadrun] at hrun
      | some head' =>
          cases htailrun :
              instantiateVarBlockStepArgs? lower levels replacements
                variablePrefix.length functionPrefix.length tail with
          | none =>
              simp [instantiateVarBlockStepArgs?, hheadrun, htailrun] at hrun
          | some tail' =>
              simp [instantiateVarBlockStepArgs?, hheadrun, htailrun] at hrun
              subst results
              exact .cons _ head' headType tail' tailTypes
                (Variety.HasType.instantiateVarBlockStep
                  hlower hreplacements hhead hheadrun)
                (VarietiesHaveTypes.instantiateVarBlockStep
                  hlower hreplacements htail htailrun)

end

namespace LowerVarBlockInstantiation

/-- The callback that always fails vacuously preserves typing. -/
theorem none_preserves :
    PreservesTyping (fun _ _ _ => none) := by
  intro ctx levels replacements body result hbody hreplacements hrun
  simp at hrun

end LowerVarBlockInstantiation

namespace Formula

/--
Every fuel stage of hereditary block instantiation preserves well-formedness
whenever it succeeds on a well-typed block and well-typed actual arguments.
-/
theorem hereditaryInstantiateVarBlockFuel_preserves
    (fuel : Nat) :
    LowerVarBlockInstantiation.PreservesTyping
      (Formula.hereditaryInstantiateVarBlockFuel? fuel) := by
  induction fuel with
  | zero =>
      intro ctx levels replacements body result hbody hreplacements hrun
      by_cases hlength : levels.length = replacements.length
      · have hstep :
            Formula.instantiateVarBlockStep? (fun _ _ _ => none)
              levels replacements 0 0 body = some result := by
          simpa [Formula.hereditaryInstantiateVarBlockFuel?, hlength] using hrun
        have hbody' :
            Formula.WellFormed
              (instantiationSourceContext ctx [] [] levels) body := by
          simpa [instantiationSourceContext] using hbody
        have htyped :=
          Formula.WellFormed.instantiateVarBlockStep
            LowerVarBlockInstantiation.none_preserves
            hreplacements hbody' hstep
        simpa [instantiationTargetContext] using htyped
      · simp [Formula.hereditaryInstantiateVarBlockFuel?, hlength] at hrun
  | succ fuel ih =>
      intro ctx levels replacements body result hbody hreplacements hrun
      by_cases hlength : levels.length = replacements.length
      · have hstep :
            Formula.instantiateVarBlockStep?
              (Formula.hereditaryInstantiateVarBlockFuel? fuel)
              levels replacements 0 0 body = some result := by
          simpa [Formula.hereditaryInstantiateVarBlockFuel?, hlength] using hrun
        have hbody' :
            Formula.WellFormed
              (instantiationSourceContext ctx [] [] levels) body := by
          simpa [instantiationSourceContext] using hbody
        have htyped :=
          Formula.WellFormed.instantiateVarBlockStep
            ih hreplacements hbody' hstep
        simpa [instantiationTargetContext] using htyped
      · simp [Formula.hereditaryInstantiateVarBlockFuel?, hlength] at hrun

/-- Arbitrary-height hereditary block instantiation preserves formula formation. -/
theorem hereditaryInstantiateVarBlock_preserves
    {ctx : TypingContext} {levels : List Nat} {replacements : List Variety}
    {body result : Formula}
    (hbody :
      Formula.WellFormed
        { ctx with
          variableTypes := levels.map TypeProfile.monotype ++ ctx.variableTypes }
        body)
    (hreplacements :
      VarietiesHaveTypes ctx replacements (levels.map TypeProfile.monotype))
    (hrun :
      Formula.hereditaryInstantiateVarBlock? levels replacements body =
        some result) :
    Formula.WellFormed ctx result := by
  exact
    Formula.hereditaryInstantiateVarBlockFuel_preserves (maxBinderLevel levels)
      hbody hreplacements
      (by simpa [Formula.hereditaryInstantiateVarBlock?] using hrun)

end Formula

end TakeutiGLC
