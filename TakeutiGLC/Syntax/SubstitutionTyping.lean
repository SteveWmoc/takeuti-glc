import Mathlib.Tactic
import TakeutiGLC.Syntax.Substitution
import TakeutiGLC.Syntax.HereditaryInstantiationTyping

/-!
# Formation preservation for complete variable substitution

Takeuti §5.2.29 states that complete substitution sends formulas to formulas,
and §5.2.30 states that it preserves the type of a variety. The stable core has
extrinsic formation judgments, so these become preservation theorems for
`Formula.WellFormed` and `Variety.HasType`.

The proof follows the recursive substitution definition. Binder cases use the
typed weakening layer; the higher-type atomic case uses hereditary block
instantiation together with its typing theorem.
-/

namespace TakeutiGLC

namespace Variety.HasType

/-- A variety of a specified nonzero profile is the corresponding abstraction. -/
theorem higher_inv
    {ctx : TypingContext} {variety : Variety}
    {headLevel : Nat} {tailLevels : List Nat}
    (h : Variety.HasType ctx variety (.higher headLevel tailLevels)) :
    ∃ body,
      variety = .abstract headLevel tailLevels body ∧
      Formula.WellFormed (ctx.underBlock headLevel tailLevels) body := by
  cases h with
  | abstract _ head tail body hbody =>
      exact ⟨body, rfl, hbody⟩

end Variety.HasType

mutual

/-- Takeuti §5.2.30: successful complete substitution preserves a variety's type. -/
theorem Variety.HasType.completeSubstituteVar
    {ctx : TypingContext} {target : VariableName} {replacement : Variety}
    (hreplacement : Variety.HasType ctx replacement target.profile)
    {variety result : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile)
    (hrun :
      Variety.completeSubstituteVar? target replacement variety = some result) :
    Variety.HasType ctx result profile := by
  cases h with
  | freeVar _ name hprofile =>
      by_cases hname : name = target
      · subst name
        have htargetZero : target.profile = .zero := hprofile
        simp [Variety.completeSubstituteVar?, htargetZero] at hrun
        subst result
        simpa [htargetZero] using hreplacement
      · simp [Variety.completeSubstituteVar?, hname] at hrun
        subst result
        exact .freeVar _ name hprofile
  | specialVar _ name hprofile =>
      simp [Variety.completeSubstituteVar?] at hrun
      subst result
      exact .specialVar _ name hprofile
  | boundVar _ index hlookup =>
      simp [Variety.completeSubstituteVar?] at hrun
      subst result
      exact .boundVar _ index hlookup
  | freeFunApp _ name args hargs =>
      cases hargsrun : completeSubstituteVarArgs? target replacement args with
      | none =>
          simp [Variety.completeSubstituteVar?, hargsrun] at hrun
      | some args' =>
          simp [Variety.completeSubstituteVar?, hargsrun] at hrun
          subst result
          exact .freeFunApp _ name args'
            (VarietiesHaveTypes.completeSubstituteVar
              hreplacement hargs hargsrun)
  | specialFunApp _ name args hargs =>
      cases hargsrun : completeSubstituteVarArgs? target replacement args with
      | none =>
          simp [Variety.completeSubstituteVar?, hargsrun] at hrun
      | some args' =>
          simp [Variety.completeSubstituteVar?, hargsrun] at hrun
          subst result
          exact .specialFunApp _ name args'
            (VarietiesHaveTypes.completeSubstituteVar
              hreplacement hargs hargsrun)
  | boundFunApp _ index functionProfile args hlookup hargs =>
      cases hargsrun : completeSubstituteVarArgs? target replacement args with
      | none =>
          simp [Variety.completeSubstituteVar?, hargsrun] at hrun
      | some args' =>
          simp [Variety.completeSubstituteVar?, hargsrun] at hrun
          subst result
          exact .boundFunApp _ index functionProfile args' hlookup
            (VarietiesHaveTypes.completeSubstituteVar
              hreplacement hargs hargsrun)
  | abstract _ headLevel tailLevels body hbody =>
      cases hbodyrun :
          Formula.completeSubstituteVar? target
            (replacement.weakenVarBy (blockSize tailLevels)) body with
      | none =>
          simp [Variety.completeSubstituteVar?, hbodyrun] at hrun
      | some body' =>
          simp [Variety.completeSubstituteVar?, hbodyrun] at hrun
          subst result
          have hreplacement' :
              Variety.HasType (ctx.underBlock headLevel tailLevels)
                (replacement.weakenVarBy (blockSize tailLevels)) target.profile :=
            hreplacement.weakenUnderBlock headLevel tailLevels
          exact .abstract _ headLevel tailLevels body'
            (Formula.WellFormed.completeSubstituteVar
              hreplacement' hbody hbodyrun)

/-- Takeuti §5.2.29: successful complete substitution preserves formula formation. -/
theorem Formula.WellFormed.completeSubstituteVar
    {ctx : TypingContext} {target : VariableName} {replacement : Variety}
    (hreplacement : Variety.HasType ctx replacement target.profile)
    {formula result : Formula}
    (h : Formula.WellFormed ctx formula)
    (hrun :
      Formula.completeSubstituteVar? target replacement formula = some result) :
    Formula.WellFormed ctx result := by
  cases h with
  | atomFree _ name args hnonzero hargs =>
      cases hargsrun : completeSubstituteVarArgs? target replacement args with
      | none =>
          simp [Formula.completeSubstituteVar?, hargsrun] at hrun
      | some args' =>
          have hargs' :=
            VarietiesHaveTypes.completeSubstituteVar
              hreplacement hargs hargsrun
          by_cases hname : name = target
          · subst name
            cases htargetProfile : target.profile with
            | zero =>
                exact False.elim (hnonzero htargetProfile)
            | higher headLevel tailLevels =>
                have hreplacement' :
                    Variety.HasType ctx replacement (.higher headLevel tailLevels) := by
                  simpa [htargetProfile] using hreplacement
                obtain ⟨replacementBody, hreplacementShape, hreplacementBody⟩ :=
                  hreplacement'.higher_inv
                subst replacement
                have hargsTyped :
                    VarietiesHaveTypes ctx args'
                      ((headLevel :: tailLevels).map TypeProfile.monotype) := by
                  simpa [htargetProfile] using hargs'
                have hrun' := hrun
                simp only [Formula.completeSubstituteVar?] at hrun'
                rw [hargsrun] at hrun'
                simp [htargetProfile, abstractionProfile] at hrun'
                by_cases hlength : args'.length = blockSize tailLevels
                · have hheritage :
                      Formula.hereditaryInstantiateVarBlock?
                        (headLevel :: tailLevels) args' replacementBody =
                          some result := by
                    simpa [hlength] using hrun'
                  have hbodyTyped :
                      Formula.WellFormed
                        { ctx with
                          variableTypes :=
                            (headLevel :: tailLevels).map TypeProfile.monotype ++
                              ctx.variableTypes }
                        replacementBody := by
                    simpa [TypingContext.underBlock, abstractionBinderTypes] using
                      hreplacementBody
                  exact Formula.hereditaryInstantiateVarBlock_preserves
                    hbodyTyped hargsTyped hheritage
                · simp [hlength] at hrun'
          · simp [Formula.completeSubstituteVar?, hargsrun, hname] at hrun
            subst result
            exact .atomFree _ name args' hnonzero hargs'
  | atomSpecial _ name args hnonzero hargs =>
      cases hargsrun : completeSubstituteVarArgs? target replacement args with
      | none =>
          simp [Formula.completeSubstituteVar?, hargsrun] at hrun
      | some args' =>
          simp [Formula.completeSubstituteVar?, hargsrun] at hrun
          subst result
          exact .atomSpecial _ name args' hnonzero
            (VarietiesHaveTypes.completeSubstituteVar
              hreplacement hargs hargsrun)
  | atomBound _ index profile args hlookup hnonzero hargs =>
      cases hargsrun : completeSubstituteVarArgs? target replacement args with
      | none =>
          simp [Formula.completeSubstituteVar?, hargsrun] at hrun
      | some args' =>
          simp [Formula.completeSubstituteVar?, hargsrun] at hrun
          subst result
          exact .atomBound _ index profile args' hlookup hnonzero
            (VarietiesHaveTypes.completeSubstituteVar
              hreplacement hargs hargsrun)
  | neg _ body hbody =>
      cases hbodyrun :
          Formula.completeSubstituteVar? target replacement body with
      | none =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
          subst result
          exact .neg _ body'
            (Formula.WellFormed.completeSubstituteVar
              hreplacement hbody hbodyrun)
  | conj _ left right hleft hright =>
      cases hleftrun :
          Formula.completeSubstituteVar? target replacement left with
      | none =>
          simp [Formula.completeSubstituteVar?, hleftrun] at hrun
      | some left' =>
          cases hrightrun :
              Formula.completeSubstituteVar? target replacement right with
          | none =>
              simp [Formula.completeSubstituteVar?, hleftrun, hrightrun] at hrun
          | some right' =>
              simp [Formula.completeSubstituteVar?, hleftrun, hrightrun] at hrun
              subst result
              exact .conj _ left' right'
                (Formula.WellFormed.completeSubstituteVar
                  hreplacement hleft hleftrun)
                (Formula.WellFormed.completeSubstituteVar
                  hreplacement hright hrightrun)
  | disj _ left right hleft hright =>
      cases hleftrun :
          Formula.completeSubstituteVar? target replacement left with
      | none =>
          simp [Formula.completeSubstituteVar?, hleftrun] at hrun
      | some left' =>
          cases hrightrun :
              Formula.completeSubstituteVar? target replacement right with
          | none =>
              simp [Formula.completeSubstituteVar?, hleftrun, hrightrun] at hrun
          | some right' =>
              simp [Formula.completeSubstituteVar?, hleftrun, hrightrun] at hrun
              subst result
              exact .disj _ left' right'
                (Formula.WellFormed.completeSubstituteVar
                  hreplacement hleft hleftrun)
                (Formula.WellFormed.completeSubstituteVar
                  hreplacement hright hrightrun)
  | allVar _ binderProfile body hbody =>
      cases hbodyrun :
          Formula.completeSubstituteVar? target replacement.weakenVar body with
      | none =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
          subst result
          exact .allVar _ binderProfile body'
            (Formula.WellFormed.completeSubstituteVar
              (hreplacement.weakenVar binderProfile) hbody hbodyrun)
  | existsVar _ binderProfile body hbody =>
      cases hbodyrun :
          Formula.completeSubstituteVar? target replacement.weakenVar body with
      | none =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
          subst result
          exact .existsVar _ binderProfile body'
            (Formula.WellFormed.completeSubstituteVar
              (hreplacement.weakenVar binderProfile) hbody hbodyrun)
  | allFun _ binderProfile body hbody =>
      cases hbodyrun :
          Formula.completeSubstituteVar? target replacement.weakenFun body with
      | none =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
          subst result
          exact .allFun _ binderProfile body'
            (Formula.WellFormed.completeSubstituteVar
              (hreplacement.weakenFun binderProfile) hbody hbodyrun)
  | existsFun _ binderProfile body hbody =>
      cases hbodyrun :
          Formula.completeSubstituteVar? target replacement.weakenFun body with
      | none =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
      | some body' =>
          simp [Formula.completeSubstituteVar?, hbodyrun] at hrun
          subst result
          exact .existsFun _ binderProfile body'
            (Formula.WellFormed.completeSubstituteVar
              (hreplacement.weakenFun binderProfile) hbody hbodyrun)

/-- Complete substitution preserves pointwise argument typing. -/
theorem VarietiesHaveTypes.completeSubstituteVar
    {ctx : TypingContext} {target : VariableName} {replacement : Variety}
    (hreplacement : Variety.HasType ctx replacement target.profile)
    {args results : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes ctx args profiles)
    (hrun : completeSubstituteVarArgs? target replacement args = some results) :
    VarietiesHaveTypes ctx results profiles := by
  cases h with
  | nil _ =>
      simp [completeSubstituteVarArgs?] at hrun
      subst results
      exact .nil _
  | cons _ head headType tail tailTypes hhead htail =>
      cases hheadrun :
          Variety.completeSubstituteVar? target replacement head with
      | none =>
          simp [completeSubstituteVarArgs?, hheadrun] at hrun
      | some head' =>
          cases htailrun :
              completeSubstituteVarArgs? target replacement tail with
          | none =>
              simp [completeSubstituteVarArgs?, hheadrun, htailrun] at hrun
          | some tail' =>
              simp [completeSubstituteVarArgs?, hheadrun, htailrun] at hrun
              subst results
              exact .cons _ head' headType tail' tailTypes
                (Variety.HasType.completeSubstituteVar
                  hreplacement hhead hheadrun)
                (VarietiesHaveTypes.completeSubstituteVar
                  hreplacement htail htailrun)

end

namespace Functional.HasType

/-- Complete variable substitution preserves the type of a functional. -/
theorem completeSubstituteVar
    {ctx : TypingContext} {target : VariableName} {replacement : Variety}
    (hreplacement : Variety.HasType ctx replacement target.profile)
    {functional result : Functional} {profile : TypeProfile}
    (h : Functional.HasType ctx functional profile)
    (hrun :
      Functional.completeSubstituteVar? target replacement functional =
        some result) :
    Functional.HasType ctx result profile := by
  cases h with
  | abstract headLevel tailLevels body hbody =>
      cases hbodyrun :
          Variety.completeSubstituteVar? target
            (replacement.weakenVarBy (blockSize tailLevels)) body with
      | none =>
          simp [Functional.completeSubstituteVar?, hbodyrun] at hrun
      | some body' =>
          have hrun' := hrun
          simp only [Functional.completeSubstituteVar?] at hrun'
          rw [hbodyrun] at hrun'
          simp at hrun'
          subst result
          have hreplacement' :
              Variety.HasType (ctx.underBlock headLevel tailLevels)
                (replacement.weakenVarBy (blockSize tailLevels)) target.profile :=
            hreplacement.weakenUnderBlock headLevel tailLevels
          exact .abstract _ headLevel tailLevels body'
            (Variety.HasType.completeSubstituteVar
              hreplacement' hbody hbodyrun)

end Functional.HasType

namespace Variety.IsTerm

/-- Complete variable substitution preserves the §2.10 term judgment. -/
theorem completeSubstituteVar
    {ctx : TypingContext} {target : VariableName} {replacement : Variety}
    (hreplacement : Variety.HasType ctx replacement target.profile)
    {term result : Variety}
    (h : Variety.IsTerm ctx term)
    (hrun : Variety.completeSubstituteVar? target replacement term = some result) :
    Variety.IsTerm ctx result :=
  Variety.HasType.completeSubstituteVar hreplacement h hrun

end Variety.IsTerm

namespace Variety.WellTyped

/-- Complete variable substitution preserves existential variety well-typing. -/
theorem completeSubstituteVar
    {ctx : TypingContext} {target : VariableName} {replacement : Variety}
    (hreplacement : Variety.HasType ctx replacement target.profile)
    {variety result : Variety}
    (h : Variety.WellTyped ctx variety)
    (hrun : Variety.completeSubstituteVar? target replacement variety = some result) :
    Variety.WellTyped ctx result := by
  obtain ⟨profile, htype⟩ := h
  exact ⟨profile, Variety.HasType.completeSubstituteVar hreplacement htype hrun⟩

end Variety.WellTyped

namespace Functional.WellFormed

/-- Complete variable substitution preserves functional well-formedness. -/
theorem completeSubstituteVar
    {ctx : TypingContext} {target : VariableName} {replacement : Variety}
    (hreplacement : Variety.HasType ctx replacement target.profile)
    {functional result : Functional}
    (h : Functional.WellFormed ctx functional)
    (hrun :
      Functional.completeSubstituteVar? target replacement functional =
        some result) :
    Functional.WellFormed ctx result :=
  Functional.HasType.completeSubstituteVar hreplacement h hrun

end Functional.WellFormed

end TakeutiGLC
