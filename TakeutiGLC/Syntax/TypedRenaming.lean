import Mathlib.Tactic
import TakeutiGLC.Syntax.TypingScope
import TakeutiGLC.Syntax.Renaming

/-!
# Typed renaming

The stable syntax keeps typing extrinsic, while bound-index renaming is defined
purely structurally. To use renaming and weakening inside the §5 substitution
metatheory, we need to know when a renaming transports valid de Bruijn lookups
from one typing context to another.

`Renaming.RespectsTyping source target ρ` states exactly that: every variable
or function lookup valid in `source` remains valid, with the same profile, at
the renamed index in `target`.

This file proves that the relation is stable under all Takeuti binders and that
any typing derivation is preserved by a typing-respecting renaming.
-/

namespace TakeutiGLC

namespace Renaming

/--
A bound-index renaming respects two typing contexts when it preserves every
typed lookup in both independent de Bruijn namespaces.
-/
structure RespectsTyping
    (source target : TypingContext) (rename : Renaming) : Prop where
  variable :
    ∀ {index : Nat} {profile : TypeProfile},
      source.variableAt index = some profile →
      target.variableAt (rename.varMap index) = some profile
  function :
    ∀ {index : Nat} {profile : FunctionProfile},
      source.functionAt index = some profile →
      target.functionAt (rename.funMap index) = some profile

namespace RespectsTyping

/-- Identity respects every typing context. -/
theorem identity (ctx : TypingContext) :
    Renaming.RespectsTyping ctx ctx Renaming.identity := by
  constructor
  · intro index profile h
    simpa [Renaming.identity] using h
  · intro index profile h
    simpa [Renaming.identity] using h

/-- Composition of typing-respecting renamings respects the composite contexts. -/
theorem comp
    {source middle target : TypingContext}
    {inner outer : Renaming}
    (hinner : Renaming.RespectsTyping source middle inner)
    (houter : Renaming.RespectsTyping middle target outer) :
    Renaming.RespectsTyping source target (Renaming.comp outer inner) := by
  constructor
  · intro index profile h
    exact houter.variable (hinner.variable h)
  · intro index profile h
    exact houter.function (hinner.function h)

/-- Crossing one variable binder preserves a typing-respecting renaming. -/
theorem underVar
    {source target : TypingContext} {rename : Renaming}
    (h : Renaming.RespectsTyping source target rename)
    (profile : TypeProfile) :
    Renaming.RespectsTyping
      (source.underVar profile) (target.underVar profile) rename.underVar := by
  constructor
  · intro index result hlookup
    cases index with
    | zero =>
        simpa [TypingContext.variableAt, TypingContext.underVar,
          Renaming.underVar, Renaming.liftIndex] using hlookup
    | succ index =>
        have hsource : source.variableAt index = some result := by
          simpa [TypingContext.variableAt, TypingContext.underVar] using hlookup
        have htarget := h.variable hsource
        simpa [TypingContext.variableAt, TypingContext.underVar,
          Renaming.underVar, Renaming.liftIndex] using htarget
  · intro index result hlookup
    have htarget := h.function hlookup
    simpa [TypingContext.functionAt, TypingContext.underVar,
      Renaming.underVar] using htarget

/-- Crossing one function binder preserves a typing-respecting renaming. -/
theorem underFun
    {source target : TypingContext} {rename : Renaming}
    (h : Renaming.RespectsTyping source target rename)
    (profile : FunctionProfile) :
    Renaming.RespectsTyping
      (source.underFun profile) (target.underFun profile) rename.underFun := by
  constructor
  · intro index result hlookup
    have htarget := h.variable hlookup
    simpa [TypingContext.variableAt, TypingContext.underFun,
      Renaming.underFun] using htarget
  · intro index result hlookup
    cases index with
    | zero =>
        simpa [TypingContext.functionAt, TypingContext.underFun,
          Renaming.underFun, Renaming.liftIndex] using hlookup
    | succ index =>
        have hsource : source.functionAt index = some result := by
          simpa [TypingContext.functionAt, TypingContext.underFun] using hlookup
        have htarget := h.function hsource
        simpa [TypingContext.functionAt, TypingContext.underFun,
          Renaming.underFun, Renaming.liftIndex] using htarget

/--
Prepending the same list of variable profiles to both contexts preserves a
typing-respecting renaming, with the variable map lifted by the prefix length.
-/
theorem underVariablePrefix
    {source target : TypingContext} {rename : Renaming}
    (h : Renaming.RespectsTyping source target rename)
    (profiles : List TypeProfile) :
    Renaming.RespectsTyping
      { source with variableTypes := profiles ++ source.variableTypes }
      { target with variableTypes := profiles ++ target.variableTypes }
      { rename with varMap := Renaming.liftIndexBy profiles.length rename.varMap } := by
  induction profiles with
  | nil =>
      simpa [Renaming.liftIndexBy] using h
  | cons profile profiles ih =>
      have hstep := ih.underVar profile
      simpa [TypingContext.underVar, List.cons_append, Renaming.liftIndexBy] using hstep

/-- Crossing one simultaneous Takeuti abstraction block preserves typed renaming. -/
theorem underBlock
    {source target : TypingContext} {rename : Renaming}
    (h : Renaming.RespectsTyping source target rename)
    (headLevel : Nat) (tailLevels : List Nat) :
    Renaming.RespectsTyping
      (source.underBlock headLevel tailLevels)
      (target.underBlock headLevel tailLevels)
      (rename.underBlock tailLevels) := by
  have hprefix :=
    h.underVariablePrefix (abstractionBinderTypes headLevel tailLevels)
  simpa [TypingContext.underBlock, Renaming.underBlock,
    abstractionBinderTypes, blockSize] using hprefix

end RespectsTyping

end Renaming

mutual

/-- Typed renaming preserves the type of a variety. -/
theorem Variety.HasType.rename
    {source target : TypingContext} {rename : Renaming}
    (hrename : Renaming.RespectsTyping source target rename)
    {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType source variety profile) :
    Variety.HasType target (variety.rename rename) profile :=
  match h with
  | .freeVar _ name hprofile =>
      .freeVar target name hprofile
  | .specialVar _ name hprofile =>
      .specialVar target name hprofile
  | .boundVar _ index hlookup =>
      .boundVar target (rename.varMap index) (hrename.variable hlookup)
  | .freeFunApp _ name args hargs =>
      .freeFunApp target name _ (VarietiesHaveTypes.rename hrename hargs)
  | .specialFunApp _ name args hargs =>
      .specialFunApp target name _ (VarietiesHaveTypes.rename hrename hargs)
  | .boundFunApp _ index functionProfile args hlookup hargs =>
      .boundFunApp target (rename.funMap index) functionProfile _
        (hrename.function hlookup)
        (VarietiesHaveTypes.rename hrename hargs)
  | .abstract _ headLevel tailLevels body hbody =>
      .abstract target headLevel tailLevels _ (by
        simpa [Variety.rename] using
          Formula.WellFormed.rename
            (hrename.underBlock headLevel tailLevels) hbody)

/-- Typed renaming preserves well-formed formulas. -/
theorem Formula.WellFormed.rename
    {source target : TypingContext} {rename : Renaming}
    (hrename : Renaming.RespectsTyping source target rename)
    {formula : Formula}
    (h : Formula.WellFormed source formula) :
    Formula.WellFormed target (formula.rename rename) :=
  match h with
  | .atomFree _ name args hnonzero hargs =>
      .atomFree target name _ hnonzero (VarietiesHaveTypes.rename hrename hargs)
  | .atomSpecial _ name args hnonzero hargs =>
      .atomSpecial target name _ hnonzero (VarietiesHaveTypes.rename hrename hargs)
  | .atomBound _ index profile args hlookup hnonzero hargs =>
      .atomBound target (rename.varMap index) profile _
        (hrename.variable hlookup) hnonzero
        (VarietiesHaveTypes.rename hrename hargs)
  | .neg _ body hbody =>
      .neg target _ (Formula.WellFormed.rename hrename hbody)
  | .conj _ left right hleft hright =>
      .conj target _ _
        (Formula.WellFormed.rename hrename hleft)
        (Formula.WellFormed.rename hrename hright)
  | .disj _ left right hleft hright =>
      .disj target _ _
        (Formula.WellFormed.rename hrename hleft)
        (Formula.WellFormed.rename hrename hright)
  | .allVar _ profile body hbody =>
      .allVar target profile _ (by
        simpa [Formula.rename] using
          Formula.WellFormed.rename (hrename.underVar profile) hbody)
  | .existsVar _ profile body hbody =>
      .existsVar target profile _ (by
        simpa [Formula.rename] using
          Formula.WellFormed.rename (hrename.underVar profile) hbody)
  | .allFun _ profile body hbody =>
      .allFun target profile _ (by
        simpa [Formula.rename] using
          Formula.WellFormed.rename (hrename.underFun profile) hbody)
  | .existsFun _ profile body hbody =>
      .existsFun target profile _ (by
        simpa [Formula.rename] using
          Formula.WellFormed.rename (hrename.underFun profile) hbody)

/-- Typed renaming preserves pointwise argument typing. -/
theorem VarietiesHaveTypes.rename
    {source target : TypingContext} {rename : Renaming}
    (hrename : Renaming.RespectsTyping source target rename)
    {args : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes source args profiles) :
    VarietiesHaveTypes target (args.map (Variety.rename rename)) profiles :=
  match h with
  | .nil _ => .nil target
  | .cons _ head headType tail tailTypes hhead htail =>
      .cons target _ headType _ tailTypes
        (Variety.HasType.rename hrename hhead)
        (VarietiesHaveTypes.rename hrename htail)

end

/-- Typed renaming preserves the type of a functional. -/
theorem Functional.HasType.rename
    {source target : TypingContext} {rename : Renaming}
    (hrename : Renaming.RespectsTyping source target rename)
    {functional : Functional} {profile : TypeProfile}
    (h : Functional.HasType source functional profile) :
    Functional.HasType target (functional.rename rename) profile := by
  cases h with
  | abstract headLevel tailLevels body hbody =>
      exact .abstract target headLevel tailLevels _ (by
        simpa [Functional.rename] using
          Variety.HasType.rename
            (hrename.underBlock headLevel tailLevels) hbody)

/-- Typed renaming preserves the §2.10 term judgment. -/
theorem Variety.IsTerm.rename
    {source target : TypingContext} {rename : Renaming}
    (hrename : Renaming.RespectsTyping source target rename)
    {variety : Variety}
    (h : Variety.IsTerm source variety) :
    Variety.IsTerm target (variety.rename rename) :=
  Variety.HasType.rename hrename h

/-- Typed renaming preserves existential well-typing of a variety. -/
theorem Variety.WellTyped.rename
    {source target : TypingContext} {rename : Renaming}
    (hrename : Renaming.RespectsTyping source target rename)
    {variety : Variety}
    (h : Variety.WellTyped source variety) :
    Variety.WellTyped target (variety.rename rename) := by
  obtain ⟨profile, htype⟩ := h
  exact ⟨profile, Variety.HasType.rename hrename htype⟩

end TakeutiGLC
