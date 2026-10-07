import TakeutiGLC.Syntax.TypedRenaming

/-!
# Typed weakening

Structural weakening is already implemented as a special bound-index renaming.
This file specializes the generic typed-renaming metatheory to the weakening
operations used by substitution when a replacement crosses a binder.

The key one-step results insert a fresh outermost variable or function profile.
For Takeuti abstraction blocks we additionally prove an iterated variable
weakening theorem: a typed variety remains typed after enough fresh variable
slots are inserted to pass beneath the whole simultaneous block.
-/

namespace TakeutiGLC

namespace Renaming.RespectsTyping

/-- Inserting one fresh outermost variable slot respects typing. -/
theorem weakenVar (ctx : TypingContext) (inserted : TypeProfile) :
    Renaming.RespectsTyping
      ctx (ctx.underVar inserted) (Renaming.weakenVarAt 0) := by
  constructor
  · intro index profile hlookup
    simpa [Renaming.weakenVarAt, insertIndex, TypingContext.variableAt,
      TypingContext.underVar] using hlookup
  · intro index profile hlookup
    simpa [Renaming.weakenVarAt, TypingContext.functionAt,
      TypingContext.underVar] using hlookup

/-- Inserting one fresh outermost function slot respects typing. -/
theorem weakenFun (ctx : TypingContext) (inserted : FunctionProfile) :
    Renaming.RespectsTyping
      ctx (ctx.underFun inserted) (Renaming.weakenFunAt 0) := by
  constructor
  · intro index profile hlookup
    simpa [Renaming.weakenFunAt, TypingContext.variableAt,
      TypingContext.underFun] using hlookup
  · intro index profile hlookup
    simpa [Renaming.weakenFunAt, insertIndex, TypingContext.functionAt,
      TypingContext.underFun] using hlookup

end Renaming.RespectsTyping

namespace Variety.HasType

/-- A typed variety remains typed after one fresh outer variable binder is inserted. -/
theorem weakenVar
    {ctx : TypingContext} {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile) (inserted : TypeProfile) :
    Variety.HasType (ctx.underVar inserted) variety.weakenVar profile := by
  simpa [Variety.weakenVar, Variety.weakenVarAt] using
    Variety.HasType.rename (Renaming.RespectsTyping.weakenVar ctx inserted) h

/-- A typed variety remains typed after one fresh outer function binder is inserted. -/
theorem weakenFun
    {ctx : TypingContext} {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile) (inserted : FunctionProfile) :
    Variety.HasType (ctx.underFun inserted) variety.weakenFun profile := by
  simpa [Variety.weakenFun, Variety.weakenFunAt] using
    Variety.HasType.rename (Renaming.RespectsTyping.weakenFun ctx inserted) h

/--
Iterated variable weakening, with the inserted profiles listed in reverse
insertion order.

This form follows the recursion of `Variety.weakenVarBy`: the head profile is
inserted first, then later insertions are placed outside it.
-/
theorem weakenVarByReverse
    {ctx : TypingContext} {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile) (inserted : List TypeProfile) :
    Variety.HasType
      { ctx with variableTypes := inserted.reverse ++ ctx.variableTypes }
      (variety.weakenVarBy inserted.length) profile := by
  induction inserted generalizing ctx variety with
  | nil =>
      simpa using h
  | cons head tail ih =>
      have hhead :
          Variety.HasType (ctx.underVar head) variety.weakenVar profile :=
        h.weakenVar head
      have htail := ih hhead
      simpa [Variety.weakenVarBy, TypingContext.underVar, List.reverse_cons,
        List.append_assoc] using htail

/-- A typed variety may be weakened beneath an arbitrary prefix of variable types. -/
theorem weakenVarPrefix
    {ctx : TypingContext} {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile) (inserted : List TypeProfile) :
    Variety.HasType
      { ctx with variableTypes := inserted ++ ctx.variableTypes }
      (variety.weakenVarBy inserted.length) profile := by
  simpa using h.weakenVarByReverse inserted.reverse

/--
A typed variety may pass beneath an entire Takeuti abstraction block.

This is the weakening shape used by complete substitution when its replacement
enters an abstraction body.
-/
theorem weakenUnderBlock
    {ctx : TypingContext} {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile)
    (headLevel : Nat) (tailLevels : List Nat) :
    Variety.HasType
      (ctx.underBlock headLevel tailLevels)
      (variety.weakenVarBy (blockSize tailLevels)) profile := by
  have hpref :=
    h.weakenVarPrefix (abstractionBinderTypes headLevel tailLevels)
  simpa [TypingContext.underBlock, abstractionBinderTypes, blockSize] using hpref

end Variety.HasType

namespace Formula.WellFormed

/-- Well-formed formulas remain well formed after one fresh variable binder. -/
theorem weakenVar
    {ctx : TypingContext} {formula : Formula}
    (h : Formula.WellFormed ctx formula) (inserted : TypeProfile) :
    Formula.WellFormed (ctx.underVar inserted) formula.weakenVar := by
  simpa [Formula.weakenVar, Formula.weakenVarAt] using
    Formula.WellFormed.rename (Renaming.RespectsTyping.weakenVar ctx inserted) h

/-- Well-formed formulas remain well formed after one fresh function binder. -/
theorem weakenFun
    {ctx : TypingContext} {formula : Formula}
    (h : Formula.WellFormed ctx formula) (inserted : FunctionProfile) :
    Formula.WellFormed (ctx.underFun inserted) formula.weakenFun := by
  simpa [Formula.weakenFun, Formula.weakenFunAt] using
    Formula.WellFormed.rename (Renaming.RespectsTyping.weakenFun ctx inserted) h

end Formula.WellFormed

namespace VarietiesHaveTypes

/-- Pointwise argument typing is preserved by one fresh variable binder. -/
theorem weakenVar
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes ctx args profiles) (inserted : TypeProfile) :
    VarietiesHaveTypes (ctx.underVar inserted)
      (args.map Variety.weakenVar) profiles :=
  match h with
  | .nil _ => .nil (ctx.underVar inserted)
  | .cons _ head headType tail tailTypes hhead htail =>
      .cons (ctx.underVar inserted) _ headType _ tailTypes
        (Variety.HasType.weakenVar hhead inserted)
        (VarietiesHaveTypes.weakenVar htail inserted)

/-- Pointwise argument typing is preserved by one fresh function binder. -/
theorem weakenFun
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes ctx args profiles) (inserted : FunctionProfile) :
    VarietiesHaveTypes (ctx.underFun inserted)
      (args.map Variety.weakenFun) profiles :=
  match h with
  | .nil _ => .nil (ctx.underFun inserted)
  | .cons _ head headType tail tailTypes hhead htail =>
      .cons (ctx.underFun inserted) _ headType _ tailTypes
        (Variety.HasType.weakenFun hhead inserted)
        (VarietiesHaveTypes.weakenFun htail inserted)

end VarietiesHaveTypes

namespace Functional.HasType

/-- Typed functionals remain typed after one fresh variable binder. -/
theorem weakenVar
    {ctx : TypingContext} {functional : Functional} {profile : TypeProfile}
    (h : Functional.HasType ctx functional profile) (inserted : TypeProfile) :
    Functional.HasType (ctx.underVar inserted) functional.weakenVar profile := by
  simpa [Functional.weakenVar, Functional.weakenVarAt] using
    Functional.HasType.rename (Renaming.RespectsTyping.weakenVar ctx inserted) h

/-- Typed functionals remain typed after one fresh function binder. -/
theorem weakenFun
    {ctx : TypingContext} {functional : Functional} {profile : TypeProfile}
    (h : Functional.HasType ctx functional profile) (inserted : FunctionProfile) :
    Functional.HasType (ctx.underFun inserted) functional.weakenFun profile := by
  simpa [Functional.weakenFun, Functional.weakenFunAt] using
    Functional.HasType.rename (Renaming.RespectsTyping.weakenFun ctx inserted) h

end Functional.HasType

namespace Variety.IsTerm

/-- Terms remain terms after one fresh variable binder. -/
theorem weakenVar
    {ctx : TypingContext} {variety : Variety}
    (h : Variety.IsTerm ctx variety) (inserted : TypeProfile) :
    Variety.IsTerm (ctx.underVar inserted) variety.weakenVar :=
  Variety.HasType.weakenVar h inserted

/-- Terms remain terms after one fresh function binder. -/
theorem weakenFun
    {ctx : TypingContext} {variety : Variety}
    (h : Variety.IsTerm ctx variety) (inserted : FunctionProfile) :
    Variety.IsTerm (ctx.underFun inserted) variety.weakenFun :=
  Variety.HasType.weakenFun h inserted

/-- Terms may be weakened beneath a whole Takeuti abstraction block. -/
theorem weakenUnderBlock
    {ctx : TypingContext} {variety : Variety}
    (h : Variety.IsTerm ctx variety)
    (headLevel : Nat) (tailLevels : List Nat) :
    Variety.IsTerm (ctx.underBlock headLevel tailLevels)
      (variety.weakenVarBy (blockSize tailLevels)) :=
  Variety.HasType.weakenUnderBlock h headLevel tailLevels

end Variety.IsTerm

namespace Variety.WellTyped

/-- Existential variety typing is preserved by one fresh variable binder. -/
theorem weakenVar
    {ctx : TypingContext} {variety : Variety}
    (h : Variety.WellTyped ctx variety) (inserted : TypeProfile) :
    Variety.WellTyped (ctx.underVar inserted) variety.weakenVar := by
  obtain ⟨profile, htype⟩ := h
  exact ⟨profile, Variety.HasType.weakenVar htype inserted⟩

/-- Existential variety typing is preserved by one fresh function binder. -/
theorem weakenFun
    {ctx : TypingContext} {variety : Variety}
    (h : Variety.WellTyped ctx variety) (inserted : FunctionProfile) :
    Variety.WellTyped (ctx.underFun inserted) variety.weakenFun := by
  obtain ⟨profile, htype⟩ := h
  exact ⟨profile, Variety.HasType.weakenFun htype inserted⟩

end Variety.WellTyped

namespace Functional.WellFormed

/-- Functional well-formedness is preserved by one fresh variable binder. -/
theorem weakenVar
    {ctx : TypingContext} {functional : Functional}
    (h : Functional.WellFormed ctx functional) (inserted : TypeProfile) :
    Functional.WellFormed (ctx.underVar inserted) functional.weakenVar := by
  exact Functional.HasType.weakenVar h inserted

/-- Functional well-formedness is preserved by one fresh function binder. -/
theorem weakenFun
    {ctx : TypingContext} {functional : Functional}
    (h : Functional.WellFormed ctx functional) (inserted : FunctionProfile) :
    Functional.WellFormed (ctx.underFun inserted) functional.weakenFun := by
  exact Functional.HasType.weakenFun h inserted

end Functional.WellFormed

end TakeutiGLC
