import Mathlib.Tactic
import TakeutiGLC.Syntax.Typing

/-!
# From extrinsic typing to structural scope

Our raw syntax deliberately carries natural-number de Bruijn indices without
intrinsic bounds. The typing judgments in `Typing.lean` look those indices up
in independent variable and function contexts. A successful lookup therefore
supplies the corresponding structural scope bound.

The theorems below establish this bridge for every mutually inductive
syntactic category. They are a prerequisite for the §5.2.29–§5.2.30
substitution-preservation proofs: those proofs can use typed source and
replacement figures without carrying independent, redundant assumptions
about their de Bruijn scope.
-/

namespace TakeutiGLC

namespace TypingContext

/-- A successful variable lookup gives a valid variable de Bruijn index. -/
theorem variableAt_lt {ctx : TypingContext} {index : Nat}
    {profile : TypeProfile} (h : ctx.variableAt index = some profile) :
    index < ctx.variableTypes.length := by
  by_contra hnot
  have hnone : ctx.variableTypes[index]? = none := by
    simp [Nat.le_of_not_gt hnot]
  simp [variableAt, hnone] at h

/-- A successful function lookup gives a valid function de Bruijn index. -/
theorem functionAt_lt {ctx : TypingContext} {index : Nat}
    {profile : FunctionProfile} (h : ctx.functionAt index = some profile) :
    index < ctx.functionProfiles.length := by
  by_contra hnot
  have hnone : ctx.functionProfiles[index]? = none := by
    simp [Nat.le_of_not_gt hnot]
  simp [functionAt, hnone] at h

/-- Forgetting a variable binder in a typing context agrees with structural scope. -/
@[simp] theorem scope_underVar (ctx : TypingContext) (profile : TypeProfile) :
    (ctx.underVar profile).scope = ctx.scope.underVar := rfl

/-- Forgetting a function binder in a typing context agrees with structural scope. -/
@[simp] theorem scope_underFun (ctx : TypingContext) (profile : FunctionProfile) :
    (ctx.underFun profile).scope = ctx.scope.underFun := rfl

/-- A simultaneous abstraction block extends exactly the same scope in both layers. -/
@[simp] theorem scope_underBlock
    (ctx : TypingContext) (headLevel : Nat) (tailLevels : List Nat) :
    (ctx.underBlock headLevel tailLevels).scope =
      ctx.scope.underBlock tailLevels := by
  simp [TypingContext.scope, TypingContext.underBlock, Scope.underBlock,
    abstractionBinderTypes, blockSize, Nat.add_comm]; omega

end TypingContext

mutual

/-- A well-typed variety is structurally well scoped in the forgotten typing context. -/
theorem Variety.HasType.toWellScoped
    {ctx : TypingContext} {variety : Variety} {profile : TypeProfile}
    (h : Variety.HasType ctx variety profile) :
    Variety.WellScoped ctx.scope variety :=
  match h with
  | .freeVar ctx name _ => .freeVar ctx.scope name
  | .specialVar ctx name _ => .specialVar ctx.scope name
  | .boundVar ctx index hlookup =>
      .boundVar ctx.scope index (TypingContext.variableAt_lt hlookup)
  | .freeFunApp ctx name args hargs =>
      .freeFunApp ctx.scope name args (VarietiesHaveTypes.toWellScoped hargs)
  | .specialFunApp ctx name args hargs =>
      .specialFunApp ctx.scope name args (VarietiesHaveTypes.toWellScoped hargs)
  | .boundFunApp ctx index _ args hlookup hargs =>
      .boundFunApp ctx.scope index args
        (TypingContext.functionAt_lt hlookup)
        (VarietiesHaveTypes.toWellScoped hargs)
  | .abstract ctx headLevel tailLevels body hbody =>
      .abstract ctx.scope headLevel tailLevels body (by
        simpa only [TypingContext.scope_underBlock] using
          Formula.WellFormed.toWellScoped hbody)

/-- A well-formed formula is structurally well scoped. -/
theorem Formula.WellFormed.toWellScoped
    {ctx : TypingContext} {formula : Formula}
    (h : Formula.WellFormed ctx formula) :
    Formula.WellScoped ctx.scope formula :=
  match h with
  | .atomFree ctx name args _ hargs =>
      .atomFree ctx.scope name args (VarietiesHaveTypes.toWellScoped hargs)
  | .atomSpecial ctx name args _ hargs =>
      .atomSpecial ctx.scope name args (VarietiesHaveTypes.toWellScoped hargs)
  | .atomBound ctx index _ args hlookup _ hargs =>
      .atomBound ctx.scope index args
        (TypingContext.variableAt_lt hlookup)
        (VarietiesHaveTypes.toWellScoped hargs)
  | .neg ctx body hbody =>
      .neg ctx.scope body (Formula.WellFormed.toWellScoped hbody)
  | .conj ctx left right hleft hright =>
      .conj ctx.scope left right
        (Formula.WellFormed.toWellScoped hleft)
        (Formula.WellFormed.toWellScoped hright)
  | .disj ctx left right hleft hright =>
      .disj ctx.scope left right
        (Formula.WellFormed.toWellScoped hleft)
        (Formula.WellFormed.toWellScoped hright)
  | .allVar ctx profile body hbody =>
      .allVar ctx.scope profile body (by
        simpa only [TypingContext.scope_underVar] using
          Formula.WellFormed.toWellScoped hbody)
  | .existsVar ctx profile body hbody =>
      .existsVar ctx.scope profile body (by
        simpa only [TypingContext.scope_underVar] using
          Formula.WellFormed.toWellScoped hbody)
  | .allFun ctx profile body hbody =>
      .allFun ctx.scope profile body (by
        simpa only [TypingContext.scope_underFun] using
          Formula.WellFormed.toWellScoped hbody)
  | .existsFun ctx profile body hbody =>
      .existsFun ctx.scope profile body (by
        simpa only [TypingContext.scope_underFun] using
          Formula.WellFormed.toWellScoped hbody)

/-- Pointwise typing implies pointwise structural scope. -/
theorem VarietiesHaveTypes.toWellScoped
    {ctx : TypingContext} {args : List Variety} {profiles : List TypeProfile}
    (h : VarietiesHaveTypes ctx args profiles) :
    VarietiesWellScoped ctx.scope args :=
  match h with
  | .nil ctx => .nil ctx.scope
  | .cons ctx head _ tail _ hhead htail =>
      .cons ctx.scope head tail
        (Variety.HasType.toWellScoped hhead)
        (VarietiesHaveTypes.toWellScoped htail)

end

/-- A well-typed functional is structurally well scoped. -/
theorem Functional.HasType.toWellScoped
    {ctx : TypingContext} {functional : Functional} {profile : TypeProfile}
    (h : Functional.HasType ctx functional profile) :
    Functional.WellScoped ctx.scope functional := by
  cases h with
  | abstract headLevel tailLevels body hbody =>
      exact .abstract ctx.scope headLevel tailLevels body (by
        simpa only [TypingContext.scope_underBlock] using
          Variety.HasType.toWellScoped hbody)

/-- Existential variety typing also implies well-scopedness. -/
theorem Variety.WellTyped.toWellScoped
    {ctx : TypingContext} {variety : Variety}
    (h : Variety.WellTyped ctx variety) :
    Variety.WellScoped ctx.scope variety := by
  obtain ⟨_, htype⟩ := h
  exact htype.toWellScoped

/-- The §2.10 term condition implies structural well-scopedness. -/
theorem Variety.IsTerm.toWellScoped
    {ctx : TypingContext} {variety : Variety}
    (h : Variety.IsTerm ctx variety) :
    Variety.WellScoped ctx.scope variety :=
  Variety.HasType.toWellScoped h

/-- A well-formed functional is structurally well scoped. -/
theorem Functional.WellFormed.toWellScoped
    {ctx : TypingContext} {functional : Functional}
    (h : Functional.WellFormed ctx functional) :
    Functional.WellScoped ctx.scope functional :=
  Functional.HasType.toWellScoped h

end TakeutiGLC
