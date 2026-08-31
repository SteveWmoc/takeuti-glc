import TakeutiGLC.Syntax.Scope

/-!
# Extrinsic typing for the stable GLC syntax

This file implements the type-formation layer planned for Milestone 2. Raw
syntax remains locally nameless and untyped; these judgments enforce the type
profiles and argument compatibility required by Takeuti's §§2–3 formation
rules.

Variable and function binders have independent typing contexts, matching the
independent de Bruijn namespaces already used by the raw syntax. An abstraction
block extends the variable context by all of its slots at once, with the first
displayed binder at de Bruijn index `0`.

This module deliberately separates **typing** from the remaining source-level
occurrence side conditions. In §§2.8–2.9 Takeuti quantifies a free variable or
function that occurs in the premiss formula; recognizing that non-vacuity
condition requires the occurrence machinery scheduled next in Milestone 2.
Thus `Formula.WellFormed` below is the typed core judgment, not yet a complete
recognizer for source figures.
-/

namespace TakeutiGLC

/-- Types of the variables bound by one nonempty Takeuti abstraction block. -/
def abstractionBinderTypes (headLevel : Nat) (tailLevels : List Nat) : List TypeProfile :=
  (headLevel :: tailLevels).map TypeProfile.monotype

/-- Independent de Bruijn typing contexts for bound variables and functions. -/
structure TypingContext where
  variableTypes : List TypeProfile
  functionProfiles : List FunctionProfile
deriving DecidableEq, Repr

namespace TypingContext

/-- The empty typing context. -/
def empty : TypingContext := ⟨[], []⟩

/-- Look up the type of a bound variable at a de Bruijn index. -/
def variableAt (ctx : TypingContext) (index : Nat) : Option TypeProfile :=
  ctx.variableTypes.get? index

/-- Look up the profile of a bound function at a de Bruijn index. -/
def functionAt (ctx : TypingContext) (index : Nat) : Option FunctionProfile :=
  ctx.functionProfiles.get? index

/-- Enter one variable quantifier. The new binder occupies index `0`. -/
def underVar (ctx : TypingContext) (profile : TypeProfile) : TypingContext :=
  { ctx with variableTypes := profile :: ctx.variableTypes }

/-- Enter one function quantifier. The new binder occupies index `0`. -/
def underFun (ctx : TypingContext) (profile : FunctionProfile) : TypingContext :=
  { ctx with functionProfiles := profile :: ctx.functionProfiles }

/--
Enter one simultaneous variable-abstraction block.

The block is prepended in display order, so the first displayed binder has
index `0`, the second has index `1`, and so on.
-/
def underBlock (ctx : TypingContext) (headLevel : Nat) (tailLevels : List Nat) :
    TypingContext :=
  { ctx with
    variableTypes := abstractionBinderTypes headLevel tailLevels ++ ctx.variableTypes }

/-- Forget typing information and retain only the two structural scope depths. -/
def scope (ctx : TypingContext) : Scope :=
  ⟨ctx.variableTypes.length, ctx.functionProfiles.length⟩

@[simp] theorem variableAt_underVar_zero (ctx : TypingContext) (profile : TypeProfile) :
    (ctx.underVar profile).variableAt 0 = some profile := rfl

@[simp] theorem functionAt_underFun_zero (ctx : TypingContext) (profile : FunctionProfile) :
    (ctx.underFun profile).functionAt 0 = some profile := rfl

@[simp] theorem variableAt_underBlock_zero (ctx : TypingContext) (headLevel : Nat)
    (tailLevels : List Nat) :
    (ctx.underBlock headLevel tailLevels).variableAt 0 =
      some (TypeProfile.monotype headLevel) := by
  simp [underBlock, variableAt, abstractionBinderTypes]

end TypingContext

mutual

/-- A raw variety has the indicated Takeuti type in a typing context. -/
inductive Variety.HasType : TypingContext → Variety → TypeProfile → Prop where
  | freeVar (ctx : TypingContext) (name : VariableName)
      (hprofile : name.profile = .zero) :
      Variety.HasType ctx (.freeVar name) .zero
  | specialVar (ctx : TypingContext) (name : VariableName)
      (hprofile : name.profile = .zero) :
      Variety.HasType ctx (.specialVar name) .zero
  | boundVar (ctx : TypingContext) (index : Nat)
      (hlookup : ctx.variableAt index = some .zero) :
      Variety.HasType ctx (.boundVar index) .zero
  | freeFunApp (ctx : TypingContext) (name : FunctionName) (args : List Variety)
      (hargs : VarietiesHaveTypes ctx args name.profile.argumentTypes) :
      Variety.HasType ctx (.freeFunApp name args) .zero
  | specialFunApp (ctx : TypingContext) (name : FunctionName) (args : List Variety)
      (hargs : VarietiesHaveTypes ctx args name.profile.argumentTypes) :
      Variety.HasType ctx (.specialFunApp name args) .zero
  | boundFunApp (ctx : TypingContext) (index : Nat) (profile : FunctionProfile)
      (args : List Variety)
      (hlookup : ctx.functionAt index = some profile)
      (hargs : VarietiesHaveTypes ctx args profile.argumentTypes) :
      Variety.HasType ctx (.boundFunApp index args) .zero
  | abstract (ctx : TypingContext) (headLevel : Nat) (tailLevels : List Nat)
      (body : Formula)
      (hbody : Formula.WellFormed (ctx.underBlock headLevel tailLevels) body) :
      Variety.HasType ctx (.abstract headLevel tailLevels body)
        (abstractionProfile headLevel tailLevels)

/-- A raw formula satisfies Takeuti's type-formation conditions in a context. -/
inductive Formula.WellFormed : TypingContext → Formula → Prop where
  | atomFree (ctx : TypingContext) (name : VariableName) (args : List Variety)
      (hnonzero : name.profile ≠ .zero)
      (hargs : VarietiesHaveTypes ctx args name.profile.argumentTypes) :
      Formula.WellFormed ctx (.atomFree name args)
  | atomSpecial (ctx : TypingContext) (name : VariableName) (args : List Variety)
      (hnonzero : name.profile ≠ .zero)
      (hargs : VarietiesHaveTypes ctx args name.profile.argumentTypes) :
      Formula.WellFormed ctx (.atomSpecial name args)
  | atomBound (ctx : TypingContext) (index : Nat) (profile : TypeProfile)
      (args : List Variety)
      (hlookup : ctx.variableAt index = some profile)
      (hnonzero : profile ≠ .zero)
      (hargs : VarietiesHaveTypes ctx args profile.argumentTypes) :
      Formula.WellFormed ctx (.atomBound index args)
  | neg (ctx : TypingContext) (body : Formula)
      (hbody : Formula.WellFormed ctx body) :
      Formula.WellFormed ctx (.neg body)
  | conj (ctx : TypingContext) (left right : Formula)
      (hleft : Formula.WellFormed ctx left)
      (hright : Formula.WellFormed ctx right) :
      Formula.WellFormed ctx (.conj left right)
  | disj (ctx : TypingContext) (left right : Formula)
      (hleft : Formula.WellFormed ctx left)
      (hright : Formula.WellFormed ctx right) :
      Formula.WellFormed ctx (.disj left right)
  | allVar (ctx : TypingContext) (profile : TypeProfile) (body : Formula)
      (hbody : Formula.WellFormed (ctx.underVar profile) body) :
      Formula.WellFormed ctx (.allVar profile body)
  | existsVar (ctx : TypingContext) (profile : TypeProfile) (body : Formula)
      (hbody : Formula.WellFormed (ctx.underVar profile) body) :
      Formula.WellFormed ctx (.existsVar profile body)
  | allFun (ctx : TypingContext) (profile : FunctionProfile) (body : Formula)
      (hbody : Formula.WellFormed (ctx.underFun profile) body) :
      Formula.WellFormed ctx (.allFun profile body)
  | existsFun (ctx : TypingContext) (profile : FunctionProfile) (body : Formula)
      (hbody : Formula.WellFormed (ctx.underFun profile) body) :
      Formula.WellFormed ctx (.existsFun profile body)

/-- Pointwise typing for a list of variety arguments. -/
inductive VarietiesHaveTypes : TypingContext → List Variety → List TypeProfile → Prop where
  | nil (ctx : TypingContext) :
      VarietiesHaveTypes ctx [] []
  | cons (ctx : TypingContext) (head : Variety) (headType : TypeProfile)
      (tail : List Variety) (tailTypes : List TypeProfile)
      (hhead : Variety.HasType ctx head headType)
      (htail : VarietiesHaveTypes ctx tail tailTypes) :
      VarietiesHaveTypes ctx (head :: tail) (headType :: tailTypes)

end

/-- A functional has its indicated higher type in a typing context. -/
inductive Functional.HasType : TypingContext → Functional → TypeProfile → Prop where
  | abstract (ctx : TypingContext) (headLevel : Nat) (tailLevels : List Nat)
      (body : Variety)
      (hbody : Variety.HasType (ctx.underBlock headLevel tailLevels) body .zero) :
      Functional.HasType ctx (.abstract headLevel tailLevels body)
        (abstractionProfile headLevel tailLevels)

/-- A typed variety is a term exactly when it has Takeuti's distinguished type `(0)`. -/
def Variety.IsTerm (ctx : TypingContext) (variety : Variety) : Prop :=
  Variety.HasType ctx variety .zero

/-- A raw variety is well typed when it has some Takeuti type. -/
def Variety.WellTyped (ctx : TypingContext) (variety : Variety) : Prop :=
  ∃ profile, Variety.HasType ctx variety profile

/-- A functional is well formed when it has the profile stored by its abstraction node. -/
def Functional.WellFormed (ctx : TypingContext) (functional : Functional) : Prop :=
  Functional.HasType ctx functional functional.profile

end TakeutiGLC
