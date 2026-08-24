import TakeutiGLC.Syntax.Name

/-!
# Stable locally nameless core syntax for Takeuti's GLC

Milestone 1 selected a locally nameless representation with independent de
Bruijn namespaces for bound variables and bound functions. This file promotes
that representation out of `TakeutiGLC.Experiment` and defines the permanent
raw syntax categories.

Typing and scope correctness are intentionally extrinsic. In particular, raw
natural-number indices may be dangling; `TakeutiGLC.Syntax.Scope` supplies the
structural well-scopedness layer.
-/

namespace TakeutiGLC

/-- Number of variable slots bound by a nonempty Takeuti abstraction block. -/
def blockSize (tailLevels : List Nat) : Nat :=
  tailLevels.length + 1

/-- The type profile produced by a Takeuti abstraction block. -/
def abstractionProfile (headLevel : Nat) (tailLevels : List Nat) : TypeProfile :=
  .higher headLevel tailLevels

mutual

/--
A raw Takeuti variety.

Free and special occurrences retain names. Bound variable and function
occurrences use separate natural-number de Bruijn namespaces.
-/
inductive Variety where
  | freeVar (name : VariableName)
  | specialVar (name : VariableName)
  | boundVar (index : Nat)
  | freeFunApp (name : FunctionName) (args : List Variety)
  | specialFunApp (name : FunctionName) (args : List Variety)
  | boundFunApp (index : Nat) (args : List Variety)
  | abstract (headLevel : Nat) (tailLevels : List Nat) (body : Formula)

/-- A raw Takeuti formula. -/
inductive Formula where
  | atomFree (name : VariableName) (args : List Variety)
  | atomSpecial (name : VariableName) (args : List Variety)
  | atomBound (index : Nat) (args : List Variety)
  | neg (body : Formula)
  | conj (left right : Formula)
  | disj (left right : Formula)
  | allVar (profile : TypeProfile) (body : Formula)
  | existsVar (profile : TypeProfile) (body : Formula)
  | allFun (profile : FunctionProfile) (body : Formula)
  | existsFun (profile : FunctionProfile) (body : Formula)

end

/--
A raw Takeuti functional (§3.2).

Its body is a variety; the later typing judgment will require that body to have
type `(0)`. The abstraction block is structurally nonempty.
-/
inductive Functional where
  | abstract (headLevel : Nat) (tailLevels : List Nat) (body : Variety)

namespace Variety

/-- The profile attached to a higher-type abstraction node. -/
def abstractProfile : Variety → Option TypeProfile
  | .abstract headLevel tailLevels _ => some (abstractionProfile headLevel tailLevels)
  | _ => none

end Variety

namespace Functional

/-- The profile attached to a functional abstraction node. -/
def profile : Functional → TypeProfile
  | .abstract headLevel tailLevels _ => abstractionProfile headLevel tailLevels

end Functional

end TakeutiGLC
