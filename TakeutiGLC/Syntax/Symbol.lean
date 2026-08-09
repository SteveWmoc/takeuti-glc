import TakeutiGLC.Syntax.TypeProfile

/-!
# Symbol classes for Takeuti's GLC

This file gives a deliberately thin representation of the symbol classes from
§1 of Takeuti's 1953 paper. It records the historical distinctions among free,
bound, and special variables and functions, together with the five logical
symbols used by the calculus.

No binding representation is chosen here. In particular, the `index` fields are
only opaque names for source-level symbols; they are not de Bruijn indices.
-/

namespace TakeutiGLC

/-- The three classes of variables distinguished in §1.1. -/
inductive VariableKind where
  | free
  | bound
  | special
deriving DecidableEq, Repr

/-- The three classes of functions distinguished in §1.2. -/
inductive FunctionKind where
  | free
  | bound
  | special
deriving DecidableEq, Repr

/-- The logical symbols listed in §1.3. -/
inductive LogicalSymbol where
  | neg
  | conj
  | disj
  | all
  | exists
deriving DecidableEq, Repr

/--
A source-level variable symbol.

Variables may have Takeuti's distinguished type `(0)` or any nonzero type
profile. The natural number is only a supply of distinct names for this
prototype.
-/
structure VariableSymbol where
  kind : VariableKind
  profile : TypeProfile
  index : Nat
deriving DecidableEq, Repr

/--
A nonzero type profile suitable for one of Takeuti's function symbols.

Section 1.2 lists functions only at types `(n₁, ..., nᵢ)` with every displayed
entry positive. We therefore store the predecessor levels directly, in the same
shifted form used by `TypeProfile.higher`.
-/
structure FunctionProfile where
  head : Nat
  tail : List Nat
deriving DecidableEq, Repr

namespace FunctionProfile

/-- Regard a function profile as the corresponding general type profile. -/
def toTypeProfile (profile : FunctionProfile) : TypeProfile :=
  .higher profile.head profile.tail

/-- The argument types accepted by a function of this profile. -/
def argumentTypes (profile : FunctionProfile) : List TypeProfile :=
  profile.toTypeProfile.argumentTypes

/-- The number of argument places of a function of this profile. -/
def arity (profile : FunctionProfile) : Nat :=
  profile.toTypeProfile.arity

@[simp] theorem toTypeProfile_mk (head : Nat) (tail : List Nat) :
    toTypeProfile ⟨head, tail⟩ = .higher head tail := rfl

@[simp] theorem arity_pos (profile : FunctionProfile) : 0 < profile.arity := by
  cases profile with
  | mk head tail => simp [arity, toTypeProfile]

end FunctionProfile

/--
A source-level function symbol.

The natural number is an opaque name. It deliberately carries no binding
semantics; that decision belongs to the later binding prototypes of Milestone 1.
-/
structure FunctionSymbol where
  kind : FunctionKind
  profile : FunctionProfile
  index : Nat
deriving DecidableEq, Repr

/--
A Takeuti predicate profile: a nonzero variable type whose displayed entries
are all `1`, equivalently whose stored predecessor levels are all `0`.
-/
def TypeProfile.IsPredicate : TypeProfile → Prop
  | .zero => False
  | .higher head tail => head = 0 ∧ ∀ n ∈ tail, n = 0

/-- A special variable is a predicate exactly when its profile is predicate-shaped. -/
def VariableSymbol.IsPredicate (symbol : VariableSymbol) : Prop :=
  symbol.kind = .special ∧ symbol.profile.IsPredicate

end TakeutiGLC
