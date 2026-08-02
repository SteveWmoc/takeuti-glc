import Mathlib.Data.List.Basic

/-!
# Takeuti type profiles

This file introduces a deliberately small representation of the finite type
profiles that occur in Takeuti's notation. It is only a starting point: the
final intrinsically scoped syntax may refine or replace this representation.
-/

namespace TakeutiGLC

/--
A raw finite profile `(n₁, ..., nᵢ)` in Takeuti's type notation.

The distinguished type `(0)` is represented by the singleton profile `[0]`.
Well-formedness conditions for higher profiles will be stated separately once
the syntax design is fixed.
-/
structure TypeProfile where
  entries : List Nat
deriving DecidableEq, Repr

namespace TypeProfile

/-- Takeuti's distinguished type `(0)`. -/
def zero : TypeProfile := ⟨[0]⟩

/-- The largest numerical level appearing in a raw type profile. -/
def height (profile : TypeProfile) : Nat :=
  profile.entries.foldl Nat.max 0

@[simp] theorem entries_zero : zero.entries = [0] := rfl

@[simp] theorem height_zero : height zero = 0 := by
  simp [height, zero]

end TypeProfile

end TakeutiGLC
