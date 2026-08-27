import Mathlib.Data.List.Basic

/-!
# Takeuti type profiles

This file implements the shifted type-profile representation selected during
Milestone 1. It records the type notation used in §§1–3 of Takeuti's 1953
paper and is part of the stable syntax layer.
-/

namespace TakeutiGLC

/--
A type profile in Takeuti's historical notation.

* `zero` represents the distinguished type `(0)`.
* `higher head tail` represents the nonzero profile
  `(head + 1, tail₁ + 1, ..., tailᵢ + 1)`.

Thus the entries stored by `higher` are the predecessor levels of the
arguments accepted by a symbol of that type. This shifted representation makes
nonzero profiles nonempty and prevents zero from occurring among their
displayed entries.
-/
inductive TypeProfile where
  | zero
  | higher (head : Nat) (tail : List Nat)
deriving DecidableEq, Repr

namespace TypeProfile

/-- The singleton type `(n)` in Takeuti's notation. -/
def monotype : Nat → TypeProfile
  | 0 => .zero
  | Nat.succ n => .higher n []

/-- The numerical entries as Takeuti writes them. -/
def displayedEntries : TypeProfile → List Nat
  | .zero => [0]
  | .higher head tail => (head + 1) :: tail.map (fun n => n + 1)

/--
The predecessor levels required in the argument places of a nonzero profile.
The base type `(0)` has no argument places.
-/
def argumentLevels : TypeProfile → List Nat
  | .zero => []
  | .higher head tail => head :: tail

/-- The singleton types required in the argument places of a profile. -/
def argumentTypes (profile : TypeProfile) : List TypeProfile :=
  profile.argumentLevels.map monotype

/-- The number of argument places of a type profile. -/
def arity : TypeProfile → Nat
  | .zero => 0
  | .higher _ tail => tail.length + 1

/--
The height of a profile: the largest displayed numerical entry.

For a nonzero profile, the maximum predecessor level is computed first and
then shifted back up by one.
-/
def height : TypeProfile → Nat
  | .zero => 0
  | .higher head tail => (head :: tail).foldl Nat.max 0 + 1

@[simp] theorem monotype_zero : monotype 0 = .zero := rfl

@[simp] theorem monotype_succ (n : Nat) : monotype (Nat.succ n) = .higher n [] := rfl

@[simp] theorem displayedEntries_zero : displayedEntries .zero = [0] := rfl

@[simp] theorem displayedEntries_higher (head : Nat) (tail : List Nat) :
    displayedEntries (.higher head tail) =
      (head + 1) :: tail.map (fun n => n + 1) := rfl

@[simp] theorem argumentLevels_zero : argumentLevels .zero = [] := rfl

@[simp] theorem argumentLevels_higher (head : Nat) (tail : List Nat) :
    argumentLevels (.higher head tail) = head :: tail := rfl

@[simp] theorem argumentTypes_zero : argumentTypes .zero = [] := rfl

@[simp] theorem argumentTypes_higher (head : Nat) (tail : List Nat) :
    argumentTypes (.higher head tail) = (head :: tail).map monotype := rfl

@[simp] theorem arity_zero : arity .zero = 0 := rfl

@[simp] theorem arity_higher (head : Nat) (tail : List Nat) :
    arity (.higher head tail) = tail.length + 1 := rfl

@[simp] theorem height_zero : height .zero = 0 := rfl

@[simp] theorem height_higher (head : Nat) (tail : List Nat) :
    height (.higher head tail) = (head :: tail).foldl Nat.max 0 + 1 := rfl

@[simp] theorem displayedEntries_monotype (n : Nat) :
    displayedEntries (monotype n) = [n] := by
  cases n <;> rfl

@[simp] theorem argumentLevels_monotype_succ (n : Nat) :
    argumentLevels (monotype (Nat.succ n)) = [n] := rfl

@[simp] theorem argumentTypes_monotype_succ (n : Nat) :
    argumentTypes (monotype (Nat.succ n)) = [monotype n] := rfl

@[simp] theorem arity_monotype_succ (n : Nat) :
    arity (monotype (Nat.succ n)) = 1 := rfl

@[simp] theorem height_monotype (n : Nat) : height (monotype n) = n := by
  cases n with
  | zero => rfl
  | succ n => simp [height]

theorem displayedEntries_ne_nil (profile : TypeProfile) :
    displayedEntries profile ≠ [] := by
  cases profile <;> simp

theorem arity_higher_pos (head : Nat) (tail : List Nat) :
    0 < arity (.higher head tail) := by
  simp

theorem height_higher_pos (head : Nat) (tail : List Nat) :
    0 < height (.higher head tail) := by
  simp

end TypeProfile

end TakeutiGLC
