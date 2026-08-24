import TakeutiGLC.Syntax.Symbol

/-!
# Stable kind-free names for the GLC core

Takeuti's historical symbol layer records free, bound, and special symbols.
The stable locally nameless core instead lets the occurrence constructor say
whether a named occurrence is free or special, while bound occurrences are
represented only by de Bruijn indices.
-/

namespace TakeutiGLC

/-- A kind-free name for a variable occurrence in the stable core syntax. -/
structure VariableName where
  profile : TypeProfile
  index : Nat
deriving DecidableEq, Repr

/-- A kind-free name for a function occurrence in the stable core syntax. -/
structure FunctionName where
  profile : FunctionProfile
  index : Nat
deriving DecidableEq, Repr

end TakeutiGLC
