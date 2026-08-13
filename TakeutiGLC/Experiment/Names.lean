import TakeutiGLC.Syntax.Symbol

/-!
# Kind-free names for syntax experiments

The historical symbol layer records Takeuti's distinction among free, bound,
and special symbols. The syntax experiments instead let the occurrence
constructor determine whether a source name is free or special, while bound
occurrences are represented only by indices.
-/

namespace TakeutiGLC.Experiment

/-- A kind-free source-level name for a variable occurrence. -/
structure VariableName where
  profile : TypeProfile
  index : Nat
deriving DecidableEq, Repr

/-- A kind-free source-level name for a function occurrence. -/
structure FunctionName where
  profile : FunctionProfile
  index : Nat
deriving DecidableEq, Repr

end TakeutiGLC.Experiment
