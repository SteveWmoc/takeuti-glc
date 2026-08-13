import TakeutiGLC.Syntax.Symbol

/-!
# Kind-free names for binding experiments

The historical symbol layer records Takeuti's distinction among free, bound,
and special symbols. The binding experiments should not carry that classification
inside named occurrences: the occurrence constructor itself determines whether a
name is free or special, while bound occurrences are represented only by de
Bruijn indices.

These structures therefore retain only the source-level profile and opaque name
index needed by the experiments.
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
