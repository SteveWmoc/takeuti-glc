import TakeutiGLC.Syntax.Instantiation

/-!
# Hereditary instantiation of variable blocks

Takeuti's clause 5.2.26 reduces a higher-type variable occurrence by applying
the body of a replacement abstraction to recursively transformed arguments.
For height one, every formal variable in that abstraction has type `(0)`, so
ordinary base-variable block instantiation is enough. At larger heights a
formal variable may itself occur as the head of an atomic formula.

This module implements the corresponding **hereditary** block instantiation.
A block slot is annotated by its Takeuti singleton level. Base slots are
replaced directly. When a positive-level slot occurs as an atomic head, its
replacement must be an abstraction of the same singleton type; that
abstraction is beta-reduced against the recursively instantiated argument.

The recursion is controlled by a fuel equal to the largest formal-variable
level. Every hereditary beta step lowers that level, while ordinary traversal
remains structural. This mirrors Takeuti's induction on substitution height
without introducing fresh source-level names.

As elsewhere in the stable syntax layer, the operation is intentionally
partial on malformed raw syntax. Well-typed source translations are expected
to avoid the failure cases.
-/

namespace TakeutiGLC

/--
A lower-level hereditary instantiator used by one structural traversal step.

The callback always starts at the outer edge of the replacement abstraction's
body. Any surrounding binders have already been incorporated by lifting the
replacement before its abstraction is opened.
-/
abbrev LowerVarBlockInstantiation :=
  List Nat → List Variety → Formula → Option Formula

mutual

/-- One structural hereditary-instantiation pass through a variety. -/
def Variety.instantiateVarBlockStep?
    (lower : LowerVarBlockInstantiation)
    (levels : List Nat) (replacements : List Variety)
    (varCutoff funCutoff : Nat) : Variety → Option Variety
  | .freeVar name => some (.freeVar name)
  | .specialVar name => some (.specialVar name)
  | .boundVar index =>
      if index < varCutoff then
        some (.boundVar index)
      else
        let relative := index - varCutoff
        match levels[relative]? with
        | none => some (.boundVar (index - levels.length))
        | some 0 =>
            match replacements[relative]? with
            | some replacement =>
                some (replacement.liftIntoScope varCutoff funCutoff)
            | none => none
        | some (Nat.succ _) => none
  | .freeFunApp name args => do
      let args' ← instantiateVarBlockStepArgs? lower levels replacements
        varCutoff funCutoff args
      some (.freeFunApp name args')
  | .specialFunApp name args => do
      let args' ← instantiateVarBlockStepArgs? lower levels replacements
        varCutoff funCutoff args
      some (.specialFunApp name args')
  | .boundFunApp index args => do
      let args' ← instantiateVarBlockStepArgs? lower levels replacements
        varCutoff funCutoff args
      some (.boundFunApp index args')
  | .abstract headLevel tailLevels body => do
      let body' ← Formula.instantiateVarBlockStep? lower levels replacements
        (varCutoff + blockSize tailLevels) funCutoff body
      some (.abstract headLevel tailLevels body')

/-- One structural hereditary-instantiation pass through a formula. -/
def Formula.instantiateVarBlockStep?
    (lower : LowerVarBlockInstantiation)
    (levels : List Nat) (replacements : List Variety)
    (varCutoff funCutoff : Nat) : Formula → Option Formula
  | .atomFree name args => do
      let args' ← instantiateVarBlockStepArgs? lower levels replacements
        varCutoff funCutoff args
      some (.atomFree name args')
  | .atomSpecial name args => do
      let args' ← instantiateVarBlockStepArgs? lower levels replacements
        varCutoff funCutoff args
      some (.atomSpecial name args')
  | .atomBound index args => do
      let args' ← instantiateVarBlockStepArgs? lower levels replacements
        varCutoff funCutoff args
      if index < varCutoff then
        some (.atomBound index args')
      else
        let relative := index - varCutoff
        match levels[relative]? with
        | none => some (.atomBound (index - levels.length) args')
        | some 0 => none
        | some (Nat.succ predecessor) =>
            match replacements[relative]? with
            | none => none
            | some replacement =>
                match replacement.liftIntoScope varCutoff funCutoff with
                | .abstract headLevel tailLevels replacementBody =>
                    if abstractionProfile headLevel tailLevels =
                        TypeProfile.monotype (Nat.succ predecessor) then
                      match args' with
                      | [arg] => lower [predecessor] [arg] replacementBody
                      | _ => none
                    else
                      none
                | _ => none
  | .neg body => do
      let body' ← Formula.instantiateVarBlockStep? lower levels replacements
        varCutoff funCutoff body
      some (.neg body')
  | .conj left right => do
      let left' ← Formula.instantiateVarBlockStep? lower levels replacements
        varCutoff funCutoff left
      let right' ← Formula.instantiateVarBlockStep? lower levels replacements
        varCutoff funCutoff right
      some (.conj left' right')
  | .disj left right => do
      let left' ← Formula.instantiateVarBlockStep? lower levels replacements
        varCutoff funCutoff left
      let right' ← Formula.instantiateVarBlockStep? lower levels replacements
        varCutoff funCutoff right
      some (.disj left' right')
  | .allVar profile body => do
      let body' ← Formula.instantiateVarBlockStep? lower levels replacements
        (varCutoff + 1) funCutoff body
      some (.allVar profile body')
  | .existsVar profile body => do
      let body' ← Formula.instantiateVarBlockStep? lower levels replacements
        (varCutoff + 1) funCutoff body
      some (.existsVar profile body')
  | .allFun profile body => do
      let body' ← Formula.instantiateVarBlockStep? lower levels replacements
        varCutoff (funCutoff + 1) body
      some (.allFun profile body')
  | .existsFun profile body => do
      let body' ← Formula.instantiateVarBlockStep? lower levels replacements
        varCutoff (funCutoff + 1) body
      some (.existsFun profile body')

/-- One structural hereditary-instantiation pass through an argument list. -/
def instantiateVarBlockStepArgs?
    (lower : LowerVarBlockInstantiation)
    (levels : List Nat) (replacements : List Variety)
    (varCutoff funCutoff : Nat) : List Variety → Option (List Variety)
  | [] => some []
  | arg :: args => do
      let arg' ← Variety.instantiateVarBlockStep? lower levels replacements
        varCutoff funCutoff arg
      let args' ← instantiateVarBlockStepArgs? lower levels replacements
        varCutoff funCutoff args
      some (arg' :: args')

end

namespace Formula

/--
Hereditary block instantiation with explicit height fuel.

At fuel zero, only base-type slots can be eliminated. At successor fuel, one
positive-level atomic-head reduction may invoke the lower-fuel instantiator.
-/
def hereditaryInstantiateVarBlockFuel? :
    Nat → List Nat → List Variety → Formula → Option Formula
  | 0, levels, replacements, body =>
      if levels.length = replacements.length then
        Formula.instantiateVarBlockStep? (fun _ _ _ => none)
          levels replacements 0 0 body
      else
        none
  | Nat.succ fuel, levels, replacements, body =>
      if levels.length = replacements.length then
        Formula.instantiateVarBlockStep?
          (Formula.hereditaryInstantiateVarBlockFuel? fuel)
          levels replacements 0 0 body
      else
        none

end Formula

/-- Largest singleton level occurring in a simultaneous abstraction block. -/
def maxBinderLevel (levels : List Nat) : Nat :=
  levels.foldl Nat.max 0

namespace Formula

/--
Instantiate a simultaneous variable block at arbitrary finite type height.

The driver supplies exactly the fuel needed by the largest formal-variable
level in the block.
-/
def hereditaryInstantiateVarBlock?
    (levels : List Nat) (replacements : List Variety) (body : Formula) :
    Option Formula :=
  Formula.hereditaryInstantiateVarBlockFuel? (maxBinderLevel levels)
    levels replacements body

end Formula

end TakeutiGLC
