import TakeutiGLC.Syntax.Renaming

/-!
# Instantiation of base-type variable blocks

Takeuti's higher-type complete substitution (§5.2.14–§5.2.35) eventually
reduces an occurrence of a higher-type variable to the body of a replacement
abstraction with its formal variables instantiated by actual arguments.

The first higher-type stage has height one, so every formal variable in the
replacement abstraction has type `(0)`. This module supplies the corresponding
locally nameless block-instantiation kernel.

A block of `n` variable binders occupies de Bruijn indices
`0, ..., n - 1`. Instantiating the block

* replaces those bound base-variable occurrences by the supplied varieties;
* contracts older variable indices by `n`;
* protects binders nested inside the body;
* weakens inserted replacements under nested variable and function binders.

The operation returns `none` if a removed base-type slot is used as the head
of an atomic formula. Such a figure is not well typed for a base-variable
block; keeping the raw operation partial makes that malformed case explicit.
-/

namespace TakeutiGLC

namespace Variety

/-- Lift a replacement from the surrounding context into a nested two-namespace scope. -/
def liftIntoScope (varDepth funDepth : Nat) (replacement : Variety) : Variety :=
  (replacement.weakenVarBy varDepth).weakenFunBy funDepth

end Variety

mutual

/--
Instantiate a simultaneous block of base-type variable binders in a variety.

`varCutoff` and `funCutoff` count binders crossed inside the body whose
scopes must also contain any inserted replacement.
-/
def Variety.instantiateBaseVarBlockAt?
    (replacements : List Variety) (varCutoff funCutoff : Nat) : Variety → Option Variety
  | .freeVar name => some (.freeVar name)
  | .specialVar name => some (.specialVar name)
  | .boundVar index =>
      if index < varCutoff then
        some (.boundVar index)
      else
        let relative := index - varCutoff
        match replacements[relative]? with
        | some replacement =>
            some (replacement.liftIntoScope varCutoff funCutoff)
        | none =>
            some (.boundVar (index - replacements.length))
  | .freeFunApp name args => do
      let args' ← instantiateBaseVarBlockArgsAt? replacements varCutoff funCutoff args
      some (.freeFunApp name args')
  | .specialFunApp name args => do
      let args' ← instantiateBaseVarBlockArgsAt? replacements varCutoff funCutoff args
      some (.specialFunApp name args')
  | .boundFunApp index args => do
      let args' ← instantiateBaseVarBlockArgsAt? replacements varCutoff funCutoff args
      some (.boundFunApp index args')
  | .abstract headLevel tailLevels body => do
      let body' ← Formula.instantiateBaseVarBlockAt? replacements
        (varCutoff + blockSize tailLevels) funCutoff body
      some (.abstract headLevel tailLevels body')

/-- Instantiate a simultaneous block of base-type variable binders in a formula. -/
def Formula.instantiateBaseVarBlockAt?
    (replacements : List Variety) (varCutoff funCutoff : Nat) : Formula → Option Formula
  | .atomFree name args => do
      let args' ← instantiateBaseVarBlockArgsAt? replacements varCutoff funCutoff args
      some (.atomFree name args')
  | .atomSpecial name args => do
      let args' ← instantiateBaseVarBlockArgsAt? replacements varCutoff funCutoff args
      some (.atomSpecial name args')
  | .atomBound index args =>
      if index < varCutoff then do
        let args' ← instantiateBaseVarBlockArgsAt? replacements varCutoff funCutoff args
        some (.atomBound index args')
      else
        let relative := index - varCutoff
        match replacements[relative]? with
        | some _ => none
        | none => do
            let args' ← instantiateBaseVarBlockArgsAt? replacements varCutoff funCutoff args
            some (.atomBound (index - replacements.length) args')
  | .neg body => do
      let body' ← Formula.instantiateBaseVarBlockAt? replacements varCutoff funCutoff body
      some (.neg body')
  | .conj left right => do
      let left' ← Formula.instantiateBaseVarBlockAt? replacements varCutoff funCutoff left
      let right' ← Formula.instantiateBaseVarBlockAt? replacements varCutoff funCutoff right
      some (.conj left' right')
  | .disj left right => do
      let left' ← Formula.instantiateBaseVarBlockAt? replacements varCutoff funCutoff left
      let right' ← Formula.instantiateBaseVarBlockAt? replacements varCutoff funCutoff right
      some (.disj left' right')
  | .allVar profile body => do
      let body' ← Formula.instantiateBaseVarBlockAt? replacements (varCutoff + 1) funCutoff body
      some (.allVar profile body')
  | .existsVar profile body => do
      let body' ← Formula.instantiateBaseVarBlockAt? replacements (varCutoff + 1) funCutoff body
      some (.existsVar profile body')
  | .allFun profile body => do
      let body' ← Formula.instantiateBaseVarBlockAt? replacements varCutoff (funCutoff + 1) body
      some (.allFun profile body')
  | .existsFun profile body => do
      let body' ← Formula.instantiateBaseVarBlockAt? replacements varCutoff (funCutoff + 1) body
      some (.existsFun profile body')

/-- Instantiate a base-variable block recursively through an argument list. -/
def instantiateBaseVarBlockArgsAt?
    (replacements : List Variety) (varCutoff funCutoff : Nat) :
    List Variety → Option (List Variety)
  | [] => some []
  | arg :: args => do
      let arg' ← Variety.instantiateBaseVarBlockAt? replacements varCutoff funCutoff arg
      let args' ← instantiateBaseVarBlockArgsAt? replacements varCutoff funCutoff args
      some (arg' :: args')

end

namespace Variety

/-- Instantiate the outermost simultaneous block of base-type variable binders. -/
def instantiateBaseVarBlock?
    (replacements : List Variety) (body : Variety) : Option Variety :=
  body.instantiateBaseVarBlockAt? replacements 0 0

end Variety

namespace Formula

/-- Instantiate the outermost simultaneous block of base-type variable binders. -/
def instantiateBaseVarBlock?
    (replacements : List Variety) (body : Formula) : Option Formula :=
  body.instantiateBaseVarBlockAt? replacements 0 0

end Formula

end TakeutiGLC
