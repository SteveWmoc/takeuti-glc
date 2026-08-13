import TakeutiGLC.Syntax.Symbol

/-!
# Binding experiment: intrinsically scoped de Bruijn syntax

This file is an executable Milestone 1 prototype. It isolates the binding
problem in Takeuti's §§2.6, 2.8, 2.9, and 3.2 without yet committing the project
to a final syntax representation.

The two binding classes are tracked by separate natural-number context depths.
Bound variable occurrences use `Fin varDepth`; bound function occurrences use
`Fin funDepth`. Thus dangling bound references are unrepresentable.

Typing is deliberately only partially intrinsic in this experiment. Binder
profiles are recorded, but the constructors do not yet prove that every
application has the argument types required by Takeuti's formation rules. The
point of this file is to test scoping and binder ergonomics before the stable
syntax API is chosen.
-/

namespace TakeutiGLC.Experiment.DeBruijn

/-- Number of variables bound by a nonempty Takeuti abstraction block. -/
def blockSize (tailLevels : List Nat) : Nat := tailLevels.length + 1

/-- Resulting Takeuti type of an abstraction block with predecessor levels. -/
def abstractionProfile (headLevel : Nat) (tailLevels : List Nat) : TypeProfile :=
  .higher headLevel tailLevels

mutual

/--
A scope-indexed prototype of Takeuti varieties.

The two natural numbers are *indices* of the inductive family, rather than
uniform parameters. This is essential: a binder constructor must be able to
store a body at a larger scope depth than the expression it constructs.

Free and special source symbols keep the opaque names from `Symbol.lean`;
bound source names disappear and are represented by de Bruijn indices.
-/
inductive Variety : Nat → Nat → Type where
  | freeVar {varDepth funDepth : Nat}
      (symbol : VariableSymbol) : Variety varDepth funDepth
  | specialVar {varDepth funDepth : Nat}
      (symbol : VariableSymbol) : Variety varDepth funDepth
  | boundVar {varDepth funDepth : Nat}
      (index : Fin varDepth) : Variety varDepth funDepth
  | freeFunApp {varDepth funDepth : Nat}
      (symbol : FunctionSymbol)
      (args : List (Variety varDepth funDepth)) : Variety varDepth funDepth
  | specialFunApp {varDepth funDepth : Nat}
      (symbol : FunctionSymbol)
      (args : List (Variety varDepth funDepth)) : Variety varDepth funDepth
  | boundFunApp {varDepth funDepth : Nat}
      (index : Fin funDepth)
      (args : List (Variety varDepth funDepth)) : Variety varDepth funDepth
  | abstract {varDepth funDepth : Nat}
      (headLevel : Nat)
      (tailLevels : List Nat)
      (body : Formula (blockSize tailLevels + varDepth) funDepth) :
      Variety varDepth funDepth

/--
A scope-indexed prototype of Takeuti formulas.

Variable and function quantifiers extend different context depths. This makes
Takeuti's two syntactically distinct binder families explicit in the type.
-/
inductive Formula : Nat → Nat → Type where
  | atomFree {varDepth funDepth : Nat}
      (symbol : VariableSymbol)
      (args : List (Variety varDepth funDepth)) : Formula varDepth funDepth
  | atomSpecial {varDepth funDepth : Nat}
      (symbol : VariableSymbol)
      (args : List (Variety varDepth funDepth)) : Formula varDepth funDepth
  | atomBound {varDepth funDepth : Nat}
      (index : Fin varDepth)
      (args : List (Variety varDepth funDepth)) : Formula varDepth funDepth
  | neg {varDepth funDepth : Nat}
      (body : Formula varDepth funDepth) : Formula varDepth funDepth
  | conj {varDepth funDepth : Nat}
      (left right : Formula varDepth funDepth) : Formula varDepth funDepth
  | disj {varDepth funDepth : Nat}
      (left right : Formula varDepth funDepth) : Formula varDepth funDepth
  | allVar {varDepth funDepth : Nat}
      (profile : TypeProfile)
      (body : Formula (Nat.succ varDepth) funDepth) : Formula varDepth funDepth
  | existsVar {varDepth funDepth : Nat}
      (profile : TypeProfile)
      (body : Formula (Nat.succ varDepth) funDepth) : Formula varDepth funDepth
  | allFun {varDepth funDepth : Nat}
      (profile : FunctionProfile)
      (body : Formula varDepth (Nat.succ funDepth)) : Formula varDepth funDepth
  | existsFun {varDepth funDepth : Nat}
      (profile : FunctionProfile)
      (body : Formula varDepth (Nat.succ funDepth)) : Formula varDepth funDepth

end

/--
A prototype functional. As in §3.2, a nonempty block of variable binders scopes
over a variety intended eventually to be checked as a term.
-/
inductive Functional : Nat → Nat → Type where
  | abstract {varDepth funDepth : Nat}
      (headLevel : Nat)
      (tailLevels : List Nat)
      (body : Variety (blockSize tailLevels + varDepth) funDepth) :
      Functional varDepth funDepth

@[simp] theorem blockSize_pos (tailLevels : List Nat) : 0 < blockSize tailLevels := by
  simp [blockSize]

/-- There is no bound variable reference in an empty variable context. -/
theorem noBoundVariableAtDepthZero (index : Fin 0) : False :=
  Fin.elim0 index

/-- There is no bound function reference in an empty function context. -/
theorem noBoundFunctionAtDepthZero (index : Fin 0) : False :=
  Fin.elim0 index

end TakeutiGLC.Experiment.DeBruijn
