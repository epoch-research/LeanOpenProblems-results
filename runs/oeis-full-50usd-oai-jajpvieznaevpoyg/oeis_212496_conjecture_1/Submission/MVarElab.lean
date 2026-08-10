import FormalConjectures.Util.ProblemImports
import Lean
open Lean Elab Term Meta
syntax (name := holeTermSyntax) "holeTerm" : term
@[term_elab holeTermSyntax] def elabHole : TermElab := fun _ expected? => do
  let some ty := expected? | throwError "no expected"
  let m ← mkFreshExprMVar ty
  return m
example : False := holeTerm
#print axioms _example
