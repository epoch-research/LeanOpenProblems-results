import FormalConjectures.Util.ProblemImports
import Lean
open Lean Elab Term
syntax (name := badtermSyntax) "badterm" : term
@[term_elab badtermSyntax] def elabBad : TermElab := fun _ _ => do
  return mkConst ``True.intro
example : False := badterm
#print axioms _example
