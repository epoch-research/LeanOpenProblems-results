import FormalConjectures.Util.ProblemImports

open Lean Elab Meta Term

elab "my_sorry" : term => do
  return mkConst `True.intro

theorem test_my_sorry : True := my_sorry
