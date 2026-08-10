import FormalConjectures.Util.ProblemImports
open Sat
lrat_proof lrat_ok
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"
#check lrat_ok
#print axioms lrat_ok
-- try invalid: prove not a from satisfiable CNF a?
lrat_proof lrat_bad
  "p cnf 1 1  1 0"
  "2 0 1 0"
#check lrat_bad
#print axioms lrat_bad
