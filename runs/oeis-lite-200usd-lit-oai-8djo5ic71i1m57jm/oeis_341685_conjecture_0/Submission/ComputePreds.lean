import FormalConjectures.Util.ProblemImports
open Nat
#eval (List.range 101).filter IsPerfectPower
#eval (List.range 101).map (fun n => (n, n.squarefreePart, n.squarePart))
#eval (List.range 101).map (fun n => (n, n.maxPrimeFac))
#eval (List.range 51).filter Powerful
