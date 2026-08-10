import FormalConjectures.Util.ProblemImports
open Int.Linear
#eval (List.range 11).map (fun n => let k : ℤ := n - 5; (k, (Poly.num k).isUnsatEq, (Poly.num k).isUnsatDiseq_k, (Poly.num k).isUnsatLe))
#eval (List.range 11).map (fun n => let k : ℤ := n - 5; (k, eq_unsat_coeff_cert (Poly.num k) 1, eq_unsat_coeff_cert (Poly.num k) 0))
