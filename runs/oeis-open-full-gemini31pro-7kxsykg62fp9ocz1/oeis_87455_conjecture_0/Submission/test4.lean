import FormalConjectures.Util.ProblemImports

open LinearRecurrence

def A087455 (n : ℕ) : ℤ :=
  let order : ℕ := 2
  let coeffs : Fin order → ℤ := fun i => Fin.cases (-3) 2 i
  let E : LinearRecurrence ℤ := ⟨order, coeffs⟩
  let init : Fin order → ℤ := fun i => Fin.cases 1 1 i
  E.mkSol init n

#eval A087455 7
#eval A087455 8
#eval A087455 9
#eval A087455 10
#eval A087455 11
#eval A087455 12
#eval A087455 13
#eval A087455 14
#eval A087455 15
