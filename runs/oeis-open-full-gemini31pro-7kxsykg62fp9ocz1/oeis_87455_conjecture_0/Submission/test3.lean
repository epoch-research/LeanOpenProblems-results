import FormalConjectures.Util.ProblemImports

open LinearRecurrence

def A087455 (n : ℕ) : ℤ :=
  let order : ℕ := 2
  let coeffs : Fin order → ℤ := fun i => Fin.cases (-3) 2 i
  let E : LinearRecurrence ℤ := ⟨order, coeffs⟩
  let init : Fin order → ℤ := fun i => Fin.cases 1 1 i
  E.mkSol init n

#eval A087455 0
#eval A087455 1
#eval A087455 2
#eval A087455 3
#eval A087455 4
#eval A087455 5
#eval A087455 6
