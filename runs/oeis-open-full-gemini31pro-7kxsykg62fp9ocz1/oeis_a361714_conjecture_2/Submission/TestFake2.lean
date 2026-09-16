import FormalConjectures.Util.ProblemImports

theorem falso : False := by
  have h : (fun _ => 0) = (fun _ => 1) := funext (fun _ => rfl)
  sorry
