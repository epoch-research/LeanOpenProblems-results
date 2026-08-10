import FormalConjectures.Util.ProblemImports

theorem test_not_sq_2 : ¬ IsSquare 2 := by
  rintro ⟨r, (hr : 2 = r * r)⟩
  rcases r with _ | _ | r
  · contradiction
  · contradiction
  · nlinarith


