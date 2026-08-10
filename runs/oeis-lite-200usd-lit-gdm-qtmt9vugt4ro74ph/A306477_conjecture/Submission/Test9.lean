import FormalConjectures.Util.ProblemImports

partial def unsound_proof (x : ℕ) : False :=
  unsound_proof (x + 1)

theorem test_unsound : False := by
  cases unsound_proof 0


