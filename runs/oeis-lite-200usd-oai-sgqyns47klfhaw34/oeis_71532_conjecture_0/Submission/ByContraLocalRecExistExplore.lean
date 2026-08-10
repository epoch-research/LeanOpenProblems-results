import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  classical
  by_contra h
  let rec hp : P := False.elim (h hp)
  exact hp

example (Q : Nat → Prop) : (∃ n, Q n) := by
  classical
  by_contra h
  let rec ex : ∃ n, Q n := ⟨0, False.elim (h ex)⟩
  exact ex
