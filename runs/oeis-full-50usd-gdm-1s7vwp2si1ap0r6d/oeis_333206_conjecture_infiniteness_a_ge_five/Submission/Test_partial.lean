import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (n ^ 3)).min?.getD 0

partial def find_next (M : ℕ) : ℕ :=
  if 5 ≤ a M then M else find_next (M + 1)

theorem test_partial (M : ℕ) : 5 ≤ a (find_next M) := by
  unfold find_next
