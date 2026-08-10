import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (n ^ 3)).min?.getD 0

theorem a19_ge_5 : 5 ≤ a 463785349256275 := by
  unfold a
  norm_num

#print axioms a19_ge_5
