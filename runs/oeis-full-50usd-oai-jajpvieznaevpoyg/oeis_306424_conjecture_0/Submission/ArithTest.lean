import FormalConjectures.Util.ProblemImports

example (m : ℕ) (hm : 1 ≤ m) : (m+1)*(m+1) + (2*(m+1)-3) = m*(4+m) := by
  have hsub : (2*(m+1)-3) + 3 = 2*(m+1) := by omega
  nlinarith

example (m : ℕ) (hm : 3 ≤ m) : (m+3)*(m+3) + (2*(m+3)-2) = 13 + m*(8+m) := by
  have hsub : (2*(m+3)-2) + 2 = 2*(m+3) := by omega
  nlinarith

example (m : ℕ) (hm : 3 ≤ m) : (m+3)*(m+3) + (2*(m+3)-1) = 14 + m*(8+m) := by
  have hsub : (2*(m+3)-1) + 1 = 2*(m+3) := by omega
  nlinarith


example (n : ℕ) (hn : 20 ≤ n) : n*n + (2*n - 3) = 0 + (n-1)*(4+(n-1)) := by
  let m := n - 1
  have hn1 : n = m + 1 := by omega
  rw [hn1]
  change (m+1)*(m+1) + (2*(m+1)-3) = 0 + m*(4+m)
  have hsub : (2*(m+1)-3) + 3 = 2*(m+1) := by omega
  nlinarith
