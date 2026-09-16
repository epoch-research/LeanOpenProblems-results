import FormalConjectures.Util.ProblemImports

def dc (a b : ℕ) : ℕ × ℤ :=
  if h1 : b ≤ a then (1, 0)
  else if h2 : b = a + 1 then (a, if a % 2 = 0 then (1 : ℤ) else -1)
  else
    let m := (a + b) / 2
    have hm1 : m - a < b - a := by omega
    have hm2 : b - m < b - a := by omega
    let (p1, f1) := dc a m
    let (p2, f2) := dc m b
    (p1 * p2, f1 * (p2 : ℤ) + (p1 : ℤ) * f2)
termination_by b - a

theorem test : (dc 2 50000).2 ≠ 0 := by decide
