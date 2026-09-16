import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def dc_reduced (fuel a b : ℕ) : ℕ × ℤ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if b ≤ a then (1, 0)
    else if b = a + 1 then (a, if a % 2 = 0 then (1 : ℤ) else -1)
    else
      let m := (a + b) / 2
      let (m1, f1) := dc_reduced fuel' a m
      let (m2, f2) := dc_reduced fuel' m b
      let f_num := f1 * m2 + f2 * m1
      let m_den := m1 * m2
      let g := Int.gcd f_num m_den
      (m_den / g, f_num / g)

theorem test : (dc_reduced 21 2 100000).1 > 0 := by decide
