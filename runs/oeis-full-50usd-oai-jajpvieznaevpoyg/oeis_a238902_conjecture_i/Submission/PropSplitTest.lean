import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

example (n : ℕ) (hn : n > 0) : a n > 0 := by
  rcases Classical.propComplete (a n > 0) with h | h
  · simpa [h]
  · have : ¬ a n > 0 := by simpa [h]
    -- can we derive contradiction?
    have hcard : a n = 0 := Nat.eq_zero_of_not_pos this
    simp [a] at hcard
    guard_target = a n > 0
    exact False.elim (by sorry)
