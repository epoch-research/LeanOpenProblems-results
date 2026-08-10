import Mathlib

mutual
  theorem foo (n : ℕ) : n + 1 ≠ 0 := by
    cases n
    · decide
    · decide

  def bar (n : ℕ) : ℕ :=
    if h : n + 1 = 0 then
      False.elim (foo n h)
    else 0
end
