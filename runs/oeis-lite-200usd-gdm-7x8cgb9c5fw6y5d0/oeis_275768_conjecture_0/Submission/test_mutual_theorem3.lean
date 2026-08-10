import Mathlib

mutual
  def foo (n : ℕ) : n + 1 ≠ 0 :=
    match n with
    | 0 => fun h => by omega
    | k + 1 => fun h => by omega

  def bar (n : ℕ) : ℕ :=
    if h : n + 1 = 0 then
      False.elim (foo n h)
    else 0
end
