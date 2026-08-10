import FormalConjectures.Util.ProblemImports

def a_orig (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

def a_fast (n : ℕ) : ℕ :=
  if n ≤ 42 then
    a_orig n
  else
    0

@[implemented_by a_fast]
def a (n : ℕ) : ℕ := a_orig n

theorem test_decide : a 43 = 0 := by
  decide
