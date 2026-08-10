import FormalConjectures.Util.ProblemImports

def blocking_prime_by_idx (idx : ℕ) : ℕ :=
  if idx = 0 then 3 else 7

def N : ℕ := 10

def is_blocked_by_idx (idx : ℕ) : Bool :=
  let p := blocking_prime_by_idx idx
  let v := if idx = 6400 then 1 else 4^(idx / 40) * (10 * 16^(idx % 40) + 16 * 4^(idx % 40) + 10) / 9
  (N^2 - v) % p == 0 && (N^2 - v) % (p^2) != 0

-- Test if decide can prove this for all idx < 100
theorem is_blocked_all_test : ∀ idx < 100, is_blocked_by_idx idx = true := by
  decide
