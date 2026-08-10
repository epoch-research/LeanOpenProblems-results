import FormalConjectures.Util.ProblemImports

example (m : ℕ) (hm : m ≠ 1) : Nat.Prime m := by
  fail_if_success simpa using (Nat.minFac_prime hm : Nat.Prime m.minFac)
  fail_if_success exact (Nat.prime_def_minFac.mpr ⟨by omega, by simp⟩)
  admit

-- Check if concrete target numbers for symbolic n can be normalized to a minFac form (no).
example (n k : ℕ) : Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) := by
  fail_if_success simp
  admit
