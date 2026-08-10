import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

/-- %C A216265 Conjecture: a(n) > 0 for n > 13. -/
theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  sorry

#print oeis_216265_conjecture_0
#check (show (∀ (n : ℕ), n > 13 → A216265 n > 0) from oeis_216265_conjecture_0)
#check (show ¬ (∀ (n : ℕ), n > 13 → A216265 n > 0) from by
  intro h
  have hh : A216265 14 > 0 := h 14 (by norm_num)
  -- cannot contradict
  exact (by omega : False))
