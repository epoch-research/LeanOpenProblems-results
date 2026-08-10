import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

/-- %C A216265 Conjecture: a(n) > 0 for n > 13. -/
theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  sorry

#print oeis_216265_conjecture_0
#check (show (∀ (n : ℕ), n > 13 → A216265 n > 0) from oeis_216265_conjecture_0)
#check (show ¬ (∀ (n : ℕ), n > 13 → A216265 n > 0) from by
  intro H
  -- cannot use n=13
  have h13bad : ¬ A216265 13 > 0 := by
    decide
  exact h13bad (H 13 (by omega)))
