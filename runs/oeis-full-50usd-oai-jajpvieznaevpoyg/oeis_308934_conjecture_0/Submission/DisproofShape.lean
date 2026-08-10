import FormalConjectures.Util.ProblemImports
open Nat Finset
def A308934 (n : ℕ) : ℕ := 1
theorem oeis_308934_conjecture_0 (n : ℕ) (hn : n > 1) : A308934 n > 0 := by simp [A308934]
#check (show ¬ (∀ (n : ℕ), n > 1 → A308934 n > 0) from by intro h; exact Nat.not_succ_le_zero _ (h 2 (by decide)))
#print oeis_308934_conjecture_0
