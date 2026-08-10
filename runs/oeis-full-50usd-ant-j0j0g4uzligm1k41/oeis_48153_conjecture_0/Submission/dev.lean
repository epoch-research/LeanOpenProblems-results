import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

/-- Reduction: it suffices to prove the strong bound `2 * A048153 n ≤ n * (n-1)`. -/
theorem reduction (n : ℕ) (h : 1 ≤ n) (H : 2 * A048153 n ≤ n * (n - 1)) :
    A048153 n ≤ (n ^ 2 - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have e1 : n ^ 2 = n * n := by ring
  have hkey : n * (n - 1) + n = n * n := by
    cases n with
    | zero => rfl
    | succ m => simp [Nat.succ_sub_one]; ring
  omega
