import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

mutual
  theorem S_bound_inductive (n : ℕ) :
      3 * (∑ k ∈ range n, k ^ 2 / n) ≥ (n - 1) * (n - 2) := by
    rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp
      · -- n is at least 2
        have h_odd := a048153_odd_le n
        sorry

  theorem a048153_odd_le (H : ℕ) : A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
    have h_Q := S_bound_inductive (2 * H + 1)
    sorry
end
