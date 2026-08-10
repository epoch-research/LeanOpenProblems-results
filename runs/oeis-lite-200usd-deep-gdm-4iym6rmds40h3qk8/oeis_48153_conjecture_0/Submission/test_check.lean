import FormalConjectures.Util.ProblemImports

open Finset

def S_term (n k : ℕ) : ℕ := if 3 * k ≥ n + 1 then 9 * k - 3 * n - 3 else 0
def S_sum (n : ℕ) : ℕ := ∑ k ∈ range n, S_term n k

lemma k_bound_universal (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : 3 * (k^2 / n) + n + 1 ≥ 3 * k := sorry

lemma k_sq_div_piecewise (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) :
    3 * (k ^ 2 / n) ≥ if 3 * k ≥ n + 1 then 3 * k - n - 1 else 0 := by
  split_ifs with h
  · have h_univ := k_bound_universal n k hn hk
    omega
  · omega

theorem S_sum_ge_target (n : ℕ) (hn : 5 ≤ n) : S_sum n ≥ (n - 1) * (n - 2) := sorry

lemma S_lower_bound (n : ℕ) (hn : 5 ≤ n) : 
    9 * (∑ k ∈ range n, k^2 / n) ≥ S_sum n := by
  have h_sum : 9 * (∑ k ∈ range n, k^2 / n) ≥ S_sum n := by
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk_lt : k < n := Finset.mem_range.mp hk
    have h_piece := k_sq_div_piecewise n k hn hk_lt
    have h_term_mul : 9 * (k^2 / n) = 3 * (3 * (k^2 / n)) := by ring
    rw [h_term_mul]
    unfold S_term
    split_ifs with h
    · split_ifs at h_piece
      omega
    · omega
  exact h_sum
