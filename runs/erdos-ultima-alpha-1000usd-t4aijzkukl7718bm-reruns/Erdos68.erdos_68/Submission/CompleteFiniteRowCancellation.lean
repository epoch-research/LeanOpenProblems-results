import Submission.LambertTailRows

/-! Complete cancellation of all rows visible in a finite sampling window
recovers the ordinary original-series partial sum. This is an auxiliary
identity, not a solution of the irrationality conjecture. -/

namespace CompleteFiniteRowCancellation

open Finset Erdos68Development LambertDifferenceOperators LambertTailRows

/-- Rows beyond the sampling window have not begun contributing to the
Lambert prefix. -/
lemma prefixQ_finite_rows (N n : ℕ) (hn : n ≤ N+1) :
    (prefixQ n : ℝ) = (∑ k ∈ Finset.range N, term k) -
      ∑ k ∈ Finset.range N, row n k := by
  have hs := (summable_row n).sum_add_tsum_nat_add N
  have htail : (fun k : ℕ => row n (k+N)) = fun k : ℕ => term (k+N) := by
    funext k
    unfold row geometricRowTail term
    rw [Nat.div_eq_of_lt (by omega), pow_zero, one_mul]
  rw [htail, tsum_row] at hs
  have ht := summable_term.sum_add_tsum_nat_add N
  linarith

/-- This identity permits arbitrary real weights. In particular, it does
not rely on an unjustified clearing of the individual weight denominators. -/
theorem boundary_eq_original_partial {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (index : ι → ℕ) (N : ℕ)
    (hindex : ∀ i ∈ s, index i ≤ N+1)
    (hcancel : ∀ k < N, ∑ i ∈ s, w i * row (index i) k = 0) :
    (∑ i ∈ s, w i * (prefixQ (index i) : ℝ)) =
      (∑ i ∈ s, w i) * (∑ k ∈ Finset.range N, term k) := by
  have hrows : (∑ i ∈ s, w i * ∑ k ∈ Finset.range N, row (index i) k) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k hk
    exact hcancel k (Finset.mem_range.mp hk)
  calc
    _ = ∑ i ∈ s, w i * ((∑ k ∈ Finset.range N, term k) -
        ∑ k ∈ Finset.range N, row (index i) k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [prefixQ_finite_rows N (index i) (hindex i hi)]
    _ = _ := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrows, sub_zero]

/-- Complete visible-row cancellation gives exactly the scaled ordinary
tail, not a new approximation to the original constant. -/
theorem error_eq_original_tail {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (index : ι → ℕ) (N : ℕ)
    (hindex : ∀ i ∈ s, index i ≤ N+1)
    (hcancel : ∀ k < N, ∑ i ∈ s, w i * row (index i) k = 0) :
    (∑ i ∈ s, w i) * (∑' k : ℕ, term k) -
        (∑ i ∈ s, w i * (prefixQ (index i) : ℝ)) =
      (∑ i ∈ s, w i) * ((∑' k : ℕ, term k) - ∑ k ∈ Finset.range N, term k) := by
  rw [boundary_eq_original_partial s w index N hindex hcancel]
  ring

/-- Nonzero retained coefficient does ensure nonzero error in this fully
cancelled case. The error is still multiplied by the partial-sum clearing
factor, whose size is not controlled by this theorem. -/
theorem error_ne_zero {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (index : ι → ℕ) (N : ℕ)
    (hindex : ∀ i ∈ s, index i ≤ N+1)
    (hcancel : ∀ k < N, ∑ i ∈ s, w i * row (index i) k = 0)
    (hA : ∑ i ∈ s, w i ≠ 0) :
    (∑ i ∈ s, w i) * (∑' k : ℕ, term k) -
        (∑ i ∈ s, w i * (prefixQ (index i) : ℝ)) ≠ 0 := by
  rw [error_eq_original_tail s w index N hindex hcancel]
  exact mul_ne_zero hA (partial_sum_error N).1.ne'

/-- Integrality of the aggregate boundary in this situation is exactly
integrality of the retained coefficient times the ordinary partial sum. -/
theorem boundary_integral_iff {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (index : ι → ℕ) (N : ℕ)
    (hindex : ∀ i ∈ s, index i ≤ N+1)
    (hcancel : ∀ k < N, ∑ i ∈ s, w i * row (index i) k = 0) :
    (∃ b : ℤ, (∑ i ∈ s, w i * (prefixQ (index i) : ℝ)) = b) ↔
      ∃ b : ℤ, (∑ i ∈ s, w i) * (∑ k ∈ Finset.range N, term k) = b := by
  rw [boundary_eq_original_partial s w index N hindex hcancel]

end CompleteFiniteRowCancellation

#print axioms CompleteFiniteRowCancellation.boundary_eq_original_partial
#print axioms CompleteFiniteRowCancellation.error_ne_zero
#print axioms CompleteFiniteRowCancellation.boundary_integral_iff
