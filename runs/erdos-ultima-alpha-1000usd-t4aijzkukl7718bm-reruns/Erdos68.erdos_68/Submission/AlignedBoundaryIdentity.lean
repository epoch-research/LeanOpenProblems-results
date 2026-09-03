import Submission.AlignedRowAnnihilator
import Submission.LambertTailRows

/-! At phase zero, the aligned annihilator gives exactly the ordinary
original-series partial sum. This is auxiliary work, not a settlement. -/

namespace AlignedBoundaryIdentity

open Finset Erdos68Development LambertDifferenceOperators LambertTailRows
  LambertRawBounds AlignedRowAnnihilator

lemma prefix_rows (N j : ℕ) (hN : 2 ≤ N) (hj : j ≤ N) :
    (prefixQ j : ℝ) = ∑ k ∈ range (N-1), (term k - row j k) := by
  have he : (∑' k : ℕ, (term k - row j k)) = (prefixQ j : ℝ) := by
    rw [summable_term.tsum_sub (summable_row j), tsum_row]
    ring
  rw [← he]
  apply tsum_eq_sum
  intro k hk
  have hk' : N < k+2 := by
    simp only [mem_range] at hk
    omega
  have hjk : j/(k+2)=0 := Nat.div_eq_of_lt (hj.trans_lt hk')
  simp [row, geometricRowTail, term, hjk]

/-- This identity holds for any weights cancelling all the rows on this
window, not just the explicit backwards recursion. -/
theorem boundary_of_row_cancellation (N : ℕ) (hN : 2 ≤ N)
    (z : ℕ → ℤ) (A : ℤ) (hA : ∑ j ∈ range (N+1), z j = A)
    (hz : ∀ d, 2 ≤ d → d ≤ N →
      (∑ j ∈ range (N+1), (z j : ℚ) /
        ((d.factorial : ℚ)^(j/d)*((d.factorial : ℚ)-1))) = 0) :
    (∑ j ∈ range (N+1), (z j : ℝ)*(prefixQ j : ℝ)) =
      (A : ℝ)*(∑ k ∈ range (N-1), term k) := by
  have hsum : (∑ j ∈ range (N+1), (z j : ℝ)) = (A : ℝ) := by
    exact_mod_cast hA
  have hzero (k : ℕ) (hk : k ∈ range (N-1)) :
      (∑ j ∈ range (N+1), (z j : ℝ)*row j k) = 0 := by
    have hkN : k+2 ≤ N := by have := mem_range.mp hk; omega
    have h := hz (k+2) (by omega) hkN
    have h' : (∑ j ∈ range (N+1), (z j : ℝ) /
        (((k+2).factorial : ℝ)^(j/(k+2))*(((k+2).factorial : ℝ)-1))) = 0 := by
      exact_mod_cast h
    simpa only [row, geometricRowTail, mul_one_div] using h'
  calc
    _ = ∑ j ∈ range (N+1), ∑ k ∈ range (N-1),
        (z j : ℝ)*(term k-row j k) := by
      apply sum_congr rfl
      intro j hj
      rw [prefix_rows N j hN (by have := mem_range.mp hj; omega), mul_sum]
    _ = ∑ k ∈ range (N-1), ∑ j ∈ range (N+1),
        (z j : ℝ)*(term k-row j k) := sum_comm
    _ = ∑ k ∈ range (N-1), (A : ℝ)*term k := by
      apply sum_congr rfl
      intro k hk
      simp_rw [mul_sub]
      rw [sum_sub_distrib, ← sum_mul, hsum, hzero k hk, sub_zero]
    _ = _ := (mul_sum ..).symm

theorem aligned_boundary (A : ℤ) (N : ℕ) (hN : 2 ≤ N)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → (d.factorial : ℤ)-1 ∣ A) :
    (∑ j ∈ range (N+1), (weight A N j : ℝ)*(prefixQ j : ℝ)) =
      (A : ℝ)*(∑ k ∈ range (N-1), term k) :=
  boundary_of_row_cancellation N hN (weight A N) A (weight_sum A N hN)
    (fun d hd hdN => weight_annihilates A N d hd hdN (hdiv d hd hdN))

theorem aligned_error (A : ℤ) (N : ℕ) (hN : 2 ≤ N)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → (d.factorial : ℤ)-1 ∣ A) (x : ℝ) :
    (∑ j ∈ range (N+1), (weight A N j : ℝ)*(x-(prefixQ j : ℝ))) =
      (A : ℝ)*(x-∑ k ∈ range (N-1), term k) := by
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, aligned_boundary A N hN hdiv]
  have hsum : (∑ j ∈ range (N+1), (weight A N j : ℝ)) = A := by
    exact_mod_cast weight_sum A N hN
  rw [hsum]


lemma scaled_partial_sum_integral (A : ℤ) (N : ℕ)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → (d.factorial : ℤ)-1 ∣ A) :
    ∃ b : ℤ, (A : ℝ)*(∑ k ∈ range (N-1), term k) = b := by
  refine ⟨∑ k ∈ range (N-1), A/(((k+2).factorial : ℤ)-1), ?_⟩
  rw [mul_sum]
  simp only [Int.cast_sum]
  apply sum_congr rfl
  intro k hk
  have hkN : k+2 ≤ N := by have := mem_range.mp hk; omega
  have hd : ((((k+2).factorial : ℤ)-1 : ℤ) : ℝ) ≠ 0 := by
    push_cast
    exact (denom_pos k).ne'
  rw [Int.cast_div (hdiv (k+2) (by omega) hkN) hd]
  simp [term, div_eq_mul_inv]

theorem aligned_boundary_integral (A : ℤ) (N : ℕ) (hN : 2 ≤ N)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → (d.factorial : ℤ)-1 ∣ A) :
    ∃ b : ℤ, (∑ j ∈ range (N+1),
      (weight A N j : ℝ)*(prefixQ j : ℝ)) = b := by
  rw [aligned_boundary A N hN hdiv]
  exact scaled_partial_sum_integral A N hdiv

theorem aligned_error_pos (A : ℤ) (N : ℕ) (hA : 0 < A) (hN : 2 ≤ N)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → (d.factorial : ℤ)-1 ∣ A) :
    0 < ∑ j ∈ range (N+1), (weight A N j : ℝ)*
      ((∑' k : ℕ, term k)-(prefixQ j : ℝ)) := by
  rw [aligned_error A N hN hdiv]
  exact mul_pos (by exact_mod_cast hA) (partial_sum_error (N-1)).1


end AlignedBoundaryIdentity

#print axioms AlignedBoundaryIdentity.boundary_of_row_cancellation
#print axioms AlignedBoundaryIdentity.aligned_boundary
#print axioms AlignedBoundaryIdentity.aligned_error

#print axioms AlignedBoundaryIdentity.aligned_boundary_integral
#print axioms AlignedBoundaryIdentity.aligned_error_pos
