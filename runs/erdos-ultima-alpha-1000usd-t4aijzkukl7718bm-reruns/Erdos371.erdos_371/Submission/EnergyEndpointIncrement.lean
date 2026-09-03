import FormalConjecturesUtil
import Submission.OffDiagonalEnergy

/-! An exact endpoint recurrence for the signed winning-prime energy.
The drift need not be nonpositive at each endpoint. No asymptotic
cancellation bound, and no proof or disproof of Erdős 371, is asserted. -/

namespace Erdos371EnergyEndpointIncrement

open Finset Erdos371PrimeDiscrepancy Erdos371PrimeEnergy
  Erdos371OffDiagonalEnergy

lemma correlation_row {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ range N, correlation n N) =
      (sign N : ℝ) * (group (winner N) N : ℝ) := by
  rw [group_cast, mul_sum]
  apply sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    have hw : winner 0 ≠ winner N := by
      rw [winner_zero]
      exact (winner_prime hN).ne_one.symm
    simp [correlation, hw]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    simp only [correlation, hnpos, hN, true_and]
    split_ifs <;> ring

/-- The drift at a new endpoint is a signed prime-group partial sum.
It cannot be discarded on a pointwise sign argument. -/
theorem energy_succ {N : ℕ} (hN : 0 < N) :
    energy (N+1) = energy N + 1 +
      2 * (sign N : ℝ) * (group (winner N) N : ℝ) := by
  rw [energy_expansion, energy_expansion]
  have ho : offDiagonal (N+1) = offDiagonal N +
      (sign N : ℝ) * (group (winner N) N : ℝ) := by
    rw [offDiagonal, sum_range_succ, correlation_row hN]
    rfl
  rw [ho]
  have hn : ((N : ℕ) : ℝ) = ((N-1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show N = (N-1)+1 by omega)
  simp only [Nat.add_sub_cancel]
  rw [hn]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma endpoint_32 : sign 32 = 1 ∧ winner 32 = 11 ∧ group 11 32 = 1 := by
  decide +kernel

/-- The energy jumps by three at endpoint 32, not by at most one. -/
theorem positive_drift_example : energy 33 = energy 32 + 3 := by
  have h := energy_succ (N := 32) (by omega)
  rw [endpoint_32.1, endpoint_32.2.1, endpoint_32.2.2] at h
  norm_num at h
  linarith

theorem not_pointwise_unit_increment :
    ¬ ∀ N : ℕ, 0 < N → energy (N+1) ≤ energy N + 1 := by
  intro h
  have hh := h 32 (by omega)
  have he := positive_drift_example
  linarith

end Erdos371EnergyEndpointIncrement

#print axioms Erdos371EnergyEndpointIncrement.energy_succ
#print axioms Erdos371EnergyEndpointIncrement.not_pointwise_unit_increment
