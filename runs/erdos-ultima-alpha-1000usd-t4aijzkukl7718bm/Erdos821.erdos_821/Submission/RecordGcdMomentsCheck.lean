import Submission.RecordGcdMomentsApplications

/-! Exact-type and axiom checks for uniform record gcd moments. -/

#print axioms Erdos821.CoprimeRecords.gcd_weight_sum_le_core_squares
#print axioms Erdos821.CoprimeRecords.record_gcd_totient_moment_le
#print axioms Erdos821.CoprimeRecords.record_large_overlap_power_bound
#print axioms Erdos821.CoprimeRecords.log_overlap_le_power_moment
#print axioms Erdos821.CoprimeRecords.exists_uniform_record_log_overlap_bound
#print axioms Erdos821.CoprimeRecords.exists_quadratic_record_pool_bound
#print axioms Erdos821.infinite_gAvoiding_independent_range
#print axioms Erdos821.CoprimeRecords.exists_large_records_with_gcd_moment_bound
#print axioms Erdos821.CoprimeRecords.exists_large_records_with_quadratic_pool_bound

open Erdos821 Erdos821.CoprimeRecords in
example (K n : ℕ) (hn : 0 < n) (s t : ℝ) (hst : 1 < 2*s-t)
    (hrec : ∀ j : ℕ, j ≤ n → (gAvoiding K j : ℝ)/(j : ℝ)^s ≤
      (gAvoiding K n : ℝ)/(n : ℝ)^s) :
    gcdTotientMoment K n t ≤ (gAvoiding K n : ℝ)^2*
      ∑' d : ℕ, (Nat.totient d : ℝ)^(-(2*s-t)) :=
  record_gcd_totient_moment_le K n hn s t hst hrec
