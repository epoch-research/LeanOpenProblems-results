import Submission.ContinuousIntervalQuantum

/-! An exact check of a strict improvement at an INTEGER length. Unlike a
lattice chord alone, the integer-threshold patch may raise endpoint values.
This is not a uniform asymptotic estimate. -/
namespace Erdos970.ContinuousInterval

private noncomputable def q3 (i : ℕ) : ℝ :=
  if i = 0 then 1 / 2 else if i = 1 then 1 / 3 else 1 / 5

private noncomputable def L3 (x : ℝ) : ℝ := (envelope q3 3 x).1
private noncomputable def U3 (x : ℝ) : ℝ := (envelope q3 3 x).2

private theorem q3_bounds (i : ℕ) : 0 ≤ q3 i ∧ q3 i ≤ 1 := by
  dsimp [q3]
  split_ifs <;> norm_num

private theorem d3 : density q3 3 = 4 / 15 := by
  norm_num [density, Finset.prod_range_succ, q3]

private theorem reg3 : Regular (4 / 15) L3 U3 := by
  have hh := envelope_regular q3 3 (fun i _ => q3_bounds i)
  rwa [d3] at hh

private theorem endpoint_values : L3 9 = 0 ∧ L3 10 = 1 / 10 ∧ L3 11 = 1 / 3 := by
  norm_num [L3, envelope, q3, stepLower, stepUpper, clip]

/-- The strengthened endpoint value is 7/45, compared with the old 1/10. -/
theorem quantum_three_at_ten :
    quantumPatch (4 / 15) 10 (quantumSlope L3 10) (quantumIntercept L3 10) L3 10 = 7 / 45 := by
  norm_num [quantumPatch, quantumSlope, quantumIntercept, quantumFactor,
    endpoint_values.2.1, endpoint_values.2.2]

theorem quantum_three_strict_gain :
    L3 10 < quantumPatch (4 / 15) 10 (quantumSlope L3 10) (quantumIntercept L3 10) L3 10 := by
  rw [quantum_three_at_ten, endpoint_values.2.1]
  norm_num

/-- The improved lower function remains regular and bounds the normalized
counts for EVERY larger pairwise coprime triple, not just the reference primes. -/
theorem quantum_three_certificate (p : ℕ → ℕ)
    (hp : ∀ i < 3, 1 < p i)
    (hc : ∀ i < 3, ∀ j < i, (p i).Coprime (p j))
    (hQ : ∀ i < 3, 1 / (p i : ℝ) ≤ q3 i ∧ q3 i ≤ 1) :
    Regular (4 / 15)
      (quantumPatch (4 / 15) 10 (quantumSlope L3 10) (quantumIntercept L3 10) L3) U3 ∧
    IntervalBounds
      (quantumPatch (4 / 15) 10 (quantumSlope L3 10) (quantumIntercept L3 10) L3)
      U3 (normalization p q3 3) p 3 := by
  have hb : IntervalBounds L3 U3 (normalization p q3 3) p 3 :=
    envelope_normalized_bound p q3 3 hp hc hQ
  apply quantum_cell_certificate reg3 hb 10 (by norm_num)
  · simpa only [d3] using density_le_normalization p q3 3 hp hQ
  · norm_num
  · simpa only [show 10 - 1 = (9 : ℕ) by omega, Nat.cast_ofNat] using endpoint_values.1
  · norm_num [endpoint_values.2.1]

#print axioms quantum_three_strict_gain
#print axioms quantum_three_certificate
end Erdos970.ContinuousInterval
