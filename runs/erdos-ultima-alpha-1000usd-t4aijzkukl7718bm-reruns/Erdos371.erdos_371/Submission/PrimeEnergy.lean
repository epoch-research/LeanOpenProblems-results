import FormalConjecturesUtil
import Submission.PrimeDiscrepancy
import Submission.CofactorDensity

/-! A square-mean estimate would suffice for the largest-prime-factor density conjecture.
The estimate itself is not asserted in this file. -/

namespace Erdos371PrimeEnergy

open Erdos371PrimeDiscrepancy Erdos371CofactorDensity Filter
open scoped Topology

def energy (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow, (group p N : ℝ) ^ 2

lemma squared_discrepancy_le (N : ℕ) :
    ((∑ p ∈ (N + 1).primesBelow, group p N : ℤ) : ℝ) ^ 2 ≤
      Nat.primeCounting N * energy N := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := (N + 1).primesBelow) (f := fun p => (group p N : ℝ))
  rw [Nat.primesBelow_card_eq_primeCounting'] at h
  push_cast
  exact h

lemma density_half_of_eventually_linear_energy {C : ℝ}
    (hE : ∀ᶠ N : ℕ in atTop, energy N ≤ C * N) :
    {n | P n < P (n + 1)}.HasDensity (1 / 2) := by
  apply density_half_iff_prime_discrepancy.mpr
  have hu : Tendsto (fun N : ℕ => Real.sqrt (C * ((Nat.primeCounting N : ℝ) / N)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul primeCounting_ratio_tendsto_zero).sqrt
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [hE, eventually_gt_atTop 0] with N hEN hN
    change |((∑ p ∈ (N + 1).primesBelow, group p N : ℤ) : ℝ) / N| ≤ _
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs, div_pow]
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    calc
      _ ≤ (Nat.primeCounting N : ℝ) * energy N := squared_discrepancy_le N
      _ ≤ (Nat.primeCounting N : ℝ) * (C * N) :=
        mul_le_mul_of_nonneg_left hEN (Nat.cast_nonneg _)
      _ = C * ((Nat.primeCounting N : ℝ) / N) * (N : ℝ) ^ 2 := by
        field_simp

lemma energy_nonneg (N : ℕ) : 0 ≤ energy N := by
  exact Finset.sum_nonneg (fun p _ => sq_nonneg (group p N : ℝ))

/-- The direct Cauchy–Schwarz criterion; no bound on `energy` is assumed implicitly. -/
lemma density_half_of_energy_product_tendsto_zero
    (hE : Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) * energy N / (N : ℝ) ^ 2)
      atTop (𝓝 0)) :
    {n | P n < P (n + 1)}.HasDensity (1 / 2) := by
  apply density_half_iff_prime_discrepancy.mpr
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hu := hE.sqrt
  simp only [Real.sqrt_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    exact abs_nonneg _
  · intro N
    change |((∑ p ∈ (N + 1).primesBelow, group p N : ℤ) : ℝ) / N| ≤ _
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs, div_pow]
    exact div_le_div_of_nonneg_right (squared_discrepancy_le N) (sq_nonneg (N : ℝ))

/-- An `o(N log N)` energy estimate suffices. This estimate is a hypothesis,
not an unconditional result about largest prime factors. -/
lemma density_half_of_energy_div_n_log_tendsto_zero
    (hE : Tendsto (fun N : ℕ => energy N / ((N : ℝ) * Real.log N))
      atTop (𝓝 0)) :
    {n | P n < P (n + 1)}.HasDensity (1 / 2) := by
  apply density_half_of_energy_product_tendsto_zero
  have hu : Tendsto (fun N : ℕ =>
      (Real.log 4 + 1) * (energy N / ((N : ℝ) * Real.log N))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hE
  have hb : ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤ (Real.log 4 + 1) * N / Real.log N := by
    simpa using
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => by
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (energy_nonneg N)) (sq_nonneg _)
  · filter_upwards [hb, eventually_gt_atTop 1] with N hN hN1
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
    calc
      (Nat.primeCounting N : ℝ) * energy N / (N : ℝ) ^ 2
          ≤ ((Real.log 4 + 1) * N / Real.log N) * energy N / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hN (energy_nonneg N)) (sq_nonneg _)
      _ = (Real.log 4 + 1) * (energy N / ((N : ℝ) * Real.log N)) := by
        field_simp

end Erdos371PrimeEnergy

#print axioms Erdos371PrimeEnergy.density_half_of_eventually_linear_energy
#print axioms Erdos371PrimeEnergy.density_half_of_energy_product_tendsto_zero
#print axioms Erdos371PrimeEnergy.density_half_of_energy_div_n_log_tendsto_zero
