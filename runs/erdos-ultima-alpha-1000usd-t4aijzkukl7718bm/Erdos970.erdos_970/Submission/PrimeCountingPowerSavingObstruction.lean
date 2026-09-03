import Submission.RectangularVarianceIteration
import Submission.PrimeCountingDyadicDiscrepancy

/-! An elementary obstruction to a power-saving scaling recurrence for the
prime-counting function. The bases 4096 and 2048 encode exponents 12 and 11. -/
namespace Erdos970.PrimeCountingDyadic
open Filter Real Finset
open scoped Topology

lemma primeCounting_le_primeCounting'_add_one (m : ℕ) :
    m.primeCounting ≤ m.primeCounting' + 1 := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ]
  split_ifs <;> omega

lemma density'_tendsto_zero :
    Tendsto (fun n : ℕ => (n.primeCounting' : ℝ) / n) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun n : ℕ => (n.primeCounting : ℝ) / n)
    (Eventually.of_forall (fun _ => by positivity)) _ density_tendsto_zero
  apply Eventually.of_forall
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast Nat.monotone_primeCounting' (Nat.le_succ n)

lemma not_bounded_count_4096 (D : ℝ) :
    ¬∀ j : ℕ, ((4096 ^ j).primeCounting' : ℝ) ≤ D * 2048 ^ j := by
  intro hh
  obtain ⟨n, hn⟩ := exists_nat_gt (max 4 (48 * (D + 1)))
  have hn4 : 4 ≤ n := by exact_mod_cast ((le_max_left _ _).trans_lt hn).le
  have hnD : 48 * (D + 1) < n := (le_max_right _ _).trans_lt hn
  have hnpos : 0 < n := by omega
  have hx : 2 ≤ 4096 ^ n := by
    have hh := Nat.le_self_pow hnpos.ne' 4096
    omega
  have hl := PrimeCountingLower.log_bound (4096 ^ n) hx
  have hl4096 : log (4096 : ℝ) = 12 * log 2 := by
    rw [show (4096 : ℝ) = 2 ^ (12 : ℕ) by norm_num, log_pow]
    norm_num
  simp only [Nat.cast_pow, Nat.cast_ofNat, log_pow, hl4096] at hl
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hmain : (4096 : ℝ) ^ n ≤ 48 * n * (4096 ^ n).primeCounting := by nlinarith only [hl, hl2]
  have hpi : ((4096 ^ n).primeCounting : ℝ) ≤ (D + 1) * 2048 ^ n := by
    have h0 : ((4096 ^ n).primeCounting : ℝ) ≤ (4096 ^ n).primeCounting' + 1 := by
      exact_mod_cast primeCounting_le_primeCounting'_add_one (4096 ^ n)
    have hp1 : (1 : ℝ) ≤ 2048 ^ n := one_le_pow₀ (by norm_num)
    nlinarith only [h0, hh n, hp1]
  have hsmall := hmain.trans (mul_le_mul_of_nonneg_left hpi (by positivity))
  have hid : (4096 : ℝ) ^ n = 2 ^ n * 2048 ^ n := by rw [← mul_pow]; norm_num
  rw [hid] at hsmall
  have hpowpos : (0 : ℝ) < 2048 ^ n := by positivity
  have hsmall' : (2 : ℝ) ^ n ≤ 48 * n * (D + 1) := by nlinarith only [hsmall, hpowpos]
  have hsq : (n : ℝ) ^ 2 ≤ 2 ^ n := by exact_mod_cast nat_sq_le_two_pow n hn4
  have hnp : (0 : ℝ) < n := by exact_mod_cast hnpos
  nlinarith only [hsmall', hsq, hnD, hnp]

/-- Even a one-sided power-saving scaling recurrence is impossible. -/
theorem not_bounded_4096_difference :
    ¬∃ B : ℝ, ∀ j : ℕ,
      4096 * ((4096 ^ j).primeCounting' : ℝ) - (4096 ^ (j + 1)).primeCounting' ≤ B * 2048 ^ j := by
  rintro ⟨B, hB⟩
  have hlim : Tendsto (fun j : ℕ => ((4096 ^ j).primeCounting' : ℝ) / (4096 : ℝ) ^ j)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow, Nat.cast_ofNat] using density'_tendsto_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 4096))
  have hb := GapAverages.upper_of_halving_recurrence_at
    (fun j => ((4096 ^ j).primeCounting' : ℝ)) 4096 (B / 4096) 0 (by norm_num) hlim (fun j => by
      norm_num only [show (4096 : ℝ) / 2 = 2048 by norm_num]
      have hh := hB j
      linarith only [hh])
  apply not_bounded_count_4096 (2 * (B / 4096))
  simpa only [zero_mul, zero_add, show (4096 : ℝ) / 2 = 2048 by norm_num] using hb

/-- Removing finitely many scales does not make the recurrence possible. -/
theorem not_eventually_bounded_4096_difference (B : ℝ) :
    ¬∀ᶠ j : ℕ in atTop,
      4096 * ((4096 ^ j).primeCounting' : ℝ) - (4096 ^ (j + 1)).primeCounting' ≤ B * 2048 ^ j := by
  intro hevent
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let f := fun j : ℕ => 4096 * ((4096 ^ j).primeCounting' : ℝ) - (4096 ^ (j + 1)).primeCounting'
  let H := ∑ j ∈ range N, max 0 (f j / 2048 ^ j)
  apply not_bounded_4096_difference
  refine ⟨max B H, fun j => ?_⟩
  have hp : (0 : ℝ) < 2048 ^ j := by positivity
  by_cases hj : N ≤ j
  · exact (hN j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  · have hterm : max 0 (f j / 2048 ^ j) ≤ H := single_le_sum (s := range N) (f := fun i => max 0 (f i / 2048 ^ i))
      (fun j _ => le_max_left _ _) (mem_range.mpr (by omega))
    have hbound : f j ≤ H * 2048 ^ j := (div_le_iff₀ hp).mp ((le_max_right _ _).trans hterm)
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le)

#print axioms not_bounded_4096_difference
#print axioms not_eventually_bounded_4096_difference
end Erdos970.PrimeCountingDyadic
