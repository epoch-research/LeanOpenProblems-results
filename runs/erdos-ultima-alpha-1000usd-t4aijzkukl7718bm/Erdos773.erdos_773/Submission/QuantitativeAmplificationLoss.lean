import Submission.PowerAmplificationBarrier

/-!
Quantitative limitations on eventual square-scale amplification.
These statements concern proposed amplification laws, not the negation of
Erdős 773.
-/
namespace Erdos773.Amplification
open Filter
open scoped Topology
set_option maxHeartbeats 1000000

lemma squareDensity_exp_upper (N : ℕ) (hN : 128 ^ 128 ≤ N) :
    squareDensity N ≤ 2 * Real.exp
      (-Real.log N / (512 * Real.log (Real.log N))) := by
  have hp : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (128 : ℕ) ^ 128) hN)
  apply (div_le_iff₀ hp).mpr
  have h := square_sidon_primorial_upper N hN
  dsimp [squareMax]
  nlinarith only [h]

lemma half_power_exp_bound {x A : ℝ} (hx : 0 ≤ x)
    (h : x ≤ 2 * Real.exp (-A)) :
    x ^ (1 / 2 : ℝ) ≤ 2 * Real.exp (-A / 2) := by
  have hs : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have he : (Real.exp (-A / 2)) ^ 2 = Real.exp (-A) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hepos := Real.exp_pos (-A)
  have ht : 0 ≤ 2 * Real.exp (-A / 2) := by positivity
  nlinarith only [hs, he, h, hepos, ht]

/-- A primorial-scale loss is necessary infinitely often for this form of
amplification. This is not an upper bound with a fixed exponent loss. -/
theorem frequently_primorial_loss (c : ℝ) (hc : 0 < c) :
    ∃ᶠ N : ℕ in atTop,
      squareMax (N ^ 2) < c * N * squareMax N *
        Real.exp (-Real.log N / (1024 * Real.log (Real.log N))) := by
  have hf := frequently_small_power_density_gain (3 / 2) (c / 2)
    (by norm_num) (by positivity)
  apply (hf.and_eventually (eventually_ge_atTop (128 ^ 128))).mono
  rintro N ⟨hh, hN⟩
  have hn : 1 ≤ N := by omega
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := squareDensity_pos N hn
  have he : squareDensity N ≤ 2 * Real.exp
      (-(Real.log N / (512 * Real.log (Real.log N)))) := by
    simpa only [neg_div] using squareDensity_exp_upper N hN
  have hu := half_power_exp_bound hp.le he
  have hid : -(Real.log (N : ℝ) / (512 * Real.log (Real.log N))) / 2 =
      -Real.log N / (1024 * Real.log (Real.log N)) := by ring
  rw [hid] at hu
  have hpow : squareDensity N ^ (3 / 2 : ℝ) =
      squareDensity N * squareDensity N ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one]
  have hb : squareDensity (N ^ 2) < c * squareDensity N *
      Real.exp (-Real.log N / (1024 * Real.log (Real.log N))) := by
    rw [hpow] at hh
    have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ (c / 2) * squareDensity N by positivity)
    nlinarith only [hh, hm]
  dsimp [squareDensity] at hb
  rw [Nat.cast_pow] at hb
  have hm := (div_lt_iff₀ (sq_pos_of_pos hn0)).mp hb
  convert hm using 1
  field_simp

lemma eventually_log_power_le_primorial (a : ℝ) (ha : a < 1) :
    ∀ᶠ N : ℕ in atTop, (Real.log (N : ℝ)) ^ a ≤
      Real.log N / (1024 * Real.log (Real.log N)) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb := ((isLittleO_log_rpow_atTop (show 0 < 1 - a by linarith)).bound
    (show (0 : ℝ) < 1 / 1024 by norm_num))
  filter_upwards [ht.eventually hb, ht.eventually (eventually_gt_atTop 1)] with N hN hL
  have hp : 0 < Real.log (N : ℝ) := by linarith
  have hpp := Real.log_pos hL
  simp only [Real.norm_eq_abs, abs_of_pos hpp,
    abs_of_pos (Real.rpow_pos_of_pos hp (1 - a))] at hN
  apply (le_div_iff₀ (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hp.le a)
  have hid : Real.log (N : ℝ) ^ (1 - a) * Real.log (N : ℝ) ^ a = Real.log N := by
    rw [← Real.rpow_add hp]
    simp
  nlinarith only [hm, hid]

/-- In particular, every fixed logarithmic-power loss with exponent below one
is too small to support an eventual amplification law of this form. -/
theorem frequently_log_power_loss (a c : ℝ) (ha : a < 1) (hc : 0 < c) :
    ∃ᶠ N : ℕ in atTop, squareMax (N ^ 2) < c * N * squareMax N *
      Real.exp (-(Real.log (N : ℝ)) ^ a) := by
  apply ((frequently_primorial_loss c hc).and_eventually
    ((eventually_log_power_le_primorial a ha).and (eventually_ge_atTop 1))).mono
  rintro N ⟨hN, he, hn⟩
  have hp := squareMax_pos N hn
  have hm : Real.exp (-Real.log (N : ℝ) / (1024 * Real.log (Real.log N))) ≤
      Real.exp (-(Real.log (N : ℝ)) ^ a) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg he
  exact hN.trans_le (mul_le_mul_of_nonneg_left hm (by positivity))

theorem no_log_power_amplification (a : ℝ) (ha : a < 1) :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      c * N * squareMax N * Real.exp (-(Real.log (N : ℝ)) ^ a) ≤
        squareMax (N ^ 2) := by
  rintro ⟨c, hc, he⟩
  obtain ⟨N, hlt, hle⟩ := ((frequently_log_power_loss a c ha hc).and_eventually he).exists
  exact (not_lt_of_ge hle) hlt

#print axioms squareDensity_exp_upper
#print axioms half_power_exp_bound
#print axioms eventually_log_power_le_primorial
#print axioms no_log_power_amplification
#print axioms frequently_primorial_loss
#print axioms frequently_log_power_loss
end Erdos773.Amplification
