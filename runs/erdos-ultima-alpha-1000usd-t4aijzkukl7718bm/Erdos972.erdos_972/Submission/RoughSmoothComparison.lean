import Submission.RoughSmoothLowerBound

/-!
Comparison of the actual rough-output smooth lower envelope with the
least-factor smoothing comparison budget. These estimates do not prove
positive genuine prime correlation.
-/
namespace Erdos972RoughSmoothComparison

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972RoughSmoothLowerBound Erdos972PrimeLeastFactorScales
open Erdos972PrimePowerError Erdos972EfficientSieveScale
open Erdos972GrowingCoprimeCandidates Erdos972LeastFactorCutoff

set_option maxHeartbeats 2000000
set_option exponentiation.threshold 8192

noncomputable def layerTau (α : ℝ) (u : ℕ) : ℝ :=
  layerParameter α u * Real.log (fastRoot u)

lemma layerTau_pos {α : ℝ} {u : ℕ} (hZ : 2 ≤ fastRoot u) :
    0 < layerTau α u :=
  mul_pos (layerParameter_pos α u) (Real.log_pos (by exact_mod_cast hZ))

lemma roughParameter_layerTau {α : ℝ} {u : ℕ} (hZ : 2 ≤ fastRoot u) :
    roughParameter (layerTau α u) u = layerParameter α u := by
  have hz : Real.log (fastRoot u) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hZ)).ne'
  exact mul_div_cancel_right₀ _ hz

lemma layerTau_upper {α : ℝ} (hα : 1 ≤ α) {u : ℕ} (_hZ : 2 ≤ fastRoot u) :
    layerTau α u ≤ 1/(layerCount u+1)^2 := by
  have hZu : fastRoot u ≤ u :=
    (root64_le_self _).trans (root64_le_self u)
  have hn : fastRoot u ≤ floorMul α (u^6) :=
    hZu.trans ((Nat.le_pow (by decide : 0 < 6)).trans (self_le_floorMul hα _))
  have hl := Erdos972ExponentialSum.monotone_log_natCast hn
  dsimp only at hl
  have hL : 0 < 1+Real.log (floorMul α (u^6)) :=
    add_pos_of_pos_of_nonneg zero_lt_one (Real.log_natCast_nonneg _)
  have hJ : (0:ℝ) < layerCount u+1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  unfold layerTau layerParameter
  apply (le_div_iff₀ (sq_pos_of_pos hJ)).mpr
  field_simp
  linarith only [hl]

lemma layerTau_lower {α : ℝ} (hα : 1 ≤ α) {u : ℕ}
    (hZ : 2 ≤ fastRoot u) (hαZ : α ≤ fastRoot u) :
    1/(49155*(layerCount u+1)^2) ≤ layerTau α u := by
  have hZpos : (0:ℝ) < fastRoot u := by exact_mod_cast (by omega : 0 < fastRoot u)
  have hz : 0 < Real.log (fastRoot u) := Real.log_pos (by exact_mod_cast hZ)
  have hu : 0 < u := by
    have hh := (root64_le_self (Erdos972PolynomialRowScales.root64 u)).trans (root64_le_self u)
    change fastRoot u ≤ u at hh
    omega
  have hn : 0 < floorMul α (u^6) := floorMul_pos hα (Nat.pow_pos hu)
  have hl := Real.log_le_log (Nat.cast_pos.mpr hn)
    (Nat.cast_le.mpr (fast_floor_output_power_bound hαZ hZ le_rfl))
  rw [Nat.cast_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hzhalf : (1/2:ℝ) ≤ Real.log (fastRoot u) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 2) (Nat.cast_le.mpr hZ)
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, Real.log_two_gt_d9]
  have hL : 0 < 1+Real.log (floorMul α (u^6)) :=
    add_pos_of_pos_of_nonneg zero_lt_one (Real.log_natCast_nonneg _)
  have hJ : (0:ℝ) < layerCount u+1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  unfold layerTau layerParameter
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 49155) (sq_pos_of_pos hJ))).mpr
  field_simp
  nlinarith only [hl, hzhalf]

lemma layerTau_admissible {α : ℝ} (hα : 1 ≤ α) {u : ℕ}
    (hZ : 2 ≤ fastRoot u) (hJ : 1 ≤ layerCount u) :
    0 < layerTau α u ∧ layerTau α u ≤ 1/2 := by
  refine ⟨layerTau_pos hZ, (layerTau_upper hα hZ).trans ?_⟩
  have hh : (1:ℝ) ≤ layerCount u := by exact_mod_cast hJ
  have hj : (0:ℝ) < (layerCount u+1)^2 :=
    sq_pos_of_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)
  apply (div_le_iff₀ hj).mpr
  nlinarith only [hh, sq_nonneg (layerCount u:ℝ)]

lemma coefficient_cancel (k : ℕ) {τ C : ℝ} (hτ : τ ≠ 0) (hC : C ≠ 0) :
    (τ/2)^(k+1)/(8195*τ*C) = τ^k/((2:ℝ)^(k+1)*8195*C) := by
  rw [div_pow, pow_succ τ]
  field_simp

noncomputable def roughNormalization : ℝ :=
  (2:ℝ)^49153 * 8195 * Erdos972EfficientPrimeAlmostPrime.roughConstant

lemma roughNormalization_one_le : 1 ≤ roughNormalization := by
  have hpow (k : ℕ) : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hC : 1 ≤ Erdos972EfficientPrimeAlmostPrime.roughConstant := by
    unfold Erdos972EfficientPrimeAlmostPrime.roughConstant
      Erdos972SelbergMajorantSize.majorantCap
    exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (hpow _) )
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hpow _) (by norm_num)) hC

lemma roughNormalization_pos : 0 < roughNormalization :=
  lt_of_lt_of_le zero_lt_one roughNormalization_one_le

lemma roughSmoothCoefficient_eq {τ : ℝ} (hτ : 0 < τ) :
    roughSmoothCoefficient τ = τ^49152/roughNormalization :=
  coefficient_cancel 49152 hτ.ne' Erdos972EfficientPrimeAlmostPrime.roughConstant_pos.ne'


lemma power_quotient_eq (k : ℕ) (C x D : ℝ) :
    (1/(C*x^2))^k/D = (1/(C^k*D))/x^(2*k) := by
  rw [div_pow, one_pow, mul_pow, ← pow_mul]
  ring

noncomputable def roughLayerCoefficient : ℝ :=
  1/((49155:ℝ)^49152*roughNormalization)

lemma roughLayerCoefficient_pos : 0 < roughLayerCoefficient :=
  div_pos zero_lt_one (mul_pos (pow_pos (by norm_num) _) roughNormalization_pos)

/-- The new lower-envelope coefficient decays as the 98304th power
of the number of layers. The upper inequality concerns this coefficient,
not the actual smoothed correlation. -/
theorem layer_coefficient_bounds {α : ℝ} (hα : 1 ≤ α) {u : ℕ}
    (hZ : 2 ≤ fastRoot u) (hαZ : α ≤ fastRoot u) :
    roughLayerCoefficient/(layerCount u+1)^98304 ≤
        roughSmoothCoefficient (layerTau α u) ∧
      roughSmoothCoefficient (layerTau α u) ≤ 1/(layerCount u+1)^98304 := by
  have hτ := layerTau_pos (α := α) hZ
  have hl := layerTau_lower hα hZ hαZ
  have hu := layerTau_upper hα hZ
  have hj : (0:ℝ) < layerCount u+1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  have hl0 : (0:ℝ) ≤ 1/(49155*(layerCount u+1)^2) :=
    le_of_lt (div_pos zero_lt_one (mul_pos (by norm_num) (sq_pos_of_pos hj)))
  have hlo := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ hl0 hl 49152) roughNormalization_pos.le
  have hup := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ hτ.le hu 49152) roughNormalization_pos.le
  rw [roughSmoothCoefficient_eq hτ]
  constructor
  · have he := power_quotient_eq 49152 (49155:ℝ) (layerCount u+1) roughNormalization
    change (1/(49155*((layerCount u:ℝ)+1)^2))^49152/roughNormalization =
      roughLayerCoefficient/((layerCount u:ℝ)+1)^98304 at he
    rw [he] at hlo
    exact hlo
  · apply hup.trans
    have he := power_quotient_eq 49152 (1:ℝ) (layerCount u+1) roughNormalization
    simp only [one_mul, one_pow] at he
    rw [he]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hj.le _)
    exact (div_le_one roughNormalization_pos).mpr roughNormalization_one_le

/-- The established rough-output coefficient is strictly smaller than
the available mixed-comparison budget at every admissible scale. This
compares the two proven envelopes, not the actual error. -/
theorem layer_lower_envelope_lt_error_budget {α : ℝ} (hα : 1 ≤ α) {u : ℕ}
    (hZ : 2 ≤ fastRoot u) (hαZ : α ≤ fastRoot u) :
    roughSmoothCoefficient (layerTau α u)*(u:ℝ)^6 <
      100000*(u:ℝ)^6/(layerCount u+1) := by
  have hZu : fastRoot u ≤ u :=
    (root64_le_self _).trans (root64_le_self u)
  have hu : 0 < u := by omega
  have hx : (0:ℝ) < (u:ℝ)^6 := pow_pos (Nat.cast_pos.mpr hu) _
  have hj : (1:ℝ) ≤ layerCount u+1 := by
    linarith only [Nat.cast_nonneg (α := ℝ) (layerCount u)]
  have hjpos : (0:ℝ) < layerCount u+1 := zero_lt_one.trans_le hj
  have hc := (layer_coefficient_bounds hα hZ hαZ).2
  have hpow : (layerCount u:ℝ)+1 ≤ (layerCount u+1)^98304 := by
    simpa only [pow_one] using pow_le_pow_right₀ hj (show 1 ≤ 98304 by decide)
  have hcoeff : roughSmoothCoefficient (layerTau α u) ≤ 1/(layerCount u+1) :=
    hc.trans (div_le_div_of_nonneg_left zero_le_one hjpos hpow)
  have hstrict : (1:ℝ)/(layerCount u+1) < 100000/(layerCount u+1) :=
    (div_lt_div_iff_of_pos_right hjpos).mpr (by norm_num)
  have hh := mul_lt_mul_of_pos_right (hcoeff.trans_lt hstrict) hx
  simpa only [div_mul_eq_mul_div] using hh

/-- At arbitrarily large actual rough-output scales, the new lower bound
holds at precisely the least-factor comparison parameter. No claim is
made here that a separately chosen moment scale is the same scale. -/
theorem exists_layerParameter_rough_lower {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < layerCount u ∧
      2 ≤ fastRoot u ∧ α ≤ fastRoot u ∧
      roughLayerCoefficient*(u:ℝ)^6/(layerCount u+1)^98304 ≤
        mixedPrimeSmooth (layerParameter α u) α (u^6) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (layerCount_tendsto.eventually_gt_atTop (max B 1))
  obtain ⟨u, hu, hZ, hαZ, hs⟩ := exists_rough_smooth_scale hα hI (max B T)
  have huT : T ≤ u := (le_max_right _ _).trans hu.le
  have hJ := hT u huT
  have hJ1 : 1 ≤ layerCount u := (le_max_right B 1).trans hJ.le
  have ha := layerTau_admissible hα.le hZ hJ1
  have hh := hs (layerTau α u) ha.1 ha.2
  rw [roughParameter_layerTau hZ] at hh
  refine ⟨u, (le_max_left _ _).trans_lt hu, (le_max_left _ _).trans_lt hJ,
    hZ, hαZ, ?_⟩
  have hl := mul_le_mul_of_nonneg_right (layer_coefficient_bounds hα.le hZ hαZ).1
    (pow_nonneg (Nat.cast_nonneg u) 6)
  apply le_trans _ hh
  simpa only [div_mul_eq_mul_div] using hl

#print axioms layer_coefficient_bounds
#print axioms layer_lower_envelope_lt_error_budget
#print axioms exists_layerParameter_rough_lower

end Erdos972RoughSmoothComparison
