import Submission.HardCubicLogPrimeBound
import Submission.HardCubicPowerBound

/-! An unconditional logarithmic saving in the 5/2 upper bound. The resulting
k^(5/2)/log(k+2) bound is still weaker than the quadratic conjecture. -/
namespace Erdos970
open FiniteSelberg Real

lemma hardCubicScale_log_pos (t : ℕ) (ht : 0 < t) :
    0 < log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ) := by
  apply log_pos
  have hD := hardCubicCutoffScale_ge
  have ht3 : 1 ≤ t ^ 3 := one_le_pow₀ ht
  have hh : 1 < hardCubicCutoffScale * t ^ 3 := by nlinarith
  exact_mod_cast hh

/-- The logarithmically sharper interval length criterion. -/
theorem isJacobsthalBound_three_quarters_log (k t m : ℕ)
    (ht : 0 < t) (hkt : k ≤ t ^ 4)
    (hm : hardCubicBoundConstant * (t : ℝ) ^ 10 <
      (m : ℝ) * log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ)) :
    IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hcard, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  obtain ⟨j, hj, havoid⟩ := prime_survivor_three_quarters_log P hP t ht
    (hcard.trans hkt) r m hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

lemma cardinality_log_le_scale_log (k t : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ 4) :
    log ((k : ℝ) + 2) ≤ 2 * log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ) := by
  let R := hardCubicCutoffScale * t ^ 3
  have hD := hardCubicCutoffScale_ge
  have ht46 : t ^ 4 ≤ t ^ 6 := Nat.pow_le_pow_right ht (by omega)
  have ht6 : 1 ≤ t ^ 6 := one_le_pow₀ ht
  have hDsq : 3 ≤ hardCubicCutoffScale ^ 2 := by nlinarith
  have hh : k + 2 ≤ R ^ 2 := by
    have he : R ^ 2 = hardCubicCutoffScale ^ 2 * t ^ 6 := by dsimp [R]; ring
    rw [he]
    nlinarith [Nat.mul_le_mul_right (t ^ 6) hDsq]
  have hlog : log ((k : ℝ) + 2) ≤ log ((R : ℝ) ^ 2) := by
    apply log_le_log (by positivity)
    exact_mod_cast hh
  simpa only [log_pow, Nat.cast_ofNat] using hlog

/-- Exact floor rounding costs only one extra copy of the scale logarithm. -/
lemma jacobsthal_mul_scale_log (k t : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ 4) :
    (jacobsthalFunction k : ℝ) * log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ) ≤
      hardCubicBoundConstant * (t : ℝ) ^ 10 +
        log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ) := by
  let L := log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ)
  let x := hardCubicBoundConstant * (t : ℝ) ^ 10 / L
  let m := ⌊x⌋₊ + 1
  have hL : 0 < L := hardCubicScale_log_pos t ht
  have hx : 0 ≤ x := div_nonneg (mul_nonneg hardCubicBoundConstant_pos.le (by positivity)) hL.le
  have hxm : x < (m : ℝ) := by simpa only [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have hm : hardCubicBoundConstant * (t : ℝ) ^ 10 < (m : ℝ) * L :=
    (div_lt_iff₀ hL).mp hxm
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_three_quarters_log k t m ht hkt hm)
  have hmupper : (m : ℝ) ≤ x + 1 := by
    dsimp [m]
    push_cast
    exact add_le_add (Nat.floor_le hx) le_rfl
  have hupper := mul_le_mul_of_nonneg_right
    ((show (jacobsthalFunction k : ℝ) ≤ m by exact_mod_cast hj).trans hmupper) hL.le
  have he : (x + 1) * L = hardCubicBoundConstant * (t : ℝ) ^ 10 + L := by
    dsimp [x]
    field_simp
  rwa [he] at hupper

lemma jacobsthal_mul_log_envelope (k t : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ 4) :
    (jacobsthalFunction k : ℝ) * log ((k : ℝ) + 2) ≤
      (2 * (hardCubicBoundConstant + hardCubicCutoffScale)) * (t : ℝ) ^ 10 := by
  let L := log ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ)
  have hL : 0 < L := hardCubicScale_log_pos t ht
  have hR : (0 : ℝ) < (hardCubicCutoffScale * t ^ 3 : ℕ) := by
    exact_mod_cast (Nat.mul_pos (show 0 < hardCubicCutoffScale by have := hardCubicCutoffScale_ge; omega)
      (Nat.pow_pos ht))
  have hlog : L ≤ (hardCubicCutoffScale : ℝ) * (t : ℝ) ^ 10 := by
    have h0 := log_le_sub_one_of_pos hR
    have ht310 := Nat.pow_le_pow_right ht (show 3 ≤ 10 by omega)
    have hh : (hardCubicCutoffScale * t ^ 3 : ℕ) ≤ hardCubicCutoffScale * t ^ 10 :=
      Nat.mul_le_mul_left _ ht310
    have hhR : ((hardCubicCutoffScale * t ^ 3 : ℕ) : ℝ) ≤
        (hardCubicCutoffScale : ℝ) * (t : ℝ) ^ 10 := by exact_mod_cast hh
    dsimp only [L]
    linarith only [h0, hhR]
  have hl := jacobsthal_mul_scale_log k t ht hkt
  have hc := mul_le_mul_of_nonneg_left (cardinality_log_le_scale_log k t ht hkt)
    (Nat.cast_nonneg (jacobsthalFunction k))
  change (jacobsthalFunction k : ℝ) * L ≤ hardCubicBoundConstant * (t : ℝ) ^ 10 + L at hl
  change (jacobsthalFunction k : ℝ) * log ((k : ℝ) + 2) ≤
    (jacobsthalFunction k : ℝ) * (2 * L) at hc
  nlinarith only [hl, hc, hlog]

lemma fourth_envelope_tenth_le (k t : ℕ) (htk : t ^ 4 ≤ 16 * k) :
    (t : ℝ) ^ 10 ≤ 1024 * (k : ℝ) ^ ((5 : ℝ) / 2) := by
  have hh : ((t : ℝ) ^ 4) ^ 5 ≤ (16 * (k : ℝ)) ^ 5 := by
    exact_mod_cast Nat.pow_le_pow_left htk 5
  have he : ((k : ℝ) ^ ((5 : ℝ) / 2)) ^ 2 = (k : ℝ) ^ 5 := by
    rw [← rpow_natCast _ 2, ← rpow_mul (Nat.cast_nonneg k)]
    norm_num
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (t : ℝ) ^ 10)
    (by positivity : 0 ≤ 1024 * (k : ℝ) ^ ((5 : ℝ) / 2)) (by omega : 2 ≠ 0)).mp
  rw [mul_pow, he]
  nlinarith only [hh]

noncomputable def logFiveHalvesConstant : ℝ :=
  2048 * (hardCubicBoundConstant + hardCubicCutoffScale)

lemma logFiveHalvesConstant_pos : 0 < logFiveHalvesConstant := by
  unfold logFiveHalvesConstant
  have := hardCubicBoundConstant_pos
  positivity

/-- Unconditional 5/2 exponent with a full logarithmic saving. -/
theorem jacobsthalFunction_mul_log_le_five_halves (k : ℕ) (hk : 0 < k) :
    (jacobsthalFunction k : ℝ) * log ((k : ℝ) + 2) ≤
      logFiveHalvesConstant * (k : ℝ) ^ ((5 : ℝ) / 2) := by
  obtain ⟨t, ht, hkt, htk⟩ := exists_fourth_power_envelope k hk
  have hh := (jacobsthal_mul_log_envelope k t ht hkt).trans
    (mul_le_mul_of_nonneg_left (fourth_envelope_tenth_le k t htk)
      (show 0 ≤ 2 * (hardCubicBoundConstant + hardCubicCutoffScale) by
        have := hardCubicBoundConstant_pos
        positivity))
  convert hh using 1
  unfold logFiveHalvesConstant
  ring

/-- Existential form. The logarithmic denominator does not lower the power to 2. -/
theorem exists_five_halves_div_log_bound :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * (k : ℝ) ^ ((5 : ℝ) / 2) / log ((k : ℝ) + 2) := by
  refine ⟨logFiveHalvesConstant, logFiveHalvesConstant_pos, fun k hk => ?_⟩
  apply (le_div_iff₀ (log_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith))).mpr
  exact jacobsthalFunction_mul_log_le_five_halves k hk

#print axioms isJacobsthalBound_three_quarters_log
#print axioms jacobsthalFunction_mul_log_le_five_halves
#print axioms exists_five_halves_div_log_bound
end Erdos970
