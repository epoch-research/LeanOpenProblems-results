import Submission.HardCubicFlexiblePrimeBound

/-! A strict improvement of the verified 5/2 exponent, retaining the full
logarithmic saving. The exponent 249999/100000 is still greater than two;
this file does not settle the original conjecture. -/
namespace Erdos970.HardCubicFlexible
open FiniteSelberg Real

lemma scale_log_pos (e t : ℕ) (ht : 0 < t) :
    0 < log ((hardCubicCutoffScale * t ^ e : ℕ) : ℝ) := by
  apply log_pos
  have hD := hardCubicCutoffScale_ge
  have hte : 1 ≤ t ^ e := one_le_pow₀ ht
  have hh : 1 < hardCubicCutoffScale * t ^ e := by nlinarith
  exact_mod_cast hh

theorem isJacobsthalBound_power_ratio_log (e f : ℕ) (hE : 0 < e) (hEF : e ≤ f)
    (hRatio : log ((f : ℝ) / e) ≤ 287697 / 1000000)
    (k t m : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ f)
    (hm : hardCubicBoundConstant * (t : ℝ) ^ (f + 2 * e) <
      (m : ℝ) * log ((hardCubicCutoffScale * t ^ e : ℕ) : ℝ)) :
    IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hcard, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  obtain ⟨j, hj, havoid⟩ := prime_survivor_power_ratio_log P hP e f hE hEF hRatio
    t ht (hcard.trans hkt) r m hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

lemma cardinality_log_le_scale_log (e f : ℕ) (hFE : f ≤ 2 * e)
    (k t : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ f) :
    log ((k : ℝ) + 2) ≤ 2 * log ((hardCubicCutoffScale * t ^ e : ℕ) : ℝ) := by
  let R := hardCubicCutoffScale * t ^ e
  have hD := hardCubicCutoffScale_ge
  have htf : t ^ f ≤ t ^ (2 * e) := Nat.pow_le_pow_right ht hFE
  have hte : 1 ≤ t ^ (2 * e) := one_le_pow₀ ht
  have hDsq : 3 ≤ hardCubicCutoffScale ^ 2 := by nlinarith
  have hh : k + 2 ≤ R ^ 2 := by
    have he : R ^ 2 = hardCubicCutoffScale ^ 2 * t ^ (2 * e) := by
      dsimp [R]
      rw [mul_pow, ← pow_mul, Nat.mul_comm e 2]
    rw [he]
    nlinarith [Nat.mul_le_mul_right (t ^ (2 * e)) hDsq]
  have hlog : log ((k : ℝ) + 2) ≤ log ((R : ℝ) ^ 2) := by
    apply log_le_log (by positivity)
    exact_mod_cast hh
  simpa only [log_pow, Nat.cast_ofNat] using hlog

lemma jacobsthal_mul_scale_log (e f : ℕ) (hE : 0 < e) (hEF : e ≤ f)
    (hRatio : log ((f : ℝ) / e) ≤ 287697 / 1000000)
    (k t : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ f) :
    (jacobsthalFunction k : ℝ) * log ((hardCubicCutoffScale * t ^ e : ℕ) : ℝ) ≤
      hardCubicBoundConstant * (t : ℝ) ^ (f + 2 * e) +
        log ((hardCubicCutoffScale * t ^ e : ℕ) : ℝ) := by
  let L := log ((hardCubicCutoffScale * t ^ e : ℕ) : ℝ)
  let x := hardCubicBoundConstant * (t : ℝ) ^ (f + 2 * e) / L
  let m := ⌊x⌋₊ + 1
  have hL : 0 < L := scale_log_pos e t ht
  have hx : 0 ≤ x := div_nonneg (mul_nonneg hardCubicBoundConstant_pos.le (by positivity)) hL.le
  have hxm : x < (m : ℝ) := by simpa only [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have hm : hardCubicBoundConstant * (t : ℝ) ^ (f + 2 * e) < (m : ℝ) * L :=
    (div_lt_iff₀ hL).mp hxm
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_power_ratio_log e f hE hEF hRatio k t m ht hkt hm)
  have hmupper : (m : ℝ) ≤ x + 1 := by
    dsimp [m]
    push_cast
    exact add_le_add (Nat.floor_le hx) le_rfl
  have hupper := mul_le_mul_of_nonneg_right
    ((show (jacobsthalFunction k : ℝ) ≤ m by exact_mod_cast hj).trans hmupper) hL.le
  have he : (x + 1) * L = hardCubicBoundConstant * (t : ℝ) ^ (f + 2 * e) + L := by
    dsimp [x]
    field_simp
  rwa [he] at hupper

lemma jacobsthal_mul_log_envelope (e f : ℕ) (hE : 0 < e) (hEF : e ≤ f)
    (hFE : f ≤ 2 * e) (hRatio : log ((f : ℝ) / e) ≤ 287697 / 1000000)
    (k t : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ f) :
    (jacobsthalFunction k : ℝ) * log ((k : ℝ) + 2) ≤
      (2 * (hardCubicBoundConstant + hardCubicCutoffScale)) * (t : ℝ) ^ (f + 2 * e) := by
  let L := log ((hardCubicCutoffScale * t ^ e : ℕ) : ℝ)
  have hL : 0 < L := scale_log_pos e t ht
  have hR : (0 : ℝ) < (hardCubicCutoffScale * t ^ e : ℕ) := by
    exact_mod_cast (Nat.mul_pos (show 0 < hardCubicCutoffScale by have := hardCubicCutoffScale_ge; omega)
      (Nat.pow_pos ht))
  have hlog : L ≤ (hardCubicCutoffScale : ℝ) * (t : ℝ) ^ (f + 2 * e) := by
    have h0 := log_le_sub_one_of_pos hR
    have htp := Nat.pow_le_pow_right ht (show e ≤ f + 2 * e by omega)
    have hh : (hardCubicCutoffScale * t ^ e : ℕ) ≤ hardCubicCutoffScale * t ^ (f + 2 * e) :=
      Nat.mul_le_mul_left _ htp
    have hhR : ((hardCubicCutoffScale * t ^ e : ℕ) : ℝ) ≤
        (hardCubicCutoffScale : ℝ) * (t : ℝ) ^ (f + 2 * e) := by exact_mod_cast hh
    dsimp only [L]
    linarith only [h0, hhR]
  have hl := jacobsthal_mul_scale_log e f hE hEF hRatio k t ht hkt
  have hc := mul_le_mul_of_nonneg_left (cardinality_log_le_scale_log e f hFE k t ht hkt)
    (Nat.cast_nonneg (jacobsthalFunction k))
  change (jacobsthalFunction k : ℝ) * L ≤ hardCubicBoundConstant * (t : ℝ) ^ (f + 2 * e) + L at hl
  change (jacobsthalFunction k : ℝ) * log ((k : ℝ) + 2) ≤
    (jacobsthalFunction k : ℝ) * (2 * L) at hc
  nlinarith only [hl, hc, hlog]

lemma exists_power_envelope (k f : ℕ) (hk : 0 < k) (hf : 0 < f) :
    ∃ t : ℕ, 0 < t ∧ k ≤ t ^ f ∧ t ^ f ≤ 2 ^ f * k := by
  have hex : ∃ t : ℕ, k ≤ t ^ f := ⟨k, Nat.le_self_pow hf.ne' k⟩
  let t := Nat.find hex
  have hkt : k ≤ t ^ f := Nat.find_spec hex
  have ht : 0 < t := by
    by_contra hn
    have heq : t = 0 := by omega
    simp only [heq, zero_pow hf.ne'] at hkt
    omega
  refine ⟨t, ht, hkt, ?_⟩
  by_cases ht1 : t = 1
  · rw [ht1, one_pow]
    exact hk.trans_le (Nat.le_mul_of_pos_left k (by positivity))
  · have hpred : (t - 1) ^ f < k := by
      have hh := Nat.find_min hex (show t - 1 < t by omega)
      omega
    have hh := Nat.pow_le_pow_left (show t ≤ 2 * (t - 1) by omega) f
    rw [Nat.mul_pow] at hh
    exact hh.trans (Nat.mul_le_mul_left _ hpred.le)

lemma power_envelope_rpow_le (k t f d : ℕ) (hf : 0 < f) (htk : t ^ f ≤ 2 ^ f * k) :
    (t : ℝ) ^ d ≤ (2 : ℝ) ^ d * (k : ℝ) ^ ((d : ℝ) / f) := by
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  have hR : (t : ℝ) ^ f ≤ (2 : ℝ) ^ f * k := by exact_mod_cast htk
  have hh := rpow_le_rpow (pow_nonneg (Nat.cast_nonneg t) f) hR
    (show 0 ≤ (d : ℝ) / f by positivity)
  have hid (x : ℝ) (hx : 0 ≤ x) : (x ^ f) ^ ((d : ℝ) / f) = x ^ d := by
    rw [← rpow_natCast x f, ← rpow_mul hx]
    have he : (f : ℝ) * ((d : ℝ) / f) = d := by field_simp
    rw [he, rpow_natCast]
  rw [hid _ (Nat.cast_nonneg t), mul_rpow (by positivity) (Nat.cast_nonneg k),
    hid 2 (by norm_num)] at hh
  exact hh

/-- A uniform bound for every admissible rational cutoff ratio. -/
theorem exists_power_ratio_div_log_bound (e f : ℕ) (hE : 0 < e) (hEF : e ≤ f)
    (hFE : f ≤ 2 * e) (hRatio : log ((f : ℝ) / e) ≤ 287697 / 1000000) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤
        C * (k : ℝ) ^ (((f + 2 * e : ℕ) : ℝ) / f) / log ((k : ℝ) + 2) := by
  let C : ℝ := (2 * (hardCubicBoundConstant + hardCubicCutoffScale)) * 2 ^ (f + 2 * e)
  have hbase : 0 < 2 * (hardCubicBoundConstant + hardCubicCutoffScale) := by
    have := hardCubicBoundConstant_pos
    positivity
  refine ⟨C, by dsimp [C]; positivity, fun k hk => ?_⟩
  obtain ⟨t, ht, hkt, htk⟩ := exists_power_envelope k f hk (by omega)
  have hh := (jacobsthal_mul_log_envelope e f hE hEF hFE hRatio k t ht hkt).trans
    (mul_le_mul_of_nonneg_left (power_envelope_rpow_le k t f (f + 2 * e) (by omega) htk) hbase.le)
  apply (le_div_iff₀ (log_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith))).mpr
  simpa only [C, mul_assoc] using hh

end Erdos970.HardCubicFlexible
namespace Erdos970
open Real

/-- A strictly sub-5/2 unrestricted bound. Its exponent is 2.49999, NOT 2. -/
theorem exists_below_five_halves_div_log_bound :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤
        C * (k : ℝ) ^ ((249999 : ℝ) / 100000) / log ((k : ℝ) + 2) := by
  have hh := HardCubicFlexible.exists_power_ratio_div_log_bound 149999 200000
    (by norm_num) (by norm_num) (by norm_num) WeightedMertens.log_improved_cubic_ratio
  norm_num at hh
  exact hh

#print axioms HardCubicFlexible.exists_power_ratio_div_log_bound
#print axioms exists_below_five_halves_div_log_bound
end Erdos970
