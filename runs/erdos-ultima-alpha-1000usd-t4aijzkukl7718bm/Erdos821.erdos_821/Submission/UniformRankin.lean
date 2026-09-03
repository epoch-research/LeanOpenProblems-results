import Submission.Rankin

/-!
# A uniform Rankin estimate for inverse-totient multiplicities

This is an auxiliary upper bound, not a settlement of Erdős 821.
The quadratic dependence of the size threshold on the saving parameter is explicit.
-/

open Nat Filter
open scoped Classical

namespace Erdos821
open Sieve

lemma pseries_one_add_inv_le (k : ℕ) (hk : 0 < k) :
    (∑' a : ℕ, (a : ℝ) ^ (-(1 + 1 / (k : ℝ)))) ≤ 2 * k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let e : ℝ := 1 / (k : ℝ)
  let r : ℝ := (2 : ℝ) ^ (-e)
  have he : 0 < e := one_div_pos.mpr hkR
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos he)
  have hrpow : r ^ k = (1 / 2 : ℝ) := by
    dsimp [r, e]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    have hid : -(1 / (k : ℝ)) * k = -1 := by field_simp
    rw [hid]
    norm_num
  have hsumk : (∑ i ∈ Finset.range k, r ^ i) ≤ (k : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => pow_le_one₀ hr0 hr1.le)
      _ = _ := by simp
  have hgap : (1 : ℝ) / 2 ≤ (k : ℝ) * (1 - r) := by
    have h := mul_le_mul_of_nonneg_right hsumk (sub_nonneg.mpr hr1.le)
    rw [geom_sum_mul_neg, hrpow] at h
    linarith
  have hgeo : (1 - r)⁻¹ ≤ 2 * (k : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (sub_pos.mpr hr1)).mpr
    nlinarith
  apply (Real.tsum_le_of_sum_range_le
    (fun a => Real.rpow_nonneg (Nat.cast_nonneg a) _) ?_).trans hgeo
  intro N
  have hfmono : ∀ ⦃a b : ℕ⦄, 0 < a → a ≤ b →
      (b : ℝ) ^ (-(1 + e)) ≤ (a : ℝ) ^ (-(1 + e)) := by
    intro a b ha hab
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast ha)
      (by exact_mod_cast hab) (by linarith)
  have hcond := Finset.le_sum_condensed hfmono N
  have hterm (i : ℕ) :
      2 ^ i • (((2 ^ i : ℕ) : ℝ) ^ (-(1 + e))) = r ^ i := by
    rw [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      (2 : ℝ) ^ i * ((2 : ℝ) ^ i) ^ (-(1 + e)) =
          ((2 : ℝ) ^ i) ^ (1 - (1 + e)) := by
        rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_neg (by positivity)]
        ring
      _ = (2 : ℝ) ^ ((i : ℝ) * (1 - (1 + e))) :=
        (Real.rpow_natCast_mul (by norm_num) i _).symm
      _ = r ^ i := by
        dsimp [r]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have hgeomN : (∑ i ∈ Finset.range N, r ^ i) ≤ (1 - r)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    rw [geom_sum_mul_neg]
    linarith [pow_nonneg hr0 N]
  calc
    (∑ a ∈ Finset.range N, (a : ℝ) ^ (-(1 + 1 / (k : ℝ)))) ≤
        ∑ a ∈ Finset.range (2 ^ N), (a : ℝ) ^ (-(1 + e)) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.lt_two_pow_self.le)) (fun a _ _ => Real.rpow_nonneg (Nat.cast_nonneg a) _)
    _ ≤ (0 : ℝ) ^ (-(1 + e)) + ∑ i ∈ Finset.range N, 2 ^ i •
        (((2 ^ i : ℕ) : ℝ) ^ (-(1 + e))) := by simpa only [Nat.cast_zero] using hcond
    _ = ∑ i ∈ Finset.range N, r ^ i := by
      rw [Real.zero_rpow (by linarith : -(1 + e) ≠ 0), zero_add]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ ≤ _ := hgeomN

noncomputable def uniformRankinBase : ℝ :=
  (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

lemma uniformRankinBase_pos : 0 < uniformRankinBase := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

lemma smoothRankinConstant_one_add_inv_le (k : ℕ) (hk : 2 ≤ k) :
    smoothRankinConstant (1 - 1 / (k : ℝ)) (1 + 1 / (k : ℝ)) ≤
      2 * uniformRankinBase * k := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have he : 0 < 1 / (k : ℝ) := by positivity
  have hehalf : 1 / (k : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hkR
  have hfactor : (1 - (2 : ℝ) ^ (-(1 - 1 / (k : ℝ))))⁻¹ ≤ uniformRankinBase := by
    apply inv_anti₀
    · exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    · apply sub_le_sub_left
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hnonneg : 0 ≤ (1 - (2 : ℝ) ^ (-(1 - 1 / (k : ℝ))))⁻¹ := by
    apply inv_nonneg.mpr
    have h := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (show -(1 - 1 / (k : ℝ)) < 0 by linarith)
    linarith
  have hz := pseries_one_add_inv_le k (by omega)
  unfold smoothRankinConstant
  calc
    _ ≤ (1 - (2 : ℝ) ^ (-(1 - 1 / (k : ℝ))))⁻¹ * (2 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hz hnonneg
    _ ≤ uniformRankinBase * (2 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := by ring

/-- A uniform threshold: a saving of `2^k` is valid once the binary
logarithm of the input exceeds an absolute constant times `k^2`.
This yields a superlogarithmic saving, not a fixed power saving. -/
theorem exists_uniform_quadratic_rankin_threshold :
    ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ,
      2 ^ (C * k ^ 2) ≤ n →
      (g n : ℝ) ≤ (4 * totientRatioAverageConstant + 4) * n / (2 : ℝ) ^ k := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨B, hB⟩ := exists_nat_gt
    ((2 * Real.log 2 + 32 * uniformRankinBase) / Real.log 2)
  let C := B + 1
  have hconst : 2 * Real.log 2 + 32 * uniformRankinBase ≤ (C : ℝ) * Real.log 2 := by
    have h := (div_lt_iff₀ hlog).mp hB
    have hBC : (B : ℝ) ≤ C := by dsimp [C]; push_cast; linarith
    exact h.le.trans (mul_le_mul_of_nonneg_right hBC hlog.le)
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro k hk n hn
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  let e : ℝ := 1 / (k : ℝ)
  let s : ℝ := 1 - e
  let u : ℝ := 1 + e
  have he : 0 < e := by dsimp [e]; positivity
  have hehalf : e ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hkR
  have hs : 0 < s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hsu : s ≤ u := by dsimp [s, u]; linarith
  have hu : 1 < u := by dsimp [u]; linarith
  have hn0 : 0 < n := (pow_pos (by decide : 0 < (2 : ℕ)) _).trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let A : ℕ := 2 ^ k
  let y : ℕ := 2 ^ (2 * k)
  have hA : 0 < A := by dsimp [A]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hyA : (y : ℝ) = (A : ℝ) ^ 2 := by
    dsimp [y, A]
    push_cast
    rw [← pow_mul]
    congr 1
    omega
  have hyscale : (y : ℝ) ^ (u - s) = 16 := by
    dsimp [y]
    rw [Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have heq : ((2 * k : ℕ) : ℝ) * (u - s) = 4 := by
      dsimp [u, s, e]
      push_cast
      field_simp
      ring
    rw [heq]
    norm_num
  have hCbound : smoothRankinConstant s u ≤ 2 * uniformRankinBase * k :=
    smoothRankinConstant_one_add_inv_le k hk
  have hAid : (A : ℝ) ^ 2 = Real.exp ((2 * Real.log 2) * k) := by
    rw [← Real.rpow_natCast (A : ℝ) 2, Real.rpow_def_of_pos hAR]
    dsimp [A]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    congr 1
    ring
  have hbudget : (A : ℝ) ^ 2 *
      Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) ≤ (n : ℝ) ^ e := by
    calc
      _ = Real.exp ((2 * Real.log 2) * k + smoothRankinConstant s u * 16) := by
        rw [hAid, hyscale, Real.exp_add]
      _ ≤ Real.exp ((2 * Real.log 2 + 32 * uniformRankinBase) * k) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ Real.exp (((C : ℝ) * Real.log 2) * k) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hconst (Nat.cast_nonneg k))
      _ = (((2 ^ (C * k ^ 2) : ℕ) : ℝ)) ^ e := by
        rw [Real.rpow_def_of_pos (by positivity), Nat.cast_pow, Nat.cast_ofNat,
          Real.log_pow]
        congr 1
        dsimp [e]
        push_cast
        field_simp
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) he.le
  have hAs : (A : ℝ) ^ s ≤ A := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hA : (1 : ℝ) ≤ A) hs1
  have hsmall : ((A * n : ℕ) : ℝ) ^ s *
      Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) ≤ (n : ℝ) / A := by
    apply (le_div_iff₀ hAR).mpr
    rw [Nat.cast_mul, Real.mul_rpow hAR.le hnR.le]
    calc
      (A : ℝ) ^ s * (n : ℝ) ^ s *
          Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) * A ≤
          (A : ℝ) * (n : ℝ) ^ s *
          Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) * A := by
        gcongr
      _ = (n : ℝ) ^ s * ((A : ℝ) ^ 2 *
          Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s))) := by ring
      _ ≤ (n : ℝ) ^ s * (n : ℝ) ^ e :=
        mul_le_mul_of_nonneg_left hbudget (Real.rpow_nonneg hnR.le _)
      _ = n := by
        rw [← Real.rpow_add hnR, show s + e = 1 by dsimp [s]; ring, Real.rpow_one]
  calc
    (g n : ℝ) ≤ (4 * totientRatioAverageConstant / A + 3 * (A : ℝ) / y) * n +
        ((A * n : ℕ) : ℝ) ^ s *
          Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s)) :=
      g_le_linear_coeff_rankin n A y hn0 hA hy s u hs hsu hu
    _ ≤ (4 * totientRatioAverageConstant / A + 3 * (A : ℝ) / y) * n + (n : ℝ) / A :=
      add_le_add_right hsmall _
    _ = (4 * totientRatioAverageConstant + 4) * n / (A : ℝ) := by
      rw [hyA]
      field_simp
      ring
    _ = _ := by dsimp [A]; push_cast; rfl

/-- Direct square-root-logarithm saving, with one absolute positive integer
constant. The square root here is the natural-number floor square root. -/
theorem exists_sqrt_log_upper_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 2 ^ (4 * C) ≤ n →
      (g n : ℝ) ≤ (4 * totientRatioAverageConstant + 4) * n /
        (2 : ℝ) ^ (Nat.sqrt (Nat.log 2 n / C)) := by
  obtain ⟨C, hC, H⟩ := exists_uniform_quadratic_rankin_threshold
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hL : 4 * C ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hn
  have hdiv : 4 ≤ Nat.log 2 n / C := (Nat.le_div_iff_mul_le hC).mpr hL
  have hk : 2 ≤ Nat.sqrt (Nat.log 2 n / C) := Nat.le_sqrt.mpr (by omega)
  apply H _ hk n
  have hsq : Nat.sqrt (Nat.log 2 n / C) ^ 2 ≤ Nat.log 2 n / C := by
    simpa only [pow_two] using Nat.sqrt_le (Nat.log 2 n / C)
  have hbudget : C * Nat.sqrt (Nat.log 2 n / C) ^ 2 ≤ Nat.log 2 n :=
    (Nat.mul_le_mul_left C hsq).trans (Nat.mul_div_le _ _)
  have hn0 : n ≠ 0 := by have := (pow_pos (by decide : 0 < (2 : ℕ)) (4 * C)).trans_le hn; omega
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hbudget).trans
    (Nat.pow_log_le_self 2 hn0)

#print axioms pseries_one_add_inv_le
#print axioms smoothRankinConstant_one_add_inv_le
#print axioms exists_uniform_quadratic_rankin_threshold
#print axioms exists_sqrt_log_upper_bound

end Erdos821
