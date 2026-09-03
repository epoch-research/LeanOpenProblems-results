import Submission.SelbergSoftEnergy

/-! Uniform first and second logarithmic moments for arbitrary finite prime sets.
The primes need not be initial primes or bounded in size. -/
namespace Erdos970.WeightedMertens
open Finset Real

lemma log_div_le_of_le {z x : ℝ} (hz : 0 < z) (hzx : z ≤ x) (hlz : 1 ≤ log z) :
    log x / x ≤ log z / z := by
  have hx : 0 < x := hz.trans_le hzx
  have ht : 1 ≤ x / z := (le_div_iff₀ hz).mpr (by simpa using hzx)
  have ht0 : 0 < x / z := div_pos hx hz
  have hl := log_le_sub_one_of_pos ht0
  rw [log_div hx.ne' hz.ne'] at hl
  have he : x / z * z = x := div_mul_cancel₀ _ hz.ne'
  apply (div_le_div_iff₀ hx hz).mpr
  nlinarith

lemma log_sq_div_le_of_le {z x : ℝ} (hz : 0 < z) (hzx : z ≤ x) (hlz : 2 ≤ log z) :
    log x ^ 2 / x ≤ log z ^ 2 / z := by
  have hx : 0 < x := hz.trans_le hzx
  have ht : 1 ≤ x / z := (le_div_iff₀ hz).mpr (by simpa using hzx)
  let y := sqrt (x / z)
  have hy0 : 0 ≤ y := sqrt_nonneg _
  have hy2 : y ^ 2 = x / z := sq_sqrt (by positivity)
  have hy : 1 ≤ y := by nlinarith
  have hly := log_le_sub_one_of_pos (by linarith : 0 < y)
  have he : log y = (log x - log z) / 2 := by
    dsimp [y]
    rw [log_sqrt (by positivity), log_div hx.ne' hz.ne']
  rw [he] at hly
  have hlx : 0 ≤ log x := (by linarith : 0 ≤ log z).trans (log_le_log hz hzx)
  have hlin : log x ≤ log z * y := by nlinarith
  have hsq : log x ^ 2 ≤ log z ^ 2 * (x / z) := by
    have := mul_nonneg (by linarith : 0 ≤ log z) hy0
    nlinarith [sq_le_sq₀ hlx this |>.mpr hlin]
  have hmul := mul_le_mul_of_nonneg_right hsq hz.le
  have he' : x / z * z = x := div_mul_cancel₀ _ hz.ne'
  apply (div_le_div_iff₀ hx hz).mpr
  nlinarith only [hmul, he']

lemma two_le_log_of_sixty_four_le {z : ℝ} (hz : 64 ≤ z) : 2 ≤ log z := by
  have hl2 : (1 / 2 : ℝ) ≤ log 2 := by
    have hh := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hh := log_le_log (by norm_num : (0 : ℝ) < 64) hz
  have he : log (64 : ℝ) = 6 * log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow]
    norm_num
  rw [he] at hh
  linarith

lemma prime_small_log_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ) (hz : 0 < z) :
    (∑ p ∈ P.filter (fun p => p ≤ z), log p / p) ≤ log z + log 4 := by
  apply (sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (upper_bound z hz)
  · intro p hp
    exact mem_primes.mpr ⟨hP p (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  · intro p hp hnot
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_primes.mp hp).1.one_le
    exact div_nonneg (log_nonneg hp1) (Nat.cast_nonneg _)

/-- Both moment bounds keep a coefficient just above one, uniformly even when
some of the selected primes are arbitrarily large. -/
theorem prime_log_moments (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ) (hz : 64 ≤ z) (hsize : 64 * P.card ≤ z) :
    (∑ p ∈ P, log p / p) ≤ (65 / 64) * (log z + log 4) ∧
    (∑ p ∈ P, log p ^ 2 / p) ≤ (65 / 64) * (log z + log 4) ^ 2 := by
  have hzR : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hlog : 2 ≤ log (z : ℝ) := two_le_log_of_sixty_four_le (by exact_mod_cast hz)
  have hlog4 : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  have hsizeR : 64 * (P.card : ℝ) ≤ z := by exact_mod_cast hsize
  have hfirst := prime_small_log_sum P hP z (by omega)
  have hsecond : (∑ p ∈ P.filter (fun p => p ≤ z), log p ^ 2 / p) ≤
      (log z + log 4) ^ 2 := by
    calc
      _ ≤ log z * (∑ p ∈ P.filter (fun p => p ≤ z), log p / p) := by
        rw [mul_sum]
        apply sum_le_sum
        intro p hp
        have hpp := hP p (mem_filter.mp hp).1
        have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
        have hplog : log (p : ℝ) ≤ log z := log_le_log hpR (by exact_mod_cast (mem_filter.mp hp).2)
        have hh := mul_le_mul_of_nonneg_right hplog (log_nonneg hp1)
        apply (div_le_iff₀ hpR).mpr
        have he : log z * (log p / p) * p = log z * log p := by field_simp
        rw [he]
        nlinarith only [hh]
      _ ≤ log z * (log z + log 4) := mul_le_mul_of_nonneg_left hfirst (by linarith)
      _ ≤ _ := by nlinarith
  have htail (f : ℕ → ℝ) (v : ℝ) (hv : 0 ≤ v)
      (hf : ∀ p ∈ P, z < p → f p ≤ v / z) :
      (∑ p ∈ P.filter (fun p => ¬p ≤ z), f p) ≤ v / 64 := by
    calc
      _ ≤ ∑ _p ∈ P.filter (fun p => ¬p ≤ z), v / z :=
        sum_le_sum (fun p hp => hf p (mem_filter.mp hp).1 (by have := (mem_filter.mp hp).2; omega))
      _ = ((P.filter (fun p => ¬p ≤ z)).card : ℝ) * (v / z) := by simp
      _ ≤ (P.card : ℝ) * (v / z) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_filter_le P (fun p => ¬p ≤ z)) (div_nonneg hv hzR.le)
      _ ≤ v / 64 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
        apply (mul_le_mul_iff_right₀ hzR).mp
        have he : z * ((P.card : ℝ) * (v / z) * 64) = (64 * (P.card : ℝ)) * v := by field_simp
        rw [he]
        nlinarith only [mul_le_mul_of_nonneg_right hsizeR hv]
  have ht1 := htail (fun p => log p / p) (log z) (by linarith)
    (fun p hp hzp => log_div_le_of_le hzR (by exact_mod_cast hzp.le) (by linarith))
  have ht2 := htail (fun p => log p ^ 2 / p) (log z ^ 2) (sq_nonneg _)
    (fun p hp hzp => log_sq_div_le_of_le hzR (by exact_mod_cast hzp.le) hlog)
  have hs1 := sum_filter_add_sum_filter_not P (fun p => p ≤ z) (fun p => log p / p)
  have hs2 := sum_filter_add_sum_filter_not P (fun p => p ≤ z) (fun p => log p ^ 2 / p)
  constructor
  · linarith
  · have hh : log z ^ 2 ≤ (log z + log 4) ^ 2 := by nlinarith
    linarith

#print axioms prime_log_moments
end Erdos970.WeightedMertens
