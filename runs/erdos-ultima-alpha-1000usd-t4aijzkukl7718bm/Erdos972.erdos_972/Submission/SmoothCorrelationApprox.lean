import Submission.SmoothMangoldtPositive
import Submission.DivisorEnergy

/-! A quantitative comparison between the smoothed divisor correlation and
the actual Mangoldt correlation. No lower bound for either is assumed or
proved by this comparison. -/
namespace Erdos972SmoothCorrelationApprox

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972PrimePowerError Erdos972DivisorEnergy

lemma card_divisors_eq_zeta_square (n : ℕ) :
    (n.divisors.card : ℝ) = ((ζ : ArithmeticFunction ℝ)^2) n := by
  rw [pow_two, coe_mul_zeta_apply]
  calc
    _ = ∑ d ∈ n.divisors, (1:ℝ) := by simp
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      simp only [natCoe_apply, zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne', Nat.cast_one]

lemma sum_card_divisors_le_log (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card:ℝ)) ≤ (N:ℝ)*(1+Real.log N) := by
  simp_rw [card_divisors_eq_zeta_square]
  exact (sum_zeta_pow_le 1 N).trans (by
    simpa only [pow_one] using mul_le_mul_of_nonneg_left
      (harmonic_le_one_add_log N) (Nat.cast_nonneg (α := ℝ) N))

lemma sum_output_divisors_le {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((floorMul α n).divisors.card:ℝ)) ≤
      (floorMul α N:ℝ)*(1+Real.log (floorMul α N)) := by
  classical
  calc
    _ = ∑ m ∈ (Ioc 0 N).image (floorMul α), (m.divisors.card:ℝ) := by
      rw [sum_image]
      exact (floorMul_strictMono hα).injective.injOn
    _ ≤ ∑ m ∈ Ioc 0 (floorMul α N), (m.divisors.card:ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hn).1,
          (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩
      · intro m _ _
        exact Nat.cast_nonneg _
    _ ≤ _ := sum_card_divisors_le_log _

lemma smooth_pair_error_bound {t L : ℝ} (ht : 0 < t) (hL : 0 ≤ L)
    (hsmall : t*L ≤ 1) (m n : ℕ) (hm : Real.log m ≤ L) (hn : Real.log n ≤ L) :
    |smoothMangoldt t m * smoothMangoldt t n - Λ m * Λ n| ≤
      t * L^3 * ((m.divisors.card:ℝ) + n.divisors.card) := by
  have herr (k : ℕ) (hk : Real.log k ≤ L) :
      |smoothMangoldt t k - Λ k| ≤ t * k.divisors.card * L^2 := by
    apply (smoothMangoldt_error_bound ht
      ((mul_le_mul_of_nonneg_left hk ht.le).trans hsmall)).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.log_natCast_nonneg k) hk 2) (by positivity)
  have hsmn : 0 ≤ smoothMangoldt t n := smoothMangoldt_nonneg ht n
  have hsmnL : smoothMangoldt t n ≤ L := (smoothMangoldt_le_log ht n).trans hn
  have hlm : Λ m ≤ L := vonMangoldt_le_log.trans hm
  have he : smoothMangoldt t m * smoothMangoldt t n - Λ m * Λ n =
      (smoothMangoldt t m - Λ m) * smoothMangoldt t n + Λ m * (smoothMangoldt t n - Λ n) := by ring
  rw [he]
  calc
    _ ≤ |(smoothMangoldt t m - Λ m) * smoothMangoldt t n| +
        |Λ m * (smoothMangoldt t n - Λ n)| := abs_add_le _ _
    _ = |smoothMangoldt t m - Λ m| * smoothMangoldt t n +
        Λ m * |smoothMangoldt t n - Λ n| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hsmn, abs_of_nonneg vonMangoldt_nonneg]
    _ ≤ (t*m.divisors.card*L^2)*L + L*(t*n.divisors.card*L^2) := by
      apply add_le_add
      · exact mul_le_mul (herr m hm) hsmnL hsmn (by positivity)
      · exact mul_le_mul hlm (herr n hn) (abs_nonneg _) hL
    _ = _ := by ring

noncomputable def smoothCorrelation (t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, smoothMangoldt t n * smoothMangoldt t (floorMul α n)

/-- The Taylor errors are summed with the mean divisor bound, rather than
using a worst-case divisor bound. This gives only logarithmic losses. -/
theorem smoothCorrelation_error_bound {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t)
    (N : ℕ) (hsmall : t * Real.log (floorMul α N) ≤ 1) :
    |smoothCorrelation t α N - mangoldtCorrelation α N| ≤
      t * ((N:ℝ) + floorMul α N) * (1+Real.log (floorMul α N))^4 := by
  by_cases hN : N = 0
  · simp [hN, smoothCorrelation, mangoldtCorrelation, floorMul]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let M := floorMul α N
  let L := Real.log M
  have hMpos : 0 < M := floorMul_pos hα hNpos
  have hL : 0 ≤ L := Real.log_natCast_nonneg M
  have hNM : N ≤ M := self_le_floorMul hα N
  have hlogNM : Real.log N ≤ L :=
    Real.log_le_log (Nat.cast_pos.mpr hNpos) (Nat.cast_le.mpr hNM)
  have hlocal (n : ℕ) (hn : n ∈ Ioc 0 N) :
      |smoothMangoldt t n * smoothMangoldt t (floorMul α n) - Λ n * Λ (floorMul α n)| ≤
        t * L^3 * ((n.divisors.card:ℝ) + (floorMul α n).divisors.card) := by
    apply smooth_pair_error_bound ht hL hsmall n (floorMul α n)
    · exact (log_input_le hn).trans hlogNM
    · apply Real.log_le_log (Nat.cast_pos.mpr (floorMul_pos hα (mem_Ioc.mp hn).1))
      exact Nat.cast_le.mpr ((floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2)
  have hsum : (∑ n ∈ Ioc 0 N, ((n.divisors.card:ℝ)+(floorMul α n).divisors.card)) ≤
      ((N:ℝ)+M)*(1+L) := by
    rw [sum_add_distrib]
    calc
      _ ≤ (N:ℝ)*(1+Real.log N)+(M:ℝ)*(1+L) :=
        add_le_add (sum_card_divisors_le_log N) (sum_output_divisors_le hα N)
      _ ≤ (N:ℝ)*(1+L)+(M:ℝ)*(1+L) := by gcongr
      _ = _ := by ring
  unfold smoothCorrelation mangoldtCorrelation
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, |smoothMangoldt t n * smoothMangoldt t (floorMul α n) - Λ n * Λ (floorMul α n)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 N, t * L^3 * ((n.divisors.card:ℝ)+(floorMul α n).divisors.card) :=
      sum_le_sum hlocal
    _ = t * L^3 * ∑ n ∈ Ioc 0 N, ((n.divisors.card:ℝ)+(floorMul α n).divisors.card) := by rw [mul_sum]
    _ ≤ t * L^3 * (((N:ℝ)+M)*(1+L)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ t * ((N:ℝ)+M) * (1+L)^4 := by
      have hp : L^3 ≤ (1+L)^3 := pow_le_pow_left₀ hL (by linarith) 3
      have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ t*((N:ℝ)+M)*(1+L) by positivity)
      nlinarith only [hh]

#print axioms smoothCorrelation_error_bound

end Erdos972SmoothCorrelationApprox
