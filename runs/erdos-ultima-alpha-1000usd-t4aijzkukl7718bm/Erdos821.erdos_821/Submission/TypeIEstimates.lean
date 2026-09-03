import Submission.PolyaVinogradov
import Submission.FiniteConvolution

/-!
# Partial summation and Type I character sums

Pólya–Vinogradov and finite partial summation control the short convolution
terms in Vaughan's identity, uniformly in the summation endpoint.
-/

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

lemma norm_monotone_weighted_sum_le (f : ℕ → ℝ) (g : ℕ → ℂ)
    (hf : Monotone f) (hf0 : ∀ n, 0 ≤ f n) (B : ℝ) (hB : 0 ≤ B) (N : ℕ)
    (hg : ∀ L ≤ N, ‖∑ i ∈ range L, g i‖ ≤ B) :
    ‖∑ i ∈ range N, f i • g i‖ ≤ 2 * B * f (N - 1) := by
  rw [Finset.sum_range_by_parts]
  calc
    _ ≤ ‖f (N - 1) • ∑ i ∈ range N, g i‖ +
        ‖∑ i ∈ range (N - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ := norm_sub_le _ _
    _ ≤ f (N - 1) * B + ∑ i ∈ range (N - 1), (f (i + 1) - f i) * B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
        exact mul_le_mul_of_nonneg_left (hg N le_rfl) (hf0 _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        have hdiff : 0 ≤ f (i + 1) - f i := sub_nonneg.mpr (hf (by omega))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
        apply mul_le_mul_of_nonneg_left _ hdiff
        exact hg (i + 1) (by have := mem_range.mp hi; omega)
    _ = f (N - 1) * B + (f (N - 1) - f 0) * B := by
      rw [← Finset.sum_mul, Finset.sum_range_sub]
    _ ≤ _ := by nlinarith [mul_nonneg (hf0 0) hB]

lemma sum_Icc_one_eq_sum_range {E : Type*} [AddCommMonoid E] (f : ℕ → E) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n) = ∑ i ∈ range N, f (i + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add']
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc]

lemma log_nat_mono {m n : ℕ} (hmn : m ≤ n) : Real.log m ≤ Real.log n := by
  by_cases hm : m = 0
  · subst m
    simpa only [Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg n
  · apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hm
    · exact_mod_cast hmn

lemma norm_twisted_convolution_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℝ) (N D : ℕ) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hf : ∀ n ∈ Icc 1 N, |f n| ≤ C) (hfD : ∀ n, D < n → f n = 0)
    (hg : ∀ L ≤ N, ‖twistedArithmeticSum χ g L‖ ≤ B) :
    ‖twistedArithmeticSum χ (f * g) N‖ ≤ (D : ℝ) * C * B := by
  classical
  rw [twistedArithmeticSum_convolution_quotient]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, if n ≤ D then C * B else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      by_cases h : n ≤ D
      · rw [if_pos h, norm_mul]
        apply mul_le_mul _ (hg _ (Nat.div_le_self N n)) (norm_nonneg _) hC
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ C * 1 := mul_le_mul (hf n hn) (χ.norm_le_one _) (norm_nonneg _) hC
          _ = C := mul_one _
      · rw [if_neg h, hfD n (Nat.lt_of_not_ge h)]
        simp
    _ = (((Icc 1 N).filter (fun n => n ≤ D)).card : ℝ) * (C * B) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D : ℝ) * (C * B) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hB)
      have hcard : ((Icc 1 N).filter (fun n => n ≤ D)).card ≤ D := by
        calc
          _ ≤ (Icc 1 D).card := Finset.card_le_card (by
            intro n hn
            obtain ⟨hn, hnD⟩ := mem_filter.mp hn
            exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, hnD⟩)
          _ = D := by simp
      exact_mod_cast hcard
    _ = _ := by ring

section Primitive

variable {q : ℕ} [NeZero q] (hq : 2 ≤ q)
variable {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)

omit [NeZero q] in
lemma twistedArithmeticSum_zeta_eq_interval (N : ℕ) :
    twistedArithmeticSum χ (ζ : ArithmeticFunction ℝ) N = intervalCharacterSum χ 1 N := by
  rw [twistedArithmeticSum, sum_Icc_one_eq_sum_range]
  unfold intervalCharacterSum
  apply Finset.sum_congr rfl
  intro i hi
  simp only [natCoe_apply, zeta_apply_ne (Nat.succ_ne_zero i), Nat.cast_one,
    Complex.ofReal_one, one_mul, Nat.cast_add, Int.cast_add, Int.cast_one, Int.cast_natCast]
  rw [add_comm]

include hq hχ

lemma norm_twisted_zeta_le_pv (N : ℕ) :
    ‖twistedArithmeticSum χ (ζ : ArithmeticFunction ℝ) N‖ ≤ Real.sqrt q * (1 + Real.log q) := by
  rw [twistedArithmeticSum_zeta_eq_interval]
  exact polya_vinogradov hq hχ 1 N

lemma norm_twisted_log_le_pv (N : ℕ) :
    ‖twistedArithmeticSum χ log N‖ ≤
      2 * (Real.sqrt q * (1 + Real.log q)) * Real.log N := by
  have hm : Monotone (fun i : ℕ => Real.log (i + 1 : ℕ)) := by
    intro i j hij
    exact log_nat_mono (by omega)
  have h := norm_monotone_weighted_sum_le (fun i : ℕ => Real.log (i + 1 : ℕ))
    (fun i => χ ((i + 1 : ℕ) : ZMod q)) hm (fun i => Real.log_natCast_nonneg _)
    (Real.sqrt q * (1 + Real.log q))
    (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_natCast_nonneg q])) N (fun L hL => ?_)
  · have heq : Real.log (N - 1 + 1 : ℕ) = Real.log N := by
      by_cases hN : N = 0
      · simp [hN]
      · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN)]
    dsimp only at h
    rw [heq] at h
    simpa only [twistedArithmeticSum, log_apply, sum_Icc_one_eq_sum_range, Complex.real_smul] using h
  · have hb := polya_vinogradov hq hχ 1 L
    simpa only [intervalCharacterSum, Int.cast_add, Int.cast_one, Int.cast_natCast,
      Nat.cast_add, Nat.cast_one, add_comm] using hb

lemma norm_vaughan_mu_log_le (V N : ℕ) :
    ‖twistedArithmeticSum χ (shortPart (μ : ArithmeticFunction ℝ) V * log) N‖ ≤
      2 * (V : ℝ) * Real.sqrt q * (1 + Real.log q) * Real.log N := by
  have hB : 0 ≤ 2 * (Real.sqrt q * (1 + Real.log q)) * Real.log N := by
    have := Real.log_natCast_nonneg q
    have := Real.log_natCast_nonneg N
    positivity
  have h := norm_twisted_convolution_le χ (shortPart (μ : ArithmeticFunction ℝ) V) log N V 1
    (2 * (Real.sqrt q * (1 + Real.log q)) * Real.log N) (by norm_num) hB
    (fun n hn => abs_shortPart_moebius_le_one V n)
    (fun n hn => by simp only [shortPart_apply, if_neg (not_le.mpr hn)]) (fun L hL => ?_)
  · convert h using 1; ring
  · apply (norm_twisted_log_le_pv hq hχ L).trans
    apply mul_le_mul_of_nonneg_left (log_nat_mono hL)
    have := Real.log_natCast_nonneg q
    positivity

lemma norm_vaughan_typeI_le (U V N : ℕ) :
    ‖twistedArithmeticSum χ (vaughanTypeI U V * (ζ : ArithmeticFunction ℝ)) N‖ ≤
      (U : ℝ) * V * Real.log N * Real.sqrt q * (1 + Real.log q) := by
  have h := norm_twisted_convolution_le χ (vaughanTypeI U V) (ζ : ArithmeticFunction ℝ)
    N (U * V) (Real.log N) (Real.sqrt q * (1 + Real.log q)) (Real.log_natCast_nonneg _)
    (by have := Real.log_natCast_nonneg q; positivity)
    (fun n hn => (abs_vaughanTypeI_le U V n).trans (log_nat_mono (mem_Icc.mp hn).2))
    (fun n hn => vaughanTypeI_eq_zero hn) (fun L hL => norm_twisted_zeta_le_pv hq hχ L)
  convert h using 1; push_cast; ring

end Primitive

end Erdos821.AnalyticSieve
