import Submission.SignedShortComplementDiagonal
import Submission.ShortComplementIndicator

/-! Simultaneous short-complement signed cancellation and a uniform prefix
budget for all small rough divisors. The long complementary indices remain
unestimated. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma shortRoughComplement_abs_le_cutoff (B k n : ℕ) :
    |shortRoughComplement B k n| ≤ (B^k+1 : ℝ) := by
  rw [shortRoughComplement,abs_mul,roughRadical_moebius_abs,one_mul]
  calc
    _ ≤ ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
        if e ≤ B^k then (1 : ℝ) else 0 := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro e _
      split_ifs
      · rw [abs_mul,divisorSideColour_abs,mul_one,← Int.cast_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := e))
      · simp
    _ ≤ (B^k+1 : ℝ) := by
      rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]
      have hc : ((roughRadical B (n*(n+1))).divisors.filter (fun e => e ≤ B^k)).card ≤ B^k+1 := by
        apply (card_le_card _).trans_eq (card_range (B^k+1))
        intro e he
        exact mem_range.mpr (by have := (mem_filter.mp he).2; omega)
      exact_mod_cast hc

lemma shortRoughComplement_shift_error (B k N : ℕ) :
    |(∑ n ∈ range N, shortRoughComplement B k (n+1))/N-
      (∑ n ∈ range N, shortRoughComplement B k n)/N| ≤ 2*(B^k+1 : ℝ)/N := by
  have hs := sum_range_succ' (shortRoughComplement B k) N
  rw [sum_range_succ] at hs
  have he : (∑ n ∈ range N, shortRoughComplement B k (n+1))-
      (∑ n ∈ range N, shortRoughComplement B k n)=shortRoughComplement B k N-shortRoughComplement B k 0 := by linarith
  rw [← sub_div,he,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have h := abs_sub (shortRoughComplement B k N) (shortRoughComplement B k 0)
  have h1 := shortRoughComplement_abs_le_cutoff B k N
  have h0 := shortRoughComplement_abs_le_cutoff B k 0
  linarith

lemma shortRoughComplement_shifted_zero (B : ℕ → ℕ) (k : ℕ)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (h : Tendsto (fun N : ℕ => (∑ n ∈ range N, shortRoughComplement (B N) k n)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, shortRoughComplement (B N) k (n+1))/N) atTop (𝓝 0) := by
  have hbound := ((subpower_pow_div_tendsto_zero B hB k).add tendsto_one_div_atTop_nhds_zero_nat).const_mul 2
  simp only [add_zero,mul_zero] at hbound
  have hd : Tendsto (fun N : ℕ => (∑ n ∈ range N, shortRoughComplement (B N) k (n+1))/N-
      (∑ n ∈ range N, shortRoughComplement (B N) k n)/N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    apply Eventually.of_forall
    intro N
    rw [Real.norm_eq_abs]
    refine (shortRoughComplement_shift_error (B N) k N).trans ?_
    have hp : (B N : ℝ)^k ≤ (B N+1 : ℝ)^k := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) k
    calc
      _ ≤ 2*((B N+1 : ℝ)^k+1)/N := by gcongr
      _ = _ := by ring
  simpa only [sub_add_cancel,add_zero] using hd.add h

/-- Restoring the moving product condition and shifting the sample preserve
signed cancellation for the short complementary range. -/
theorem shortRoughComplementAt_zero_of_untruncated (B H : ℕ → ℕ) (k : ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N ≤ B N+1)
    (hshort : Tendsto (fun N : ℕ => (∑ n ∈ range N, shortRoughComplement (B N) k n)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, shortRoughComplementAt (B N) (H N*N) k (n+1))/N)
      atTop (𝓝 0) := by
  have hshift := shortRoughComplement_shifted_zero B k hB hshort
  have habs := shortRoughComplementAt_mean_absolute_error_zero B H k hBatTop hB hHB
  have hd : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, shortRoughComplementAt (B N) (H N*N) k (n+1))/N-
      (∑ n ∈ range N, shortRoughComplement (B N) k (n+1))/N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ habs
    apply Eventually.of_forall
    intro N
    rw [Real.norm_eq_abs,← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
  simpa only [sub_add_cancel,add_zero] using hd.add hshift

/-- For every FIXED k, one can simultaneously cancel the ACTUAL e≤B^k
complementary sum and control EVERY small-divisor sampling prefix by o(N). -/
theorem exists_signed_short_complement_cutoffs (k : ℕ) :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ range N, shortRoughComplementAt (B N) (H N*N) k (n+1))/N)
        atTop (𝓝 0) := by
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hprefix,hClim,hshort⟩ := exists_signed_short_subpower_prefix_budget k
  exact ⟨B,H,C,hB,hH,hlog,hHB,hC,hprefix,hClim,
    shortRoughComplementAt_zero_of_untruncated B H k hB hlog hHB hshort⟩

#print axioms exists_signed_short_complement_cutoffs
end Erdos371
