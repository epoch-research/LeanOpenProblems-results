import Submission.SignedRoughUnitDiagonal

/-! Signed cancellation of the ACTUAL unit complementary summand, including
its radical-size indicator, for cutoffs also controlling all small moduli. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma untruncatedRoughUnit_shift_error (B N : ℕ) :
    |(∑ n ∈ range N, untruncatedRoughUnit B (n+1))/N-
      (∑ n ∈ range N, untruncatedRoughUnit B n)/N|≤2/(N : ℝ) := by
  have hs := sum_range_succ' (untruncatedRoughUnit B) N
  rw [sum_range_succ] at hs
  have he : (∑ n ∈ range N, untruncatedRoughUnit B (n+1))-
      (∑ n ∈ range N, untruncatedRoughUnit B n)=untruncatedRoughUnit B N-untruncatedRoughUnit B 0 := by linarith
  rw [← sub_div,he,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ)≤N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have h := abs_sub (untruncatedRoughUnit B N) (untruncatedRoughUnit B 0)
  simpa only [untruncatedRoughUnit_abs,one_add_one_eq_two] using h

lemma untruncatedRoughUnit_shifted_zero (B : ℕ → ℕ)
    (h : Tendsto (fun N : ℕ => (∑ n ∈ range N, untruncatedRoughUnit (B N) n)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, untruncatedRoughUnit (B N) (n+1))/N) atTop (𝓝 0) := by
  have hd : Tendsto (fun N : ℕ => (∑ n ∈ range N, untruncatedRoughUnit (B N) (n+1))/N-
      (∑ n ∈ range N, untruncatedRoughUnit (B N) n)/N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    exact Eventually.of_forall fun N => untruncatedRoughUnit_shift_error (B N) N
  simpa only [sub_add_cancel,add_zero] using hd.add h

lemma roughComplementUnit_untruncated_error (B D n : ℕ) :
    |roughComplementUnit B D n-untruncatedRoughUnit B n|=1-‖roughComplementUnit B D n‖ := by
  rw [roughComplementUnit_norm]
  have he : roughComplementUnit B D n =
      if D<roughRadical B (n*(n+1)) then untruncatedRoughUnit B n else 0 := rfl
  rw [he]
  split_ifs
  · simp
  · simp only [zero_sub,abs_neg,untruncatedRoughUnit_abs,sub_zero]

lemma roughComplementUnit_untruncated_mean_error (B D N : ℕ) (hN : 0<N) :
    |(∑ n ∈ range N, roughComplementUnit B D (n+1))/N-
      (∑ n ∈ range N, untruncatedRoughUnit B (n+1))/N| ≤
      1-(∑ n ∈ range N, ‖roughComplementUnit B D (n+1)‖)/N := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_pos hNr]
  calc
    _ ≤ (∑ n ∈ range N, |roughComplementUnit B D (n+1)-untruncatedRoughUnit B (n+1)|)/N :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hNr.le
    _ = _ := by
      simp only [roughComplementUnit_untruncated_error,sum_sub_distrib,sum_const,card_range,
        nsmul_eq_mul,mul_one,sub_div,div_self hNr.ne']

/-- The absolute unit mass tends to one, so restoring the size indicator
changes its mean negligibly. This is a signed conclusion, not an absolute
bound for the entire complementary-divisor sum. -/
theorem roughComplementUnit_zero_of_untruncated (B H : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (hlog : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N≤B N+1)
    (hunit : Tendsto (fun N : ℕ => (∑ n ∈ range N, untruncatedRoughUnit (B N) n)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, roughComplementUnit (B N) (H N*N) (n+1))/N)
      atTop (𝓝 0) := by
  have habs := roughComplementUnit_absolute_average_one B H hB hlog hHB
  have hshift := untruncatedRoughUnit_shifted_zero B hunit
  have hd : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, roughComplementUnit (B N) (H N*N) (n+1))/N-
      (∑ n ∈ range N, untruncatedRoughUnit (B N) (n+1))/N) atTop (𝓝 0) := by
    have ht : Tendsto (fun N : ℕ => 1-
        (∑ n ∈ range N, ‖roughComplementUnit (B N) (H N*N) (n+1)‖)/N)
        atTop (𝓝 (1-1 : ℝ)) := tendsto_const_nhds.sub habs
    simp only [sub_self] at ht
    apply squeeze_zero_norm' _ ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact roughComplementUnit_untruncated_mean_error (B N) (H N*N) N hN
  simpa only [sub_add_cancel,add_zero] using hd.add hshift

/-- Simultaneous unconditional signed cancellation of the actual unit term
and a uniform o(N) prefix budget for all small rough divisors through H(N)*N. -/
theorem exists_signed_complement_unit_cutoffs :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N≤B N+1) ∧ (∀ N, 0≤C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)|≤C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ range N, roughComplementUnit (B N) (H N*N) (n+1))/N)
        atTop (𝓝 0) := by
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hprefix,hClim,hunit⟩ := exists_signed_unit_subpower_prefix_budget
  exact ⟨B,H,C,hB,hH,hlog,hHB,hC,hprefix,hClim,
    roughComplementUnit_zero_of_untruncated B H hB hlog hHB hunit⟩

#print axioms exists_signed_complement_unit_cutoffs
end Erdos371
