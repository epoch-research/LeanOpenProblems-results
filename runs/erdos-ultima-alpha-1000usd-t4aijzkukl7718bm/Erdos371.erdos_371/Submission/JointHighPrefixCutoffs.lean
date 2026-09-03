import Submission.TwoWeightPrefixDiagonal
import Submission.FullEndpointMixedRectangle

/-! The high-weighted and unweighted complementary prefixes now share
one cutoff sequence and one uniform small-divisor prefix budget. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

theorem exists_joint_untruncated_prefix_cutoffs (w : ℕ → ℕ → ℝ)
    (hw : ∀ N n, n < N → |w N n| ≤ 1) :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ X ≤ (B N)^k,
        |(∑ n ∈ range N, w N n*untruncatedComplementPrefix (B N) X n)/N| < ε) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ X ≤ (B N)^k,
        |(∑ n ∈ range N, untruncatedComplementPrefix (B N) X n)/N| < ε) := by
  let v : ℕ → Bool → ℕ → ℝ := fun N b n => if b then w N n else 1
  have hv : ∀ N b n, n < N → |v N b n| ≤ 1 := by
    intro N b n hn
    cases b
    · simp [v]
    · simpa only [v,ite_true] using hw N n hn
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hbudget,hClim,hmax⟩ := exists_two_weight_untruncated_prefix_cutoffs v hv
  refine ⟨B,H,C,hB,hH,hlog,hHB,hC,hbudget,hClim,?_,?_⟩
  · intro k ε hε
    filter_upwards [hmax k ε hε] with N hN
    simpa only [v,ite_true] using hN true
  · intro k ε hε
    filter_upwards [hmax k ε hε] with N hN
    simpa only [v,Bool.false_eq_true,ite_false,one_mul] using hN false

lemma exists_joint_high_weighted_prefix_cutoffs (W X : ℕ → ℕ) (L : ℕ)
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L) :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
        |(∑ n ∈ range N, highDivisorWeight (W N) (X N) (n+1)*
          untruncatedComplementPrefix (B N) F (n+1))/N| < ε) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
        |(∑ n ∈ range N, untruncatedComplementPrefix (B N) F n)/N| < ε) := by
  classical
  let A : ℝ := 2^(2*L)
  have hA : 0 < A := by dsimp [A]; positivity
  let w : ℕ → ℕ → ℝ := fun N n =>
    if 1 < W N ∧ N+1 ≤ (W N)^L then highDivisorWeight (W N) (X N) n/A else 0
  have hw : ∀ N n, n < N → |w N n| ≤ 1 := by
    intro N n hn
    dsimp [w]
    split_ifs with hg
    · by_cases hn0 : n=0
      · subst n
        rw [highDivisorWeight_zero,zero_div,abs_zero]
        norm_num
      · rw [abs_div,abs_of_pos hA]
        apply (div_le_one hA).mpr
        exact (high_weight_and_complement_bound (W N) L N n 0 0 (X N) hg.1 hg.2 (by omega) hn.le).1
    · norm_num
  obtain ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,hshort,hplain⟩ := exists_joint_untruncated_prefix_cutoffs w hw
  have hunshift (k : ℕ) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
      |(∑ n ∈ range N, highDivisorWeight (W N) (X N) n*untruncatedComplementPrefix (B N) F n)/N| < ε := by
    filter_upwards [hW,hshort k (ε/A) (by positivity)] with N hwN hs
    intro F hF
    have he : (∑ n ∈ range N, highDivisorWeight (W N) (X N) n*untruncatedComplementPrefix (B N) F n)/N=
        A*((∑ n ∈ range N, w N n*untruncatedComplementPrefix (B N) F n)/N) := by
      rw [← mul_div_assoc,mul_sum]
      congr 1
      apply sum_congr rfl
      intro n _
      dsimp only [w]
      rw [if_pos hwN]
      field_simp
    rw [he,abs_mul,abs_of_pos hA]
    have hh := mul_lt_mul_of_pos_left (hs F hF) hA
    convert hh using 1
    field_simp
  refine ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,?_,hplain⟩
  intro k ε hε
  have ht := ((subpower_pow_div_tendsto_zero B hB k).add tendsto_one_div_atTop_nhds_zero_nat).const_mul A
  simp only [add_zero,mul_zero] at ht
  filter_upwards [hW,hunshift k (ε/2) (by positivity),
    ht.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity),eventually_gt_atTop (0 : ℕ)]
    with N hwN hu htN hN
  intro F hF
  have hh := highWeightedPrefix_shift_error (B N) (W N) F (X N) L N hN hwN.1 hwN.2
  have hFr : (F : ℝ) ≤ (B N+1 : ℝ)^k := by
    exact (show (F : ℝ) ≤ (B N : ℝ)^k by exact_mod_cast hF).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) k)
  have hbound : A*(F+1 : ℝ)/N ≤ A*((B N+1 : ℝ)^k/N+1/N) := by
    rw [← add_div,mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hA.le
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)
  have hsmall := (hh.trans hbound).trans_lt htN
  have htri := abs_sub_le
    ((∑ n ∈ range N, highDivisorWeight (W N) (X N) (n+1)*untruncatedComplementPrefix (B N) F (n+1))/N)
    ((∑ n ∈ range N, highDivisorWeight (W N) (X N) n*untruncatedComplementPrefix (B N) F n)/N) 0
  simp only [sub_zero] at htri
  linarith [hu F hF]

#print axioms exists_joint_high_weighted_prefix_cutoffs
end Erdos371
