import Submission.MixedRectangleError
import Submission.WeightedPrefixDiagonal
import Submission.UniformComplementCutoffs

/-! Signed cancellation for a mixed low/high complementary rectangle, with
one cutoff pair for every fixed short-factor degree and every short endpoint.
This does not control an unrestricted low-prime part of the index. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma highWeightedPrefix_shift_error (B W F X L N : ℕ) (hN : 0 < N)
    (hW : 1 < W) (hWN : N+1 ≤ W^L) :
    |(∑ n ∈ range N, highDivisorWeight W X (n+1)*untruncatedComplementPrefix B F (n+1))/N-
      (∑ n ∈ range N, highDivisorWeight W X n*untruncatedComplementPrefix B F n)/N| ≤
      (2 : ℝ)^(2*L)*(F+1 : ℝ)/N := by
  let f : ℕ → ℝ := fun n => highDivisorWeight W X n*untruncatedComplementPrefix B F n
  have h0 : f 0=0 := by simp [f,highDivisorWeight_zero]
  have hs := sum_range_succ' f N
  rw [sum_range_succ,h0,add_zero] at hs
  have he : (∑ n ∈ range N, f (n+1))-(∑ n ∈ range N, f n)=f N := by linarith
  change |(∑ n ∈ range N, f (n+1))/N-(∑ n ∈ range N, f n)/N| ≤ _
  rw [← sub_div,he,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  dsimp only [f]
  rw [abs_mul]
  exact mul_le_mul (high_weight_and_complement_bound W L N N B 0 X hW hWN hN le_rfl).1
    (untruncatedComplementPrefix_abs_le_cutoff B F N) (abs_nonneg _) (by positivity)

lemma exists_high_weighted_prefix_cutoffs (W X : ℕ → ℕ) (L : ℕ)
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
          untruncatedComplementPrefix (B N) F (n+1))/N| < ε) := by
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
  obtain ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,hshort⟩ := exists_weighted_untruncated_prefix_cutoffs w hw
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
  refine ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,?_⟩
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

/-- Actual mixed complementary summands, not just high-only ones, are
cancelled. The same B,H work for every fixed short-factor degree k. -/
theorem exists_mixed_rectangle_cancellation (W X : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hX : ∀ᶠ N in atTop, (X N)^4 ≤ N) :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
        |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N| < ε) := by
  obtain ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,hweighted⟩ := exists_high_weighted_prefix_cutoffs W X L hW
  refine ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,?_⟩
  intro k ε hε
  have hsize : ∀ᶠ N in atTop, ((H N*N)*((B N)^k*X N))^2 ≤ (N+1)^3 := by
    filter_upwards [hHB,hX,subpower_pow_eventually_nat_le B hB ((k+1)*4)] with N hh hx hb
    have hH : H N*(B N)^k ≤ (B N+1)^(k+1) := by
      calc
        _ ≤ (B N+1)*(B N+1)^k := Nat.mul_le_mul hh (Nat.pow_le_pow_left (Nat.le_succ _) k)
        _ = _ := by rw [pow_succ]; ring
    have hH4 : (H N*(B N)^k)^4 ≤ N := by
      rw [pow_mul] at hb
      exact (Nat.pow_le_pow_left hH 4).trans hb
    have hp : ((H N*(B N)^k)^2*(X N)^2)^2 ≤ N^2 := by nlinarith [Nat.mul_le_mul hH4 hx]
    have hp' : (H N*(B N)^k)^2*(X N)^2 ≤ N :=
      (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hp
    have hh := Nat.mul_le_mul_right (N^2) hp'
    nlinarith
  have herr := mixedRectangle_mean_error_uniform B (fun N => H N*N) W X k L hL hBt hB hW hsize
  filter_upwards [herr (ε/2) (by positivity),hweighted k (ε/2) (by positivity),
    eventually_gt_atTop (0 : ℕ)] with N he hw hN
  intro F hF
  have hdiff : |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N-
      (∑ n ∈ range N, highDivisorWeight (W N) (X N) (n+1)*untruncatedComplementPrefix (B N) F (n+1))/N| < ε/2 := by
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact (div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)).trans_lt (he F hF)
  have htri := abs_sub_le
    ((∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N)
    ((∑ n ∈ range N, highDivisorWeight (W N) (X N) (n+1)*untruncatedComplementPrefix (B N) F (n+1))/N) 0
  simp only [sub_zero] at htri
  linarith [hw F hF]

#print axioms exists_mixed_rectangle_cancellation
end Erdos371
