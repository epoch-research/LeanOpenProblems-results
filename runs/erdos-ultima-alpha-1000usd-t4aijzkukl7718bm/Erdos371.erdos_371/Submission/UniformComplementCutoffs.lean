import Submission.MaximalComplementDiagonal
import Submission.ComplementPrefixIndicator

/-! One cutoff pair simultaneously cancels all fixed-degree complementary
prefixes, including the moving radical-size condition and the shifted input. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma untruncatedComplementPrefix_abs_le_cutoff (B X n : ℕ) :
    |untruncatedComplementPrefix B X n| ≤ (X+1 : ℝ) := by
  rw [untruncatedComplementPrefix,abs_mul,roughRadical_moebius_abs,one_mul]
  calc
    _ ≤ ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
        if e ≤ X then (1 : ℝ) else 0 := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro e _
      split_ifs
      · rw [abs_mul,divisorSideColour_abs,mul_one,← Int.cast_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := e))
      · simp
    _ ≤ (X+1 : ℝ) := by
      rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]
      have hc : ((roughRadical B (n*(n+1))).divisors.filter (fun e => e ≤ X)).card ≤ X+1 := by
        apply (card_le_card _).trans_eq (card_range (X+1))
        intro e he
        exact mem_range.mpr (by have := (mem_filter.mp he).2; omega)
      exact_mod_cast hc

lemma untruncatedComplementPrefix_shift_error (B X N : ℕ) :
    |(∑ n ∈ range N, untruncatedComplementPrefix B X (n+1))/N-
      (∑ n ∈ range N, untruncatedComplementPrefix B X n)/N| ≤ 2*(X+1 : ℝ)/N := by
  have hs := sum_range_succ' (untruncatedComplementPrefix B X) N
  rw [sum_range_succ] at hs
  have he : (∑ n ∈ range N, untruncatedComplementPrefix B X (n+1))-
      (∑ n ∈ range N, untruncatedComplementPrefix B X n)=untruncatedComplementPrefix B X N-untruncatedComplementPrefix B X 0 := by linarith
  rw [← sub_div,he,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have h := abs_sub (untruncatedComplementPrefix B X N) (untruncatedComplementPrefix B X 0)
  have h1 := untruncatedComplementPrefix_abs_le_cutoff B X N
  have h0 := untruncatedComplementPrefix_abs_le_cutoff B X 0
  linarith

/-- Uniformity in the complementary endpoint survives both the sample shift
and restoration of the moving radical-size indicator. -/
theorem complementPrefixAt_uniform_zero_of_untruncated (B H : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N ≤ B N+1)
    (hshort : ∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ X ≤ (B N)^k,
      |(∑ n ∈ range N, untruncatedComplementPrefix (B N) X n)/N| < ε) :
    ∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ X ≤ (B N)^k,
      |(∑ n ∈ range N, complementPrefixAt (B N) (H N*N) X (n+1))/N| < ε := by
  intro k ε hε
  have hbound := ((subpower_pow_div_tendsto_zero B hB k).add tendsto_one_div_atTop_nhds_zero_nat).const_mul 2
  simp only [add_zero,mul_zero] at hbound
  filter_upwards [hshort k (ε/3) (by positivity),
    complementPrefixAt_mean_error_uniform B H k hBatTop hB hHB (ε/3) (by positivity),
    hbound.eventually_lt_const (show (0 : ℝ) < ε/3 by positivity),eventually_gt_atTop (0 : ℕ)]
      with N hshort herr hbound hN
  intro X hX
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hshort := hshort X hX
  have herr := herr X hX
  have hshift := untruncatedComplementPrefix_shift_error (B N) X N
  have hXr : (X : ℝ) ≤ (B N+1 : ℝ)^k := by
    exact (show (X : ℝ) ≤ (B N : ℝ)^k by exact_mod_cast hX).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) k)
  have hshift' : |(∑ n ∈ range N, untruncatedComplementPrefix (B N) X (n+1))/N-
      (∑ n ∈ range N, untruncatedComplementPrefix (B N) X n)/N| < ε/3 := by
    refine (hshift.trans ?_).trans_lt hbound
    calc
      _ ≤ 2*((B N+1 : ℝ)^k+1)/N := by gcongr
      _ = _ := by ring
  have herr' : |(∑ n ∈ range N, complementPrefixAt (B N) (H N*N) X (n+1))/N-
      (∑ n ∈ range N, untruncatedComplementPrefix (B N) X (n+1))/N| < ε/3 := by
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_pos hNr]
    exact (div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hNr.le).trans_lt herr
  have ht1 := abs_sub_le
    ((∑ n ∈ range N, complementPrefixAt (B N) (H N*N) X (n+1))/N)
    ((∑ n ∈ range N, untruncatedComplementPrefix (B N) X (n+1))/N) 0
  have ht2 := abs_sub_le
    ((∑ n ∈ range N, untruncatedComplementPrefix (B N) X (n+1))/N)
    ((∑ n ∈ range N, untruncatedComplementPrefix (B N) X n)/N) 0
  simp only [sub_zero] at ht1 ht2
  linarith

/-- The SAME B,H work for every fixed k and uniformly for every product
prefix X≤B^k. The small-divisor budget remains uniform in its sampling prefix. -/
theorem exists_simultaneous_maximal_complement_cutoffs :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ X ≤ (B N)^k,
        |(∑ n ∈ range N, complementPrefixAt (B N) (H N*N) X (n+1))/N| < ε) := by
  obtain ⟨B,H,K,C,hB,hH,hK,hweighted,hHB,hC,hbudget,hClim,hmax⟩ := exists_maximal_complement_diagonal
  have hnonneg (N : ℕ) : 0 ≤ Real.log (B N+1 : ℝ)/Real.log N :=
    div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (B N); linarith)) (Real.log_natCast_nonneg N)
  have hlog : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => hnonneg N) _ hweighted
    intro N
    have hh : (1 : ℝ) ≤ K N+1 := by have := Nat.cast_nonneg (α := ℝ) (K N); linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (hnonneg N)
  have hi : Tendsto (fun N => 1/(K N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hK
  have hfixed (k : ℕ) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ X ≤ (B N)^k,
      |(∑ n ∈ range N, untruncatedComplementPrefix (B N) X n)/N| < ε := by
    filter_upwards [hmax,hK.eventually_ge_atTop k,hB.eventually_gt_atTop 0,hi.eventually_lt_const hε]
      with N hm hk hb hi
    intro X hX
    exact (hm X (hX.trans (Nat.pow_le_pow_right hb hk))).trans_lt hi
  exact ⟨B,H,C,hB,hH,hlog,hHB,hC,hbudget,hClim,
    complementPrefixAt_uniform_zero_of_untruncated B H hB hlog hHB hfixed⟩

#print axioms exists_simultaneous_maximal_complement_cutoffs
end Erdos371
