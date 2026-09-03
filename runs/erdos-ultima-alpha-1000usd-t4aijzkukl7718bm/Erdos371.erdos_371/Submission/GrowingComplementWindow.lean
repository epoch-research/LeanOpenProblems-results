import Submission.UniformComplementCutoffs

/-! A growing uniformly cancelled complementary window. It dominates every
fixed power of B, but remains subpower in N; the latter distinction is explicit. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma exists_growing_complement_window (B H : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hfixed : ∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ X ≤ (B N)^k,
      |(∑ n ∈ range N, complementPrefixAt (B N) (H N*N) X (n+1))/N| < ε) :
    ∃ K : ℕ → ℕ, Tendsto K atTop atTop ∧
      Tendsto (fun N => Real.log ((B N)^(K N)+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ X ≤ (B N)^(K N),
        |(∑ n ∈ range N, complementPrefixAt (B N) (H N*N) X (n+1))/N| < ε) := by
  classical
  let P (N k : ℕ) : Prop := Real.log (B N+1 : ℝ)/Real.log N ≤ 1/(k+1 : ℝ)^2 ∧
    ∀ X ≤ (B N)^k, |(∑ n ∈ range N, complementPrefixAt (B N) (H N*N) X (n+1))/N| ≤ 1/(k+1 : ℝ)
  have hP (k : ℕ) : ∀ᶠ N in atTop, P N k := by
    filter_upwards [hB.eventually_lt_const (show (0 : ℝ) < 1/(k+1 : ℝ)^2 by positivity),
      hfixed k (1/(k+1 : ℝ)) (by positivity)] with N hl hm
    exact ⟨hl.le,fun X hX => (hm X hX).le⟩
  let K (N : ℕ) := Nat.findGreatest (P N) N
  have hK : Tendsto K atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k,hP k] with N hNk hp
    exact Nat.le_findGreatest hNk hp
  have hPK : ∀ᶠ N in atTop, P N (K N) := by
    filter_upwards [hP 0] with N hp
    exact Nat.findGreatest_spec (Nat.zero_le N) hp
  have hi : Tendsto (fun N => 1/(K N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hK
  refine ⟨K,hK,?_,?_⟩
  · apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg
      (Real.log_nonneg (by have := pow_nonneg (Nat.cast_nonneg (α := ℝ) (B N)) (K N); linarith))
      (Real.log_natCast_nonneg N)) _ hi
    filter_upwards [hPK,hBatTop.eventually_ge_atTop 1] with N hp hb
    have hpow : (B N)^(K N)+1 ≤ (B N+1)^(K N+1) := by
      have hmono := Nat.pow_le_pow_left (Nat.le_succ (B N)) (K N)
      have hone : 1 ≤ (B N+1)^(K N) := Nat.pow_pos (by omega)
      calc
        _ ≤ (B N+1)^(K N)+(B N+1)^(K N) := Nat.add_le_add hmono hone
        _ = 2*(B N+1)^(K N) := by ring
        _ ≤ (B N+1)*(B N+1)^(K N) := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by rw [pow_succ]; ring
    have hlog : Real.log ((B N)^(K N)+1 : ℝ)/Real.log N ≤
        (K N+1 : ℝ)*(Real.log (B N+1 : ℝ)/Real.log N) := by
      have hh := div_le_div_of_nonneg_right
        (Real.log_le_log (by positivity) (show ((B N)^(K N)+1 : ℝ) ≤ (B N+1 : ℝ)^(K N+1) by exact_mod_cast hpow))
        (Real.log_natCast_nonneg N)
      rw [Real.log_pow] at hh
      convert hh using 1
      push_cast
      ring
    have hfrac : (K N+1 : ℝ)*(1/(K N+1 : ℝ)^2)=1/(K N+1 : ℝ) := by
      field_simp
    exact hlog.trans ((mul_le_mul_of_nonneg_left hp.1 (by positivity)).trans_eq hfrac)
  · intro ε hε
    filter_upwards [hPK,hi.eventually_lt_const hε] with N hp hi
    intro X hX
    exact (hp.2 X hX).trans_lt hi

/-- Two subpower quantities still occupy a vanishing fraction of N. In
particular the controlled U-window cannot be identified with N/H. -/
lemma subpower_complement_window_fraction_zero (B H U : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hU : Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N ≤ B N+1) :
    Tendsto (fun N : ℕ => (U N : ℝ)*H N/N) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(-(1/2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ ht
  filter_upwards [hHB,subpower_pow_eventually_le B hB 1 (1/4) (by norm_num),
    subpower_pow_eventually_le U hU 1 (1/4) (by norm_num),eventually_gt_atTop (0 : ℕ)]
      with N hh hb hu hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [pow_one] at hb hu
  have hhr : (H N : ℝ) ≤ B N+1 := by exact_mod_cast hh
  have hprod : (U N : ℝ)*H N ≤ (N : ℝ)^(1/2 : ℝ) := by
    calc
      _ ≤ (U N+1 : ℝ)*(B N+1 : ℝ) := mul_le_mul (by linarith) hhr (Nat.cast_nonneg _) (by positivity)
      _ ≤ (N : ℝ)^(1/4 : ℝ)*(N : ℝ)^(1/4 : ℝ) := mul_le_mul hu hb (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hNr]; congr 1; ring
  rw [show -(1/2 : ℝ)=1/2-1 by ring,Real.rpow_sub hNr,Real.rpow_one]
  exact div_le_div_of_nonneg_right hprod hNr.le

/-- One growing window dominates all fixed B-powers and has vanishing
signed prefix means, while its relative size versus N/H tends to zero. -/
theorem exists_cancelled_growing_complement_window :
    ∃ B H U : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto U atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ U N) ∧
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ X ≤ U N,
        |(∑ n ∈ range N, complementPrefixAt (B N) (H N*N) X (n+1))/N| < ε) ∧
      Tendsto (fun N : ℕ => (U N : ℝ)*H N/N) atTop (𝓝 0) := by
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hbudget,hClim,hfixed⟩ := exists_simultaneous_maximal_complement_cutoffs
  obtain ⟨K,hK,hlogU,hmax⟩ := exists_growing_complement_window B H hB hlog hfixed
  let U : ℕ → ℕ := fun N => (B N)^(K N)
  have hU : Tendsto U atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hB.eventually_ge_atTop M,hB.eventually_gt_atTop 0,hK.eventually_ge_atTop 1]
      with N hb hb0 hk
    exact hb.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hb0 hk)
  refine ⟨B,H,U,C,hB,hH,hU,hlog,?_,hHB,hC,hbudget,hClim,?_,hmax,?_⟩
  · simpa only [U,Nat.cast_pow] using hlogU
  · intro k
    filter_upwards [hB.eventually_gt_atTop 0,hK.eventually_ge_atTop k] with N hb hk
    exact Nat.pow_le_pow_right hb hk
  · exact subpower_complement_window_fraction_zero B H U hlog
      (by simpa only [U,Nat.cast_pow] using hlogU) hHB

#print axioms exists_cancelled_growing_complement_window
end Erdos371
