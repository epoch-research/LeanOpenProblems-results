import Submission.MixedRectangleCancellation
import Submission.MixedRectangleSupport
import Submission.GrowingComplementWindow

/-! The cancelled low-factor window can grow past every fixed B-power while
remaining subpower. This does not make it the full W-smooth factor range. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma exists_growing_rectangle_window (B H W X : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hfixed : ∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
      |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N| < ε) :
    ∃ K : ℕ → ℕ, Tendsto K atTop atTop ∧
      Tendsto (fun N => Real.log ((B N)^(K N)+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^(K N),
        |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N| < ε) := by
  classical
  let P (N k : ℕ) : Prop := Real.log (B N+1 : ℝ)/Real.log N ≤ 1/(k+1 : ℝ)^2 ∧
    ∀ F ≤ (B N)^k, |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N| ≤ 1/(k+1 : ℝ)
  have hP (k : ℕ) : ∀ᶠ N in atTop, P N k := by
    filter_upwards [hB.eventually_lt_const (show (0 : ℝ) < 1/(k+1 : ℝ)^2 by positivity),
      hfixed k (1/(k+1 : ℝ)) (by positivity)] with N hl hm
    exact ⟨hl.le,fun F hF => (hm F hF).le⟩
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
    intro F hF
    exact (hp.2 F hF).trans_lt hi


/-- A growing low-factor window in an actual mixed complementary subrange.
The high endpoint X is prescribed; U is NOT allowed to cover arbitrary
W-smooth divisors without an additional argument. -/
theorem exists_cancelled_growing_mixed_rectangle (W X : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hX : ∀ᶠ N in atTop, (X N)^4 ≤ N) :
    ∃ B H U : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto U atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ U N) ∧ (∀ᶠ N in atTop, U N ≤ W N) ∧
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ U N,
        |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N| < ε) := by
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hbudget,hClim,hfixed⟩ := exists_mixed_rectangle_cancellation W X L hL hW hX
  obtain ⟨K,hK,hlogU,hmax⟩ := exists_growing_rectangle_window B H W X hB hlog hfixed
  let U : ℕ → ℕ := fun N => (B N)^(K N)
  have hU : Tendsto U atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hB.eventually_ge_atTop M,hB.eventually_gt_atTop 0,hK.eventually_ge_atTop 1]
      with N hb hb0 hk
    exact hb.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hb0 hk)
  have hUl : Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) := by
    simpa only [U,Nat.cast_pow] using hlogU
  refine ⟨B,H,U,C,hB,hH,hU,hlog,hUl,hHB,hC,hbudget,hClim,?_,?_,hmax⟩
  · intro k
    filter_upwards [hB.eventually_gt_atTop 0,hK.eventually_ge_atTop k] with N hb hk
    exact Nat.pow_le_pow_right hb hk
  · simpa only [pow_one] using subpower_below_power_cutoff U W L hL hUl (hW.mono fun N h => h.2) 1

/-- Removing f=1 leaves the same cancellation conclusion, so this also
controls the proper mixed part rather than only its sum with high-only terms. -/
theorem proper_low_mixed_rectangle_cancellation (B H U W X : ℕ → ℕ)
    (hmax : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ U N,
      |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N| < ε) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F, 1 ≤ F → F ≤ U N →
      |(∑ n ∈ range N, (mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1)-
        highComplementAt (B N) (H N*N) (W N) (X N) (n+1)))/N| < ε := by
  intro ε hε
  filter_upwards [hmax (ε/2) (by positivity)] with N hm
  intro F hF hFU
  have h1 := hm 1 (hF.trans hFU)
  have hF' := hm F hFU
  simp only [mixedComplementRectangleAt_one] at h1
  rw [sum_sub_distrib,sub_div]
  exact (abs_sub _ _).trans_lt (by linarith)

#print axioms exists_cancelled_growing_mixed_rectangle
#print axioms proper_low_mixed_rectangle_cancellation
end Erdos371
