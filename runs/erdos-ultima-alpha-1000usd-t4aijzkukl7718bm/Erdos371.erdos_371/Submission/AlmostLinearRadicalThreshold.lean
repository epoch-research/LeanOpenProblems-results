import Submission.LargeWindowMixedRectangle
import Submission.RoughEndpointScale

/-! A justified slow diagonal supplies an almost-linear threshold A with
negligible small-radical error. All fixed powers are checked before selection. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma nat_power_eventually_le_of_log_ratio (X : ℕ → ℕ) (v : ℝ) (r m : ℕ) (hr : 0 < r)
    (hX : ∀ᶠ N : ℕ in atTop, 0 < X N)
    (hlog : Tendsto (fun N : ℕ => Real.log (X N)/Real.log N) atTop (𝓝 v))
    (hvr : v*(r : ℝ) < m) :
    ∀ᶠ N : ℕ in atTop, (X N)^r ≤ N^m := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hv : v < (m : ℝ)/r := (lt_div_iff₀ hrR).mpr hvr
  filter_upwards [hX,hlog.eventually_lt_const hv,eventually_gt_atTop (1 : ℕ)] with N hx hl hN
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hl' := (div_lt_iff₀ hlogN).mp hl
  have hh := mul_lt_mul_of_pos_left hl' hrR
  have hden := div_mul_cancel₀ (m : ℝ) hrR.ne'
  have hlogpow : (r : ℝ)*Real.log (X N) ≤ (m : ℝ)*Real.log N := by nlinarith
  apply nat_pow_le_of_log_le (X N) (N^m) r hx (Nat.pow_pos (by omega))
  simpa only [Nat.cast_pow,Real.log_pow] using hlogpow

lemma short_radical_threshold_zero (B H X : ℕ → ℕ) (k q : ℕ) (hq : 2 ≤ q)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hH : ∀ᶠ N : ℕ in atTop, H N ≤ B N+1)
    (hX : ∀ᶠ N : ℕ in atTop, (X N)^(2*q) ≤ N^(2*q-3)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, if
      roughRadical (B N) ((n+1)*(n+2)) ≤ (H N*N)*((B N)^k*X N)
      then (1 : ℝ) else 0)/N) atTop (𝓝 0) := by
  have hsize : ∀ᶠ N in atTop, ((H N*N)*((B N)^k*X N))^(2*q) ≤ (N+1)^(2*(2*q-1)) := by
    filter_upwards [hH,hX,subpower_pow_eventually_nat_le B hB ((k+1)*(2*q))] with N hh hx hb
    have hH' : H N*(B N)^k ≤ (B N+1)^(k+1) := by
      calc
        _ ≤ (B N+1)*(B N+1)^k := Nat.mul_le_mul hh (Nat.pow_le_pow_left (Nat.le_succ _) k)
        _ = _ := by rw [pow_succ]; ring
    have hHp : (H N*(B N)^k)^(2*q) ≤ N := by
      rw [pow_mul] at hb
      exact (Nat.pow_le_pow_left hH' (2*q)).trans hb
    have he : (H N*N)*((B N)^k*X N)=(H N*(B N)^k)*N*X N := by ring
    rw [he,mul_pow,mul_pow]
    calc
      _ ≤ N*N^(2*q)*N^(2*q-3) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hHp) hx
      _ = N^(2*(2*q-1)) := by rw [← pow_succ',← pow_add]; congr 1; omega
      _ ≤ (N+1)^(2*(2*q-1)) := Nat.pow_le_pow_left (Nat.le_succ _) _
  exact roughRadical_small_power_proportion_zero B (fun N => (H N*N)*((B N)^k*X N))
    (2*q-1) hBt hB (by simpa only [show 2*q-1+1=2*q by omega] using hsize)

/-- A may depend on the fixed low degree k. It does not enter the selected
external weight, which will use the full endpoint N. -/
theorem exists_almost_linear_radical_threshold (B H : ℕ → ℕ) (k : ℕ)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hH : ∀ᶠ N : ℕ in atTop, H N ≤ B N+1) :
    ∃ A : ℕ → ℕ, (∀ᶠ N : ℕ in atTop, 1 ≤ A N ∧ A N ≤ N) ∧
      Tendsto (fun N : ℕ => Real.log (A N)/Real.log N) atTop (𝓝 1) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ range N, if
        roughRadical (B N) ((n+1)*(n+2)) ≤ (H N*N)*((B N)^k*A N)
        then (1 : ℝ) else 0)/N) atTop (𝓝 0) := by
  classical
  let v (j : ℕ) : ℝ := 1-2/(j+4 : ℝ)
  let X (j N : ℕ) : ℕ := ceilPowerCutoff (v j) N
  have hv (j : ℕ) : 0 < v j := by
    dsimp only [v]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hdiv : (2 : ℝ)/(j+4) < 1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < j+4)).mpr (by linarith)
    linarith
  have hv1 (j : ℕ) : v j ≤ 1 := by
    dsimp [v]
    have hh : (0 : ℝ) ≤ 2/(j+4 : ℝ) := by positivity
    linarith
  have hXpos (j : ℕ) : ∀ᶠ N : ℕ in atTop, 0 < X j N := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hh : (1 : ℝ) ≤ X j N := (Real.one_le_rpow (show (1 : ℝ) ≤ N by exact_mod_cast hN) (hv j).le).trans (Nat.le_ceil _)
    exact_mod_cast (show (0 : ℝ) < X j N by linarith)
  have hXpow (j : ℕ) : ∀ᶠ N : ℕ in atTop, (X j N)^(2*(j+4)) ≤ N^(2*(j+4)-3) := by
    apply nat_power_eventually_le_of_log_ratio (X j) (v j) (2*(j+4)) (2*(j+4)-3) (by omega)
      (hXpos j) (ceilPowerCutoff_log_ratio_tendsto (v j) (hv j))
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    dsimp only [v]
    rw [Nat.cast_sub (by omega : 3 ≤ 2*(j+4))]
    push_cast
    have hden := div_mul_cancel₀ (2 : ℝ) (by positivity : (j+4 : ℝ) ≠ 0)
    nlinarith
  let P (N j : ℕ) : Prop := 1 ≤ X j N ∧ X j N ≤ N ∧ v j ≤ Real.log (X j N)/Real.log N ∧
    (∑ n ∈ range N, if roughRadical (B N) ((n+1)*(n+2)) ≤ (H N*N)*((B N)^k*X j N)
      then (1 : ℝ) else 0)/N ≤ 1/(j+1 : ℝ)
  have hP (j : ℕ) : ∀ᶠ N : ℕ in atTop, P N j := by
    have hr := short_radical_threshold_zero B H (X j) k (j+4) (by omega) hBt hB hH (hXpow j)
    filter_upwards [hXpos j,eventually_gt_atTop (1 : ℕ),
      hr.eventually_lt_const (show (0 : ℝ) < 1/(j+1 : ℝ) by positivity)] with N hx hN hh
    refine ⟨hx,?_,?_,hh.le⟩
    · change ⌈(N : ℝ)^(v j)⌉₊ ≤ N
      apply Nat.ceil_le.mpr
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ N by exact_mod_cast hN.le) (hv1 j)
    · exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hN))).mpr
        (ceilPowerCutoff_log_bounds (v j) (hv j) N hN).1
  let J (N : ℕ) := Nat.findGreatest (P N) N
  let A (N : ℕ) := X (J N) N
  have hJ : Tendsto J atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [hP j,eventually_ge_atTop j] with N hp hj
    exact Nat.le_findGreatest hj hp
  have hPJ : ∀ᶠ N : ℕ in atTop, P N (J N) := by
    filter_upwards [hP 0] with N hp
    exact Nat.findGreatest_spec (Nat.zero_le N) hp
  refine ⟨A,hPJ.mono (fun N hp => ⟨hp.1,hp.2.1⟩),?_,?_⟩
  · have hvlim : Tendsto (fun N => v (J N)) atTop (𝓝 1) := by
      have hden : Tendsto (fun N : ℕ => (J N+4 : ℝ)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.comp hJ).atTop_add tendsto_const_nhds
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
        (show Tendsto (fun N : ℕ => 2/(J N+4 : ℝ)) atTop (𝓝 0) from tendsto_const_nhds.div_atTop hden)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hvlim tendsto_const_nhds
    · exact hPJ.mono fun N hp => hp.2.2.1
    · filter_upwards [hPJ,eventually_gt_atTop (1 : ℕ)] with N hp hN
      have hAR : (0 : ℝ) < A N := by exact_mod_cast (show 0 < A N by have := hp.1; dsimp [A]; omega)
      apply (div_le_iff₀ (Real.log_pos (by exact_mod_cast hN))).mpr
      simpa only [one_mul] using Real.log_le_log hAR (show (A N : ℝ) ≤ N by exact_mod_cast hp.2.1)
  · apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg
      (sum_nonneg fun n _ => by split_ifs <;> norm_num) (Nat.cast_nonneg N)) _
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hJ)
    exact hPJ.mono fun N hp => hp.2.2.2

#print axioms exists_almost_linear_radical_threshold
end Erdos371
