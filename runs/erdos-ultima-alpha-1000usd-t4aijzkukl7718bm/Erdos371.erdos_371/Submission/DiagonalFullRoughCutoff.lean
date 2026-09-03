import Submission.FullLinearRoughCutoff
import Submission.PrimeWinnerPrimeWeightedEnergy

/-! A slow diagonal choice allows a subpower roughness cutoff while still
removing every divisor modulus up to N. The tail above N remains unestimated. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

noncomputable def rootRoughCutoff (k N : ℕ) : ℕ := ceilPowerCutoff (1/(k+1 : ℝ)) N

lemma rootRoughCutoff_power (k N : ℕ) : N≤(rootRoughCutoff k N)^(k+1) := by
  have h := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) (1/(k+1 : ℝ)))
    (Nat.le_ceil ((N : ℝ)^(1/(k+1 : ℝ)))) (k+1)
  rw [one_div,show (k+1 : ℝ)=((k+1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (by omega)] at h
  have h' : N≤⌈(N : ℝ)^((k+1 : ℕ) : ℝ)⁻¹⌉₊^(k+1) := by exact_mod_cast h
  simpa only [rootRoughCutoff,ceilPowerCutoff,one_div,Nat.cast_add,Nat.cast_one] using h'

lemma rootRoughCutoff_atTop (k : ℕ) : Tendsto (rootRoughCutoff k) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [eventually_ge_atTop (M^(k+1)+1)] with N hN
  by_contra h
  have hb : rootRoughCutoff k N≤M := by omega
  have hpow := Nat.pow_le_pow_left hb (k+1)
  have hn := rootRoughCutoff_power k N
  omega

lemma rootRoughCutoff_full_linear_tendsto (k : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, roughSmallDivisorSum (rootRoughCutoff k N) N (n+1))/N)
      atTop (𝓝 0) := by
  apply roughSmallDivisorSum_full_linear_tendsto (rootRoughCutoff k) (k+1) (rootRoughCutoff_atTop k)
  exact Eventually.of_forall fun N => (rootRoughCutoff_power k N).trans
    (Nat.pow_le_pow_left (Nat.le_succ _) _)

lemma rootRoughCutoff_log_eventually_le (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, Real.log (rootRoughCutoff k N+1 : ℝ)/Real.log N ≤ 2/(k+1 : ℝ) := by
  have ht : Tendsto (fun N : ℕ => Real.log 3/Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_lt_const (show (0 : ℝ)<1/(k+1 : ℝ) by positivity),
    eventually_gt_atTop (1 : ℕ)] with N ht hN
  have hlogN : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hb := div_le_div_of_nonneg_right
    (ceilPowerCutoff_succ_log_bound (1/(k+1 : ℝ)) (by positivity) N (by omega)) hlogN.le
  change Real.log (rootRoughCutoff k N+1 : ℝ)/Real.log N ≤ _ at hb
  have he : (Real.log 3+1/(k+1 : ℝ)*Real.log N)/Real.log N =
      Real.log 3/Real.log N+1/(k+1 : ℝ) := by field_simp
  rw [he] at hb
  rw [show (2 : ℝ)/(k+1)=1/(k+1)+1/(k+1) by ring]
  linarith

/-- This is a justified slow diagonal, not a uniform interchange of a
fixed-cutoff limit with a moving cutoff. All three constraints are enforced
in the finite maximization defining the index. -/
theorem exists_subpower_full_linear_rough_cutoff :
    ∃ B : ℕ → ℕ, Tendsto B atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ range N, roughSmallDivisorSum (B N) N (n+1))/N)
        atTop (𝓝 0) := by
  classical
  let P (N k : ℕ) : Prop := k≤rootRoughCutoff k N ∧
    Real.log (rootRoughCutoff k N+1 : ℝ)/Real.log N ≤ 2/(k+1 : ℝ) ∧
    ‖(∑ n ∈ range N, roughSmallDivisorSum (rootRoughCutoff k N) N (n+1))/N‖ ≤ 1/(k+1 : ℝ)
  have hP (k : ℕ) : ∀ᶠ N in atTop, P N k := by
    have he := (rootRoughCutoff_full_linear_tendsto k).norm
    simp only [norm_zero] at he
    filter_upwards [(rootRoughCutoff_atTop k).eventually_ge_atTop k,
      rootRoughCutoff_log_eventually_le k,
      he.eventually_lt_const
        (show (0 : ℝ)<1/(k+1 : ℝ) by positivity)] with N hb hl he
    exact ⟨hb,hl,by simpa only [norm_zero] using he.le⟩
  let K (N : ℕ) := Nat.findGreatest (P N) N
  let B (N : ℕ) := rootRoughCutoff (K N) N
  have hK : Tendsto K atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k,hP k] with N hNk hp
    exact Nat.le_findGreatest hNk hp
  have hPK : ∀ᶠ N in atTop, P N (K N) := by
    filter_upwards [hP 0] with N hp
    exact Nat.findGreatest_spec (Nat.zero_le N) hp
  have hB : Tendsto B atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hPK,hK.eventually_ge_atTop M] with N hp hk
    exact hk.trans hp.1
  have hi : Tendsto (fun N => 1/(K N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hK
  refine ⟨B,hB,?_,?_⟩
  · have hi2 := hi.const_mul 2
    simp only [mul_zero] at hi2
    apply squeeze_zero' (Eventually.of_forall fun N =>
      div_nonneg (Real.log_nonneg (show (1 : ℝ)≤B N+1 by have := Nat.cast_nonneg (α := ℝ) (B N); linarith)) (Real.log_natCast_nonneg N)) _ hi2
    filter_upwards [hPK] with N hp
    exact hp.2.1.trans_eq (by ring)
  · apply squeeze_zero_norm' _ hi
    exact hPK.mono fun N hp => hp.2.2

/-- The complete small-modulus estimate and subpower smooth sparsity reduce
the conjecture to the rough mixed tail with product cutoff EXACTLY N. -/
theorem density_iff_full_linear_rough_mixed_tail (B : ℕ → ℕ)
    (hlog : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hsmall : Tendsto (fun N : ℕ => (∑ n ∈ range N, roughSmallDivisorSum (B N) N (n+1))/N)
      atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N, roughMixedDivisorTail (B N) N (n+1))/N)
        atTop (𝓝 0) := by
  have hl := lowLeastDivisorGroup_shifted_average_zero_of_smooth_count B
    (subpower_smooth_count_tendsto_zero B hlog)
  have he := rough_one_sided_average_tendsto_zero B id
  have herr := (hsmall.add hl).add he
  simp only [add_zero] at herr
  have hid (N : ℕ) :
      (∑ n ∈ range N, roughSmallDivisorSum (B N) N (n+1))/N+
      (∑ n ∈ range N, lowLeastDivisorGroup (B N) (n+1))/N+
      ((∑ n ∈ range N, roughLargeDivisorTail (B N) N (n+1))/N-
        (∑ n ∈ range N, roughMixedDivisorTail (B N) N (n+1))/N) =
      -(∑ n ∈ range N, factorSign (n+1))/N-
        (∑ n ∈ range N, roughMixedDivisorTail (B N) N (n+1))/N := by
    have hz : (∑ n ∈ range N, roughSmallDivisorSum (B N) N (n+1))+
        (∑ n ∈ range N, lowLeastDivisorGroup (B N) (n+1))+
        (∑ n ∈ range N, roughLargeDivisorTail (B N) N (n+1)) =
        -(∑ n ∈ range N, factorSign (n+1)) := by
      rw [← sum_add_distrib,← sum_add_distrib,← sum_neg_distrib]
      apply sum_congr rfl
      intro n hn
      linarith [rough_small_add_tail_add_low (B N) N (n+1) (by omega)]
    rw [← add_div,← add_sub_assoc,← add_div,hz]
  have herr' : Tendsto (fun N : ℕ => -(∑ n ∈ range N, factorSign (n+1))/N-
      (∑ n ∈ range N, roughMixedDivisorTail (B N) N (n+1))/N) atTop (𝓝 0) := by
    apply herr.congr
    intro N
    exact hid N
  rw [density_iff_shifted_sign_average]
  constructor
  · intro h
    have ht := h.neg.sub herr'
    simp only [neg_zero,sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    have ht := (herr'.add h).neg
    simp only [add_zero,neg_zero] at ht
    apply ht.congr
    intro N
    ring

theorem exists_full_linear_rough_tail_criterion :
    ∃ B : ℕ → ℕ, Tendsto B atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      ({n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
        Tendsto (fun N : ℕ => (∑ n ∈ range N, roughMixedDivisorTail (B N) N (n+1))/N)
          atTop (𝓝 0)) := by
  obtain ⟨B,hB,hlog,hsmall⟩ := exists_subpower_full_linear_rough_cutoff
  exact ⟨B,hB,hlog,density_iff_full_linear_rough_mixed_tail B hlog hsmall⟩

#print axioms exists_subpower_full_linear_rough_cutoff
#print axioms density_iff_full_linear_rough_mixed_tail
#print axioms exists_full_linear_rough_tail_criterion
end Erdos371
