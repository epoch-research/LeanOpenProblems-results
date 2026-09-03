import Submission.DiagonalFullRoughCutoff

/-! The small rough-modulus estimate extends to a slowly growing multiple
of N. The complementary tail is still a signed, input-weighted problem. -/
namespace Erdos371
open Finset Filter
open scoped Topology

theorem roughSmallDivisorSum_fixed_multiple_tendsto (B : ℕ → ℕ) (K H : ℕ)
    (hH : 0 < H) (hB : Tendsto B atTop atTop)
    (hsize : ∀ᶠ N in atTop, H*N≤(B N+1)^K) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, roughSmallDivisorSum (B N) (H*N) (n+1))/N)
      atTop (𝓝 0) := by
  have hM : Tendsto (fun N : ℕ => H*N) atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with N hN
    have hle : N≤H*N := by nlinarith
    exact hN.trans hle
  have ht := (roughNumberCount_reindexed_succ_tendsto B (fun N => H*N) hB hM).const_mul
    (((2 : ℝ)^K+1)*H)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hsize,hB.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℕ)] with N hs hb hn
  rw [norm_div,Real.norm_natCast]
  have h := div_le_div_of_nonneg_right
    (roughSmallDivisorSum_bounded_factor_length (B N) K (H*N) N hb hs) (Nat.cast_nonneg (α := ℝ) N)
  apply h.trans_eq
  have hH0 : (H : ℝ)≠0 := by exact_mod_cast hH.ne'
  have hN0 : (N : ℝ)≠0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

lemma rootRoughCutoff_multiple_tendsto (k : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      roughSmallDivisorSum (rootRoughCutoff k N) ((k+1)*N) (n+1))/N) atTop (𝓝 0) := by
  apply roughSmallDivisorSum_fixed_multiple_tendsto (rootRoughCutoff k) ((k+1)*2) (k+1)
    (by omega) (rootRoughCutoff_atTop k)
  filter_upwards [eventually_ge_atTop (k+1)] with N hn
  have hb := (rootRoughCutoff_power k N).trans (Nat.pow_le_pow_left (Nat.le_succ _) (k+1))
  calc
    (k+1)*N ≤ N*N := Nat.mul_le_mul_right N hn
    _ ≤ ((rootRoughCutoff k N+1)^(k+1))*((rootRoughCutoff k N+1)^(k+1)) := Nat.mul_le_mul hb hb
    _ = _ := by rw [pow_mul,pow_two]

/-- Both the roughness cutoff and the divisor-cutoff multiplier may tend
to infinity, while the roughness cutoff remains subpower. -/
theorem exists_subpower_superlinear_rough_cutoff :
    ∃ B H : ℕ → ℕ, Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N≤B N+1) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ range N, roughSmallDivisorSum (B N) (H N*N) (n+1))/N)
        atTop (𝓝 0) := by
  classical
  let P (N k : ℕ) : Prop := k≤rootRoughCutoff k N ∧
    Real.log (rootRoughCutoff k N+1 : ℝ)/Real.log N ≤ 2/(k+1 : ℝ) ∧
    ‖(∑ n ∈ range N, roughSmallDivisorSum (rootRoughCutoff k N) ((k+1)*N) (n+1))/N‖ ≤ 1/(k+1 : ℝ)
  have hP (k : ℕ) : ∀ᶠ N in atTop, P N k := by
    have he := (rootRoughCutoff_multiple_tendsto k).norm
    simp only [norm_zero] at he
    filter_upwards [(rootRoughCutoff_atTop k).eventually_ge_atTop k,
      rootRoughCutoff_log_eventually_le k,
      he.eventually_lt_const (show (0 : ℝ)<1/(k+1 : ℝ) by positivity)] with N hb hl he
    exact ⟨hb,hl,he.le⟩
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
  refine ⟨B,fun N => K N+1,hB,(tendsto_add_atTop_nat 1).comp hK,?_,?_,?_⟩
  · have hi2 := hi.const_mul 2
    simp only [mul_zero] at hi2
    apply squeeze_zero' (Eventually.of_forall fun N =>
      div_nonneg (Real.log_nonneg (show (1 : ℝ)≤B N+1 by have := Nat.cast_nonneg (α := ℝ) (B N); linarith))
        (Real.log_natCast_nonneg N)) _ hi2
    filter_upwards [hPK] with N hp
    exact hp.2.1.trans_eq (by ring)
  · exact hPK.mono fun N hp => Nat.add_le_add_right hp.1 1
  · apply squeeze_zero_norm' _ hi
    exact hPK.mono fun N hp => hp.2.2

/-- The exact tail criterion permits an arbitrary divisor cutoff D. -/
theorem density_iff_rough_mixed_tail_of_small_and_subpower (B D : ℕ → ℕ)
    (hlog : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hsmall : Tendsto (fun N : ℕ => (∑ n ∈ range N, roughSmallDivisorSum (B N) (D N) (n+1))/N)
      atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N, roughMixedDivisorTail (B N) (D N) (n+1))/N)
        atTop (𝓝 0) := by
  have hl := lowLeastDivisorGroup_shifted_average_zero_of_smooth_count B
    (subpower_smooth_count_tendsto_zero B hlog)
  have he := rough_one_sided_average_tendsto_zero B D
  have herr := (hsmall.add hl).add he
  simp only [add_zero] at herr
  have hid (N : ℕ) :
      (∑ n ∈ range N, roughSmallDivisorSum (B N) (D N) (n+1))/N+
      (∑ n ∈ range N, lowLeastDivisorGroup (B N) (n+1))/N+
      ((∑ n ∈ range N, roughLargeDivisorTail (B N) (D N) (n+1))/N-
        (∑ n ∈ range N, roughMixedDivisorTail (B N) (D N) (n+1))/N) =
      -(∑ n ∈ range N, factorSign (n+1))/N-
        (∑ n ∈ range N, roughMixedDivisorTail (B N) (D N) (n+1))/N := by
    have hz : (∑ n ∈ range N, roughSmallDivisorSum (B N) (D N) (n+1))+
        (∑ n ∈ range N, lowLeastDivisorGroup (B N) (n+1))+
        (∑ n ∈ range N, roughLargeDivisorTail (B N) (D N) (n+1)) =
        -(∑ n ∈ range N, factorSign (n+1)) := by
      rw [← sum_add_distrib,← sum_add_distrib,← sum_neg_distrib]
      apply sum_congr rfl
      intro n hn
      linarith [rough_small_add_tail_add_low (B N) (D N) (n+1) (by omega)]
    rw [← add_div,← add_sub_assoc,← add_div,hz]
  have herr' : Tendsto (fun N : ℕ => -(∑ n ∈ range N, factorSign (n+1))/N-
      (∑ n ∈ range N, roughMixedDivisorTail (B N) (D N) (n+1))/N) atTop (𝓝 0) := by
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

theorem exists_superlinear_rough_tail_criterion :
    ∃ B H : ℕ → ℕ, Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N≤B N+1) ∧
      ({n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
        Tendsto (fun N : ℕ => (∑ n ∈ range N, roughMixedDivisorTail (B N) (H N*N) (n+1))/N)
          atTop (𝓝 0)) := by
  obtain ⟨B,H,hB,hH,hlog,hHB,hsmall⟩ := exists_subpower_superlinear_rough_cutoff
  exact ⟨B,H,hB,hH,hlog,hHB,
    density_iff_rough_mixed_tail_of_small_and_subpower B (fun N => H N*N) hlog hsmall⟩

/-- A divisor larger than H*N has a complementary divisor at most
(N+1)/H whenever the original integer is at most N*(N+1). -/
lemma superlinear_divisor_complement_bound (H N R d : ℕ) (hN : 0<N)
    (hR : R≤N*(N+1)) (hd : d∣R) (hlarge : H*N<d) :
    H*(R/d)≤N+1 := by
  have h : (H*(R/d))*N≤(N+1)*N := by
    calc
      _ = (R/d)*(H*N) := by ring
      _ ≤ (R/d)*d := Nat.mul_le_mul_left _ hlarge.le
      _ = R := Nat.div_mul_cancel hd
      _ ≤ (N+1)*N := by simpa only [Nat.mul_comm] using hR
  exact (mul_le_mul_iff_right₀ hN).mp (by simpa only [Nat.mul_comm] using h)

theorem superlinear_divisor_complement_ratio_tendsto (H R d : ℕ → ℕ)
    (hH : Tendsto H atTop atTop)
    (hdata : ∀ᶠ N : ℕ in atTop, R N≤N*(N+1) ∧ d N∣R N ∧ H N*N<d N) :
    Tendsto (fun N : ℕ => ((R N/d N : ℕ) : ℝ)/N) atTop (𝓝 0) := by
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp hH
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ ht
  filter_upwards [hdata,hH.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℕ)] with N hd hH' hN
  have hb := superlinear_divisor_complement_bound (H N) N (R N) (d N) hN hd.1 hd.2.1 hd.2.2
  have hb' : (H N : ℝ)*((R N/d N : ℕ) : ℝ)≤(N : ℝ)+1 := by exact_mod_cast hb
  apply (div_le_div_iff₀ (by exact_mod_cast hN : (0 : ℝ)<N)
    (by exact_mod_cast hH' : (0 : ℝ)<H N)).mpr
  have hn' : (1 : ℝ)≤N := by exact_mod_cast hN
  nlinarith

#print axioms roughSmallDivisorSum_fixed_multiple_tendsto
#print axioms exists_subpower_superlinear_rough_cutoff
#print axioms exists_superlinear_rough_tail_criterion
#print axioms superlinear_divisor_complement_ratio_tendsto
end Erdos371
