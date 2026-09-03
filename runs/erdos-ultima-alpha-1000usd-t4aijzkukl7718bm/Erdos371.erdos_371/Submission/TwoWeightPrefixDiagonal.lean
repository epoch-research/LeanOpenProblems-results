import Submission.TwoWeightComplementSelection
import Submission.ExponentialRoughCutoff

/-! A single cutoff controls every fixed short degree for one prescribed
bounded weight. The weight is independent of the selected rough cutoff. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma exists_two_weight_maximal_prefix_row (w : ℕ → Bool → ℕ → ℝ)
    (hw : ∀ N b n, n < N → |w N b n| ≤ 1) (d k : ℕ) :
    ∃ B : ℕ → ℕ, ∃ L : ℕ, ∀ᶠ N : ℕ in atTop,
      k≤B N ∧ 1≤B N ∧ (k+1)*N≤(B N+1)^L ∧
      Real.log (B N+1 : ℝ)/Real.log N≤2/(k+1 : ℝ) ∧
      (∀ b : Bool, ∀ X ≤ (B N)^d, |(∑ n ∈ range N, w N b n*untruncatedComplementPrefix (B N) X n)/N|≤1/(k+1 : ℝ)) ∧
      roughPrefixBudget (B N) L ((k+1)*N)/N≤1/(k+1 : ℝ) := by
  classical
  obtain ⟨u,hu,_,hex⟩ := exists_power_cutoff_two_weight_maximal_cancellation d (1/(k+1 : ℝ)) (1/(k+1 : ℝ))
    (by positivity) (by positivity)
  let Good (N B : ℕ) : Prop := (N : ℝ)^u≤B ∧ (B : ℝ)≤(N : ℝ)^(1/(k+1 : ℝ)) ∧
    ∀ b : Bool, ∀ X ≤ B^d, |(∑ n ∈ range N, w N b n*untruncatedComplementPrefix B X n)/N|<1/(k+1 : ℝ)
  let B (N : ℕ) : ℕ := if h : ∃ b, Good N b then Classical.choose h else 0
  have hgood : ∀ᶠ N in atTop, Good N (B N) := by
    filter_upwards [hex] with N hN
    have h : ∃ b, Good N b := hN (w N) (hw N)
    dsimp only [B]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hB : Tendsto B atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    have hp := ((tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (M : ℝ)
    filter_upwards [hgood,hp] with N hg hp
    exact_mod_cast hp.trans hg.1
  obtain ⟨l,hl⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hu).exists
  let L := (l+1)*2
  have hsize : ∀ᶠ N in atTop, (k+1)*N≤(B N+1)^L := by
    filter_upwards [hgood,eventually_ge_atTop (max 1 (k+1))] with N hg hN
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast (le_max_left 1 (k+1)).trans hN
    have hr : rootRoughCutoff l N≤B N := by
      apply Nat.ceil_le.mpr
      exact (Real.rpow_le_rpow_of_exponent_le hN1 hl.le).trans hg.1
    have hp : N≤(B N+1)^(l+1) := (rootRoughCutoff_power l N).trans
      (Nat.pow_le_pow_left (hr.trans (Nat.le_succ _)) _)
    calc
      _ ≤ N*N := Nat.mul_le_mul_right N ((le_max_right 1 (k+1)).trans hN)
      _ ≤ ((B N+1)^(l+1))*((B N+1)^(l+1)) := Nat.mul_le_mul hp hp
      _ = _ := by dsimp [L]; rw [pow_mul,pow_two]
  have hlog : ∀ᶠ N in atTop, Real.log (B N+1 : ℝ)/Real.log N≤2/(k+1 : ℝ) := by
    filter_upwards [hgood,rootRoughCutoff_log_eventually_le k] with N hg hr
    have hle : B N≤rootRoughCutoff k N := by
      have hh := hg.2.1.trans (Nat.le_ceil ((N : ℝ)^(1/(k+1 : ℝ))))
      change B N≤⌈(N : ℝ)^(1/(k+1 : ℝ))⌉₊
      exact_mod_cast hh
    apply le_trans _ hr
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hle 1
  have hbudget := roughPrefixBudget_fixed_multiple_tendsto B L (k+1) (by omega) hB
  refine ⟨B,L,?_⟩
  filter_upwards [hgood,hsize,hlog,hB.eventually_ge_atTop k,hB.eventually_ge_atTop 1,
    hbudget.eventually_lt_const (show (0 : ℝ)<1/(k+1 : ℝ) by positivity)] with N hg hs hl hk h1 hb
  exact ⟨hk,h1,hs,hl,(fun b X hX => (hg.2.2 b X hX).le),hb.le⟩



theorem exists_two_weight_maximal_prefix_diagonal (w : ℕ → Bool → ℕ → ℝ)
    (hw : ∀ N b n, n < N → |w N b n| ≤ 1) :
    ∃ B H K : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto K atTop atTop ∧
      Tendsto (fun N => (K N+1 : ℝ)*(Real.log (B N+1 : ℝ)/Real.log N)) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, ∀ b : Bool, ∀ X ≤ (B N)^(K N),
        |(∑ n ∈ range N, w N b n*untruncatedComplementPrefix (B N) X n)/N| ≤ 1/(K N+1 : ℝ)) := by
  classical
  choose R L hrow using fun k => exists_two_weight_maximal_prefix_row w hw k ((k+1)^2)
  let P (N k : ℕ) : Prop := (k+1)^2 ≤ R k N ∧ 1 ≤ R k N ∧
    ((k+1)^2+1)*N ≤ (R k N+1)^(L k) ∧
    Real.log (R k N+1 : ℝ)/Real.log N ≤ 2/((k+1)^2+1 : ℝ) ∧
    (∀ b : Bool, ∀ X ≤ (R k N)^k, |(∑ n ∈ range N, w N b n*untruncatedComplementPrefix (R k N) X n)/N| ≤
      1/((k+1)^2+1 : ℝ)) ∧
    roughPrefixBudget (R k N) (L k) (((k+1)^2+1)*N)/N ≤ 1/((k+1)^2+1 : ℝ)
  let K (N : ℕ) := Nat.findGreatest (P N) N
  let B (N : ℕ) := R (K N) N
  let H (N : ℕ) := (K N+1)^2+1
  let C (N : ℕ) := roughPrefixBudget (B N) (L (K N)) (H N*N)
  have hP (k : ℕ) : ∀ᶠ N in atTop, P N k := by
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hrow k
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
    have hh : K N ≤ (K N+1)^2 := by nlinarith
    exact hk.trans (hh.trans hp.1)
  have hH : Tendsto H atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hK.eventually_ge_atTop M] with N hk
    dsimp only [H]
    nlinarith
  have hi : Tendsto (fun N => 1/(K N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hK
  have hfrac (N : ℕ) : 1/((K N+1)^2+1 : ℝ) ≤ 1/(K N+1 : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    have := Nat.cast_nonneg (α := ℝ) (K N)
    nlinarith
  refine ⟨B,H,K,C,hB,hH,hK,?_,?_,?_,?_,?_,?_⟩
  · have hi2 := hi.const_mul 2
    simp only [mul_zero] at hi2
    apply squeeze_zero' (Eventually.of_forall fun N => mul_nonneg (by positivity)
      (div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (B N); linarith))
        (Real.log_natCast_nonneg N))) _ hi2
    filter_upwards [hPK] with N hp
    have hpos : (0 : ℝ) < K N+1 := by positivity
    have hden : (0 : ℝ) < (K N+1)^2+1 := by positivity
    calc
      _ ≤ (K N+1 : ℝ)*(2/((K N+1)^2+1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hp.2.2.2.1 hpos.le
      _ ≤ 2/(K N+1 : ℝ) := by
        rw [show (K N+1 : ℝ)*(2/((K N+1)^2+1 : ℝ)) =
          (2*(K N+1))/((K N+1)^2+1) by ring]
        apply (div_le_div_iff₀ hden hpos).mpr
        nlinarith
      _ = _ := by ring
  · exact hPK.mono fun N hp => Nat.add_le_add_right hp.1 1
  · intro N
    exact roughPrefixBudget_nonneg _ _ _
  · filter_upwards [hPK] with N hp
    intro M
    exact roughSmallDivisorSum_prefix_budget (B N) (L (K N)) (H N*N) M hp.2.1 hp.2.2.1
  · apply squeeze_zero' (Eventually.of_forall fun N =>
      div_nonneg (roughPrefixBudget_nonneg _ _ _) (Nat.cast_nonneg N)) _ hi
    exact hPK.mono fun N hp => hp.2.2.2.2.2.trans (hfrac N)
  · filter_upwards [hPK] with N hp
    intro b X hX
    exact (hp.2.2.2.2.1 b X hX).trans (hfrac N)


theorem exists_two_weight_untruncated_prefix_cutoffs (w : ℕ → Bool → ℕ → ℝ)
    (hw : ∀ N b n, n < N → |w N b n| ≤ 1) :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ b : Bool, ∀ X ≤ (B N)^k,
        |(∑ n ∈ range N, w N b n*untruncatedComplementPrefix (B N) X n)/N| < ε) := by
  obtain ⟨B,H,K,C,hB,hH,hK,hweighted,hHB,hC,hbudget,hClim,hmax⟩ := exists_two_weight_maximal_prefix_diagonal w hw
  have hnonneg (N : ℕ) : 0 ≤ Real.log (B N+1 : ℝ)/Real.log N :=
    div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (B N); linarith)) (Real.log_natCast_nonneg N)
  have hlog : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => hnonneg N) _ hweighted
    intro N
    have hh : (1 : ℝ) ≤ K N+1 := by have := Nat.cast_nonneg (α := ℝ) (K N); linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (hnonneg N)
  have hi : Tendsto (fun N => 1/(K N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hK
  have hfixed (k : ℕ) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ b : Bool, ∀ X ≤ (B N)^k,
      |(∑ n ∈ range N, w N b n*untruncatedComplementPrefix (B N) X n)/N| < ε := by
    filter_upwards [hmax,hK.eventually_ge_atTop k,hB.eventually_gt_atTop 0,hi.eventually_lt_const hε]
      with N hm hk hb hi
    intro b X hX
    exact (hm b X (hX.trans (Nat.pow_le_pow_right hb hk))).trans_lt hi
  exact ⟨B,H,C,hB,hH,hlog,hHB,hC,hbudget,hClim,
    hfixed⟩


#print axioms exists_two_weight_untruncated_prefix_cutoffs
end Erdos371
