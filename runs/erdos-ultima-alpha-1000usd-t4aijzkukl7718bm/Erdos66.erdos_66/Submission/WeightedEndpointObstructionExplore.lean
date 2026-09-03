import FormalConjecturesUtil

/-! Unbalanced pairs obstruct a pointwise weighted transfer. The conclusion
below is about a different, weighted convolution, not the conjecture in Spec.lean. -/
namespace Erdos66WeightedEndpoint
open Filter AdditiveCombinatorics
open scoped Classical Topology

noncomputable def weightedIndicator (A : Set ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n ∈ A then w n else 0

noncomputable def weightedRep (A : Set ℕ) (w : ℕ → ℝ) : ℕ → ℝ :=
  sumConv (weightedIndicator A w) (weightedIndicator A w)

lemma endpoint_lower (A : Set ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) :
    w a*w b ≤ weightedRep A w (a+b) := by
  have hnon (n : ℕ) : 0 ≤ weightedIndicator A w n := by
    unfold weightedIndicator
    split_ifs <;> simp_all
  have hh := Finset.single_le_sum (s := Finset.antidiagonal (a+b)) (a := (a,b))
    (f := fun p : ℕ × ℕ ↦ weightedIndicator A w p.1*weightedIndicator A w p.2)
    (fun p hp ↦ mul_nonneg (hnon p.1) (hnon p.2))
    (Finset.mem_antidiagonal.mpr (show a+b=a+b from rfl))
  simpa only [weightedIndicator,if_pos ha,if_pos hb] using hh

/-- Any fixed positive-weight point, paired with arbitrarily late points,
creates arbitrarily large normalized weighted counts under these hypotheses. -/
theorem endpoint_peaks {A : Set ℕ} (hA : A.Infinite) (w g : ℕ → ℝ)
    (hw : ∀ n, 0 < w n) (hanti : Antitone w) (hg : ∀ n, 0 ≤ g n)
    (hscale : Tendsto (fun n ↦ w n*g n) atTop atTop) :
    ∀ R : ℝ, ∀ N : ℕ, ∃ n ≥ N, R < weightedRep A w n*g n := by
  obtain ⟨a,ha⟩ := hA.nonempty
  intro R N
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((tendsto_atTop.1 (hscale.const_mul_atTop (hw a))) (R+1))
  obtain ⟨b,hb,hbN⟩ := hA.exists_gt (max M N)
  let n := a+b
  have hnM : M ≤ n := by dsimp [n]; omega
  have hnN : N ≤ n := by dsimp [n]; omega
  have hmono : w n ≤ w b := hanti (by dsimp [n]; omega)
  have hbase : w a*w n ≤ weightedRep A w n :=
    (mul_le_mul_of_nonneg_left hmono (hw a).le).trans
      (endpoint_lower A w (fun n ↦ (hw n).le) ha hb)
  have hbound := mul_le_mul_of_nonneg_right hbase (hg n)
  have hlarge := hM n hnM
  exact ⟨n,hnN,by nlinarith⟩

/-- These weighted normalizations cannot have any finite limit, even if the
unweighted representation function might have the conjectured logarithmic limit. -/
theorem no_finite_weighted_limit {A : Set ℕ} (hA : A.Infinite) (w g : ℕ → ℝ)
    (hw : ∀ n, 0 < w n) (hanti : Antitone w) (hg : ∀ n, 0 ≤ g n)
    (hscale : Tendsto (fun n ↦ w n*g n) atTop atTop) (c : ℝ) :
    ¬ Tendsto (fun n ↦ weightedRep A w n*g n) atTop (𝓝 c) := by
  intro h
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h.eventually_lt_const (lt_add_one c))
  obtain ⟨n,hn,hbig⟩ := endpoint_peaks hA w g hw hanti hg hscale (c+1) N
  linarith [hN n hn]

lemma power_over_log_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ)+2)^α/Real.log ((n : ℝ)+2)) atTop atTop := by
  have hx : Tendsto (fun n : ℕ ↦ (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ)+2)/((n : ℝ)+2)^α)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      (isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero.comp hx
  have hh' : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ)+2)/((n : ℝ)+2)^α)
      atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hh,Eventually.of_forall (fun n ↦ ?_)⟩
    exact div_pos (Real.log_pos (by nlinarith [Nat.cast_nonneg (α := ℝ) n])) (Real.rpow_pos_of_pos (by positivity) α)
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp hh'

/-- Power weighting can create unbounded normalized endpoint peaks for every
infinite set. For α=1/4 this rejects pointwise comparison with the natural
log(n)/sqrt(n) scale of the correspondingly weighted fractional profile. -/
theorem power_weight_endpoint_peaks {A : Set ℕ} (hA : A.Infinite)
    (α : ℝ) (hα : 0 < α) :
    ∀ R : ℝ, ∀ N : ℕ, ∃ n ≥ N,
      R < weightedRep A (fun k ↦ ((k : ℝ)+2)^(-α)) n *
        (((n : ℝ)+2)^(2*α)/Real.log ((n : ℝ)+2)) := by
  apply endpoint_peaks hA
  · intro n
    exact Real.rpow_pos_of_pos (by positivity) _
  · intro n m hnm
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 2) (by linarith)
  · intro n
    apply div_nonneg (Real.rpow_nonneg (by positivity) _)
    exact (Real.log_pos (by nlinarith [Nat.cast_nonneg (α := ℝ) n])).le
  · convert power_over_log_tendsto α hα using 1
    funext n
    rw [← mul_div_assoc,← Real.rpow_add (by positivity)]
    congr 2
    ring

/-- No finite limit exists for this power-weighted expression. This theorem
must not be substituted for a negation of the original unweighted conjecture. -/
theorem power_weight_no_finite_limit {A : Set ℕ} (hA : A.Infinite)
    (α : ℝ) (hα : 0 < α) (c : ℝ) :
    ¬ Tendsto (fun n ↦ weightedRep A (fun k ↦ ((k : ℝ)+2)^(-α)) n *
      (((n : ℝ)+2)^(2*α)/Real.log ((n : ℝ)+2))) atTop (𝓝 c) := by
  intro h
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h.eventually_lt_const (lt_add_one c))
  obtain ⟨n,hn,hbig⟩ := power_weight_endpoint_peaks hA α hα (c+1) N
  linarith [hN n hn]

end Erdos66WeightedEndpoint
