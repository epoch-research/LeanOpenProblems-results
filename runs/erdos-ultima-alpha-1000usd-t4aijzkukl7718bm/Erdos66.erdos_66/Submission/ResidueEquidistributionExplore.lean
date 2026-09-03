import Submission.ResidueSeriesExplore

/-! A necessary residue-equidistribution condition for any witness to Erdős 66.
The original existence conjecture remains unresolved. -/
namespace Erdos66ResidueEquidistribution
open Filter AdditiveCombinatorics Erdos66Generating Erdos66MixedEnergy
  Erdos66ResidueSeries Erdos66ConvRigidity
open scoped Topology Classical

noncomputable def weightedIndicator (A : Set ℕ) (r : ℝ) (n : ℕ) : ℝ := indicator A n * r ^ n

lemma weightedIndicator_conv (A : Set ℕ) (r : ℝ) (n : ℕ) :
    sumConv (weightedIndicator A r) (weightedIndicator A r) n = (sumRep A n : ℝ) * r ^ n := by
  unfold sumConv weightedIndicator
  calc
    _ = (∑ p ∈ Finset.antidiagonal n, indicator A p.1 * indicator A p.2) * r ^ n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.mem_antidiagonal.mp hp, pow_add]
      ring
    _ = _ := by rw [sum_indicator_antidiagonal]

lemma conv_div (f : G → ℝ) [AddCommGroup G] [Fintype G] (d : ℝ) (z : G) :
    conv (fun x ↦ f x / d) (fun x ↦ f x / d) z = conv f f z / d ^ 2 := by
  simp only [conv, div_mul_div_comm, pow_two, Finset.sum_div]

variable (m : ℕ) [NeZero m]

noncomputable def residueMass (A : Set ℕ) (r : ℝ) (z : ZMod m) : ℝ :=
  push m (weightedIndicator A r) z

noncomputable def normalizedMass (A : Set ℕ) (r : ℝ) (z : ZMod m) : ℝ :=
  residueMass m A r z / series (indicator A) r

lemma sum_residueMass (A : Set ℕ) {r : ℝ} (hr : |r| < 1) :
    (∑ z : ZMod m, residueMass m A r z) = series (indicator A) r :=
  sum_push m (summable_indicator A hr)

lemma residueMass_conv (A : Set ℕ) {r : ℝ} (hr : |r| < 1) (z : ZMod m) :
    conv (residueMass m A r) (residueMass m A r) z =
      push m (fun n ↦ (sumRep A n : ℝ) * r ^ n) z := by
  unfold residueMass
  have hs : Summable (weightedIndicator A r) := summable_indicator A hr
  rw [push_convolution m hs hs]
  congr 2
  funext n
  exact weightedIndicator_conv A r n

lemma witness_series_eventually_ne_zero {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∀ᶠ r : ℝ in 𝓝[<] 1, series (indicator A) r ≠ 0 := by
  have hcpos := Erdos66Explore.limit_pos hc h
  filter_upwards [(witness_generating_square_limit h).eventually (eventually_gt_nhds hcpos)] with r hr
  intro hz
  simp only [hz, zero_pow (by omega : 2 ≠ 0), zero_mul, zero_div] at hr
  exact lt_irrefl _ hr

lemma normalizedMass_conv_limit {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) (z : ZMod m) :
    Tendsto (fun r : ℝ ↦ conv (normalizedMass m A r) (normalizedMass m A r) z)
      (𝓝[<] 1) (𝓝 (1 / m)) := by
  have hden : Tendsto (fun r : ℝ ↦ series (indicator A) r ^ 2 * kernel r)
      (𝓝[<] 1) (𝓝 c) := by
    simpa only [kernel, mul_div_assoc] using witness_generating_square_limit h
  have hh := (push_series_limit m h z).div hden hc
  have he : (c / (m : ℝ)) / c = 1 / m := by field_simp
  rw [he] at hh
  apply hh.congr'
  filter_upwards [unit_interval_eventually] with r hr
  have hk := ne_of_gt (kernel_pos hr.1 hr.2)
  have hrabs : |r| < 1 := by simpa only [abs_of_pos hr.1] using hr.2
  change push m (fun n ↦ (sumRep A n : ℝ) * r ^ n) z * kernel r /
      (series (indicator A) r ^ 2 * kernel r) =
    conv (fun x ↦ residueMass m A r x / series (indicator A) r)
      (fun x ↦ residueMass m A r x / series (indicator A) r) z
  rw [conv_div, residueMass_conv m A hrabs]
  exact mul_div_mul_right _ _ hk

/-- Every residue class receives asymptotically the same fraction of the
geometrically weighted mass of a hypothetical witness. -/
theorem witness_residue_equidistribution {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) (z : ZMod m) :
    Tendsto (fun r : ℝ ↦ normalizedMass m A r z) (𝓝[<] 1) (𝓝 (1 / m)) := by
  have hsum : ∀ᶠ r : ℝ in 𝓝[<] 1, ∑ z : ZMod m, normalizedMass m A r z = 1 := by
    filter_upwards [witness_series_eventually_ne_zero hc h, unit_interval_eventually] with r hF hr
    have hrabs : |r| < 1 := by simpa only [abs_of_pos hr.1] using hr.2
    simp only [normalizedMass, ← Finset.sum_div, sum_residueMass m A hrabs, div_self hF]
  have hh := tendsto_probability_of_convolution (normalizedMass m A) hsum
    (fun z ↦ by simpa only [ZMod.card] using normalizedMass_conv_limit m hc h z) z
  simpa only [ZMod.card] using hh

lemma kernel_tendsto_zero : Tendsto kernel (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hn : Tendsto (fun r : ℝ ↦ 1 - r) (𝓝[<] 1) (𝓝 0) := by
    simpa only [sub_self] using ((continuous_const.sub continuous_id : Continuous (fun r : ℝ ↦ 1 - r)).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  exact hn.div_atTop negative_log_one_sub

lemma witness_series_tendsto_atTop {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (series (indicator A)) (𝓝[<] 1) atTop := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hlim : Tendsto (fun r : ℝ ↦ series (indicator A) r ^ 2 * kernel r)
      (𝓝[<] 1) (𝓝 c) := by
    simpa only [kernel, mul_div_assoc] using witness_generating_square_limit h
  rw [tendsto_atTop]
  intro B
  let D := (|B| + 1) ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hδ : 0 < c / (2 * D) := by positivity
  filter_upwards [unit_interval_eventually,
    hlim.eventually (eventually_gt_nhds (show c / 2 < c by linarith)),
    kernel_tendsto_zero.eventually_lt_const hδ] with r hr hlarge hsmall
  by_contra hB
  have hF0 := series_indicator_nonneg A hr.1.le
  have hk := kernel_pos hr.1 hr.2
  have hF : series (indicator A) r ≤ |B| + 1 := by linarith [le_abs_self B]
  have hFsq : series (indicator A) r ^ 2 ≤ D := pow_le_pow_left₀ hF0 hF 2
  have hm := mul_le_mul_of_nonneg_right hFsq hk.le
  have hh := (lt_div_iff₀ (show 0 < 2 * D by positivity)).mp hsmall
  nlinarith

lemma residueMass_finite (A : Set ℕ) (z : ZMod m)
    (hfin : {n : ℕ | n ∈ A ∧ (n : ZMod m) = z}.Finite) (r : ℝ) :
    residueMass m A r z = ∑ n ∈ hfin.toFinset, r ^ n := by
  unfold residueMass push
  rw [tsum_eq_sum (s := hfin.toFinset) (fun n hn ↦ ?_)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hh := hfin.mem_toFinset.mp hn
    simp only [Set.mem_setOf_eq] at hh
    simp [residueTerm, weightedIndicator, indicator, hh.1, hh.2]
  · have hh : ¬(n ∈ A ∧ (n : ZMod m) = z) := by simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hn
    by_cases hA : n ∈ A <;> by_cases hz : (n : ZMod m) = z <;>
      simp_all [residueTerm, weightedIndicator, indicator]

/-- No fixed residue class can contain only finitely many elements of a witness. -/
theorem witness_infinite_each_residue {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) (z : ZMod m) :
    {n : ℕ | n ∈ A ∧ (n : ZMod m) = z}.Infinite := by
  by_contra hnot
  have hfin := Set.not_infinite.mp hnot
  have hmass : Tendsto (fun r : ℝ ↦ residueMass m A r z) (𝓝[<] 1) (𝓝 (hfin.toFinset.card : ℝ)) := by
    simp_rw [residueMass_finite m A z hfin]
    have hh := tendsto_finset_sum hfin.toFinset (fun n _ ↦
      ((continuous_pow n).tendsto (1 : ℝ)).mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds))
    simpa only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using hh
  have hzero : Tendsto (fun r : ℝ ↦ normalizedMass m A r z) (𝓝[<] 1) (𝓝 0) :=
    hmass.div_atTop (witness_series_tendsto_atTop hc h)
  have he := tendsto_nhds_unique (witness_residue_equidistribution m hc h z) hzero
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  exact (one_div_ne_zero hm) he

/-- In particular, a permanent omitted residue class rules out the limit. -/
theorem no_log_limit_of_missing_tail_residue (A : Set ℕ) (z : ZMod m) (N : ℕ)
    (hA : ∀ n ≥ N, n ∈ A → (n : ZMod m) ≠ z) (c : ℝ) (hc : c ≠ 0) :
    ¬Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  intro h
  have hfin : {n : ℕ | n ∈ A ∧ (n : ZMod m) = z}.Finite := by
    apply (Set.finite_Iio N).subset
    intro n hn
    change n < N
    by_contra hnN
    exact hA n (by omega) hn.1 hn.2
  exact (witness_infinite_each_residue m hc h z).not_finite hfin

end Erdos66ResidueEquidistribution
