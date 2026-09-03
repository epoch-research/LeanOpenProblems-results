import Submission.ResiduePairIdentityExplore
import Submission.DensityDiagonalExplore

/-! Joint density-one limits for all residue-pair contributions of a
hypothetical witness. The exceptional set is not eliminated. -/
namespace Erdos66ResidueProjectionDensity
open Erdos66NaturalResidueProjection Erdos66WitnessResidueProjection
  Erdos66ResiduePairIdentity Erdos66AbelSquarePrefix Erdos66SquarePrefixDensity
  Erdos66DensityDiagonal Erdos66WitnessAutocorrelation Erdos66Generating
  Erdos66ResidueSeries
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2800000
variable (m : ℕ) [NeZero m]

noncomputable def totalError (A : Set ℕ) (n : ℕ) : ℝ :=
  Real.sqrt (∑ i : ZMod m, projectionError m (indicator A) i n^2)

lemma totalError_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ totalError m A n := Real.sqrt_nonneg _

lemma totalError_square (A : Set ℕ) (n : ℕ) :
    totalError m A n^2=∑ i : ZMod m, projectionError m (indicator A) i n^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

lemma projectionError_le_totalError (A : Set ℕ) (i : ZMod m) (n : ℕ) :
    |projectionError m (indicator A) i n| ≤ totalError m A n := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact Finset.single_le_sum (f := fun i ↦ projectionError m (indicator A) i n^2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)

lemma summable_projection_square (A : Set ℕ) {r : ℝ} (hr0 : 0<r) (hr1 : r<1) (i : ZMod m) :
    Summable (fun n ↦ projectionError m (indicator A) i n^2*r^n) := by
  have hq0 : 0<Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hq1 : Real.sqrt r<1 := (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr (by simpa using hr1)
  have hf := summable_indicator A (r := Real.sqrt r) (by simpa only [abs_of_pos hq0] using hq1)
  have hh := summable_square (summable_projectionError m hf i)
  simpa only [projectionError_weighted,square_weight,Real.sq_sqrt hr0.le] using hh

lemma summable_totalError_square (A : Set ℕ) {r : ℝ} (hr0 : 0<r) (hr1 : r<1) :
    Summable (fun n ↦ totalError m A n^2*r^n) := by
  simp only [totalError_square,Finset.sum_mul]
  exact summable_sum (fun i _ ↦ summable_projection_square m A hr0 hr1 i)

lemma totalError_series_eq (A : Set ℕ) {r : ℝ} (hr0 : 0<r) (hr1 : r<1) :
    series (fun n ↦ totalError m A n^2) r=residueEnergy m (indicator A) r := by
  simp only [series,totalError_square,Finset.sum_mul,residueEnergy]
  exact Summable.tsum_finsetSum (fun i _ ↦ summable_projection_square m A hr0 hr1 i)

/-- The ordinary cumulative joint residue error is o(N log² N). -/
theorem witness_totalError_prefix_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ ↦ (∑ n∈Finset.range N, totalError m A n^2)/
      ((N : ℝ)*(Real.log N)^2)) atTop (𝓝 0) := by
  apply prefix_zero_of_weighted_zero (fun n ↦ totalError m A n^2) (fun _ ↦ sq_nonneg _) 1
  · intro r hr0 hr1
    simpa only [one_mul,pow_succ,mul_assoc] using (summable_totalError_square m A hr0 hr1).mul_right r
  · have hi : Tendsto (fun r : ℝ ↦ r) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_right nhdsWithin_le_nhds
    have hh := (witness_residueEnergy_zero m h).mul hi
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [unit_interval_eventually] with r hr
    rw [← totalError_series_eq m A hr.1 hr.2]
    simp only [one_mul,pow_succ,series,← mul_assoc,tsum_mul_right]
    ring

lemma log_shift_limit {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ f n/Real.log ((n : ℝ)+2)) atTop (𝓝 c) := by
  have hh := h.div (log_affine_ratio 1 2) (by norm_num : (1:ℝ)≠0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : Real.log (n : ℝ)≠0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  simp only [Pi.div_apply,Nat.mul_one,Nat.cast_add,Nat.cast_ofNat]
  field_simp

lemma witness_totalError_exception {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ E : Set ℕ, Tendsto (fun N : ℕ ↦ (Erdos66Counting.count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then 0 else totalError m A n/Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
  apply exists_density_zero_exception _ 0
  intro ε hε
  have he : {n | ε ≤ dist (totalError m A n/Real.log ((n : ℝ)+2)) 0}=logBad (totalError m A) ε := by
    ext n
    have hL : 0<Real.log ((n : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    simp only [Set.mem_setOf_eq,logBad,Real.dist_eq,sub_zero,
      abs_of_nonneg (div_nonneg (totalError_nonneg m A n) hL.le),
      abs_of_nonneg (totalError_nonneg m A n),le_div_iff₀ hL]
  rw [he]
  exact logBad_density_zero _ (witness_totalError_prefix_zero m h) hε

/-- A single density-zero set works for every endpoint residue. At each
nonexceptional target these are the m compatible ordered residue pairs. -/
theorem witness_projection_limits_off_density_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ E : Set ℕ, Tendsto (fun N : ℕ ↦ (Erdos66Counting.count E N : ℝ)/N) atTop (𝓝 0) ∧
      ∀ i : ZMod m, Tendsto (fun n ↦ if n∈E then c/m else
        sumConv (indicator A) (residueTerm m (indicator A) i) n/Real.log ((n : ℝ)+2))
        atTop (𝓝 (c/m)) := by
  obtain ⟨E,hE,hD⟩ := witness_totalError_exception m h
  have hmean : Tendsto (fun n ↦ ((sumRep A n : ℝ)/m)/Real.log ((n : ℝ)+2)) atTop (𝓝 (c/m)) := by
    convert (log_shift_limit h).div_const (m : ℝ) using 1
    funext n
    ring
  refine ⟨E,hE,fun i ↦ Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hD) (ε/2) (half_pos hε),
    (Metric.tendsto_nhds.mp hmean) (ε/2) (half_pos hε)] with n hnD hnM
  by_cases hn : n∈E
  · simpa only [if_pos hn,dist_self] using hε
  · rw [if_neg hn]
    have hL : 0<Real.log ((n : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hDsmall : totalError m A n/Real.log ((n : ℝ)+2)<ε/2 := by
      simpa only [if_neg hn,Real.dist_eq,sub_zero,
        abs_of_nonneg (div_nonneg (totalError_nonneg m A n) hL.le)] using hnD
    have hMsmall : |((sumRep A n : ℝ)/m)/Real.log ((n : ℝ)+2)-c/m|<ε/2 := by
      simpa only [Real.dist_eq] using hnM
    have he : sumConv (indicator A) (residueTerm m (indicator A) i) n/Real.log ((n : ℝ)+2)-c/m=
        projectionError m (indicator A) i n/Real.log ((n : ℝ)+2)+
          (((sumRep A n : ℝ)/m)/Real.log ((n : ℝ)+2)-c/m) := by
      rw [projectionError,show sumConv (indicator A) (indicator A) n=(sumRep A n : ℝ) from sum_indicator_antidiagonal A n]
      ring
    rw [Real.dist_eq,he]
    have hh := abs_add_le (projectionError m (indicator A) i n/Real.log ((n : ℝ)+2))
      (((sumRep A n : ℝ)/m)/Real.log ((n : ℝ)+2)-c/m)
    have hproj : |projectionError m (indicator A) i n/Real.log ((n : ℝ)+2)| ≤
        totalError m A n/Real.log ((n : ℝ)+2) := by
      rw [abs_div,abs_of_pos hL]
      exact div_le_div_of_nonneg_right (projectionError_le_totalError m A i n) hL.le
    linarith

/-- All ordered residue-pair contributions have their expected leading
share on one common density-one set of natural targets. -/
theorem witness_pair_limits_off_density_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ E : Set ℕ, Tendsto (fun N : ℕ ↦ (Erdos66Counting.count E N : ℝ)/N) atTop (𝓝 0) ∧
      ∀ i j : ZMod m, Tendsto (fun n ↦ if n∈E then 0 else
        sumConv (residueTerm m (indicator A) i) (residueTerm m (indicator A) j) n/Real.log ((n : ℝ)+2)-
          if i+j=(n : ZMod m) then c/m else 0) atTop (𝓝 0) := by
  obtain ⟨E,hE,hP⟩ := witness_projection_limits_off_density_zero m h
  refine ⟨E,hE,fun i j ↦ Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp (hP j)) ε hε] with n hn
  by_cases he : n∈E
  · simp only [if_pos he,dist_self]
    exact hε
  · rw [if_neg he,residue_pair_eq]
    by_cases hij : i+j=(n : ZMod m)
    · simpa only [if_neg he,if_pos hij,Real.dist_eq,sub_zero] using hn
    · simpa only [if_neg hij,zero_div,sub_self,dist_self] using hε

end Erdos66ResidueProjectionDensity
