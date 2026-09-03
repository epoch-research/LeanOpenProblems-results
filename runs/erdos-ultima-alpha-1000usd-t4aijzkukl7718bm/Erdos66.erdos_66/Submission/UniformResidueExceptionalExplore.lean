import Submission.UniformResiduePrefixExplore

/-! A uniform exceptional-proportion bound for residue projection errors.
The normalization log N is common across each prefix. -/
namespace Erdos66UniformResidueExceptional
open Erdos66UniformResiduePrefix Erdos66ResidueProjectionDensity
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 1800000

noncomputable def badTargets (m : ℕ) [NeZero m] (A : Set ℕ) (ε : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n ↦ ε*Real.log N ≤ totalError m A n)

lemma badTargets_energy_bound (m : ℕ) [NeZero m] (A : Set ℕ) {ε : ℝ} (hε : 0<ε)
    {N : ℕ} (hN : 2≤N) :
    ((badTargets m A ε N).card : ℝ)/N ≤ prefixEnergy m A N/ε^2 := by
  have hNr : (1 : ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hN0 : (0 : ℝ)<N := by linarith
  have hL : 0<Real.log (N : ℝ) := Real.log_pos hNr
  have ht : 0≤ε*Real.log N := mul_nonneg hε.le hL.le
  have hb : ((badTargets m A ε N).card : ℝ)*(ε^2*(Real.log N)^2) ≤
      ∑ n∈Finset.range N, totalError m A n^2 := by
    calc
      _ = ∑ n∈badTargets m A ε N, (ε*Real.log N)^2 := by simp [mul_pow]
      _ ≤ ∑ n∈badTargets m A ε N, totalError m A n^2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact (sq_le_sq₀ ht (totalError_nonneg m A n)).mpr (Finset.mem_filter.mp hn).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ ↦ sq_nonneg _)
  calc
    _ ≤ ((∑ n∈Finset.range N, totalError m A n^2)/(ε^2*(Real.log N)^2))/N :=
      div_le_div_of_nonneg_right ((le_div_iff₀ (mul_pos (sq_pos_of_pos hε) (sq_pos_of_pos hL))).mpr hb) hN0.le
    _ = _ := by unfold prefixEnergy; field_simp

/-- Uniformly in every positive modulus, the proportion of targets below
N with joint residue error at least ε log N tends to zero. -/
theorem witness_uniform_bad_proportion {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    {ε : ℝ} (hε : 0<ε) :
    ∀ δ>0, ∀ᶠ N in atTop, ∀ (m : ℕ) [NeZero m],
      ((badTargets m A ε N).card : ℝ)/N<δ := by
  intro δ hδ
  filter_upwards [eventually_ge_atTop 2,
    witness_uniform_prefix_energy_zero h (δ*ε^2) (mul_pos hδ (sq_pos_of_pos hε))]
    with N hN he
  intro m hm
  exact (badTargets_energy_bound m A hε hN).trans_lt
    ((div_lt_iff₀ (sq_pos_of_pos hε)).mpr (he m))

/-- The modulus may be chosen after seeing the entire prefix. -/
theorem witness_variable_bad_proportion_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    {ε : ℝ} (hε : 0<ε) (μ : ℕ → ℕ) [∀ N, NeZero (μ N)] :
    Tendsto (fun N ↦ ((badTargets (μ N) A ε N).card : ℝ)/N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    _ (by simpa only [zero_div] using (witness_variable_prefix_energy_zero h μ).div_const (ε^2))
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact badTargets_energy_bound (μ N) A hε hN

end Erdos66UniformResidueExceptional
