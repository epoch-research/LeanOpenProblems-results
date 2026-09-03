import Submission.WeightedPushEnergyExplore

/-! A weighted half-line version of convolution-square stability, obtained
by periodizing into any sufficiently large finite cyclic group. -/
namespace Erdos66WeightedSquareStability
open Filter AdditiveCombinatorics Erdos66Generating Erdos66ResidueSeries
  Erdos66WeightedPushEnergy Erdos66ConvolutionSquareStability Erdos66MixedEnergy
open scoped Classical Topology

lemma weighted_convolution (f g : ℕ → ℝ) (r : ℝ) (n : ℕ) :
    sumConv (fun k ↦ f k*r^k) (fun k ↦ g k*r^k) n = sumConv f g n*r^n := by
  unfold sumConv
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [← he,pow_add]
  ring

lemma summable_weighted_convolution {f g : ℕ → ℝ} {r : ℝ}
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n)) :
    Summable (fun n ↦ sumConv f g n*r^n) := by
  have hh := summable_sum_mul_antidiagonal_of_summable_mul
    (summable_mul_of_summable_norm hf.norm hg.norm)
  change Summable (sumConv (fun n ↦ f n*r^n) (fun n ↦ g n*r^n)) at hh
  convert hh using 1
  funext n
  exact (weighted_convolution f g r n).symm

variable (m : ℕ) [NeZero m]

lemma push_sub {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) (z : ZMod m) :
    push m (fun n ↦ f n-g n) z=push m f z-push m g z := by
  have he (n : ℕ) : residueTerm m (fun n ↦ f n-g n) z n =
      residueTerm m f z n-residueTerm m g z n := by unfold residueTerm; split_ifs <;> simp
  unfold push
  simp_rw [he]
  exact (summable_residueTerm m hf z).tsum_sub (summable_residueTerm m hg z)

/-- A positive squared-mass gap forces a weighted L2 error in the convolution
squares. The factor `(1-r^m)⁻¹` is a periodization overhead, not a hypothesis
about uniform distribution of the input sequences. -/
theorem weighted_square_stability {f g : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n))
    (hf2 : Summable (fun n ↦ (f n)^2*(r^2)^n))
    (hg2 : Summable (fun n ↦ (g n)^2*r^n))
    (hE2 : Summable (fun n ↦ (sumConv f f n-sumConv g g n)^2*r^n)) :
    (max 0 ((∑' n, (f n)^2*(r^2)^n)-
        (1-r^m)⁻¹*(∑' n, (g n)^2*r^n)))^2 ≤
      (1-r^m)⁻¹*(∑' n, (sumConv f f n-sumConv g g n)^2*r^n) := by
  let F := push m (fun n ↦ f n*r^n)
  let G := push m (fun n ↦ g n*r^n)
  let e := fun n ↦ sumConv f f n-sumConv g g n
  have he : Summable (fun n ↦ e n*r^n) := by
    simp only [e,sub_mul]
    exact (summable_weighted_convolution hf hf).sub (summable_weighted_convolution hg hg)
  have hconv (z : ZMod m) : conv F F z-conv G G z=push m (fun n ↦ e n*r^n) z := by
    dsimp only [F,G]
    rw [push_convolution m hf hf,push_convolution m hg hg]
    have hcf : sumConv (fun n ↦ f n*r^n) (fun n ↦ f n*r^n) =
        (fun n ↦ sumConv f f n*r^n) := funext (weighted_convolution f f r)
    have hcg : sumConv (fun n ↦ g n*r^n) (fun n ↦ g n*r^n) =
        (fun n ↦ sumConv g g n*r^n) := funext (weighted_convolution g g r)
    rw [hcf,hcg]
    rw [← push_sub m (summable_weighted_convolution hf hf) (summable_weighted_convolution hg hg)]
    simp only [e,sub_mul]
  have hstab := square_mass_difference_le F G
  simp_rw [hconv] at hstab
  have hnorm := sum_push_sq_le m hr0 hr1 he hE2
  have hlow := weighted_mass_le_sum_push_sq m hr0 hf0 hf hf2
  have hupp := sum_push_sq_le m hr0 hr1 hg hg2
  change _ ≤ ∑ z : ZMod m, F z^2 at hlow
  change (∑ z : ZMod m, G z^2) ≤ _ at hupp
  have hgap : (∑' n, (f n)^2*(r^2)^n)-(1-r^m)⁻¹*(∑' n, (g n)^2*r^n) ≤
      (∑ z : ZMod m, F z^2)-(∑ z : ZMod m, G z^2) := by linarith
  by_cases hh : 0 ≤ (∑' n, (f n)^2*(r^2)^n)-(1-r^m)⁻¹*(∑' n, (g n)^2*r^n)
  · rw [max_eq_right hh]
    have hs := (sq_le_sq₀ hh (hh.trans hgap)).mpr hgap
    exact hs.trans (hstab.trans hnorm)
  · rw [max_eq_left (le_of_not_ge hh),zero_pow (by decide)]
    have hp : 0 ≤ (1-r^m)⁻¹ := inv_nonneg.mpr
      (sub_nonneg.mpr (pow_le_one₀ hr0 hr1.le))
    exact mul_nonneg hp (tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr0 n)))

/-- Sending the auxiliary period to infinity removes its overhead. -/
theorem weighted_square_stability_limit {f g : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n))
    (hf2 : Summable (fun n ↦ (f n)^2*(r^2)^n))
    (hg2 : Summable (fun n ↦ (g n)^2*r^n))
    (hE2 : Summable (fun n ↦ (sumConv f f n-sumConv g g n)^2*r^n)) :
    (max 0 ((∑' n, (f n)^2*(r^2)^n)-(∑' n, (g n)^2*r^n)))^2 ≤
      ∑' n, (sumConv f f n-sumConv g g n)^2*r^n := by
  have hp : Tendsto (fun k : ℕ ↦ (1-r^(k+1))⁻¹) atTop (𝓝 (1 : ℝ)) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      (tendsto_add_atTop_nat 1)).const_sub 1
    simpa only [sub_zero,inv_one] using hh.inv₀ (by norm_num : (1-0 : ℝ) ≠ 0)
  have hleft := ((show Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) from tendsto_const_nhds).max
    ((hp.mul_const (∑' n, (g n)^2*r^n)).const_sub (∑' n, (f n)^2*(r^2)^n))).pow 2
  have hright := hp.mul_const (∑' n, (sumConv f f n-sumConv g g n)^2*r^n)
  simp only [one_mul] at hleft hright
  apply le_of_tendsto_of_tendsto hleft hright
  exact Eventually.of_forall (fun k ↦ weighted_square_stability (k+1)
    hr0 hr1 hf0 hf hg hf2 hg2 hE2)

end Erdos66WeightedSquareStability
