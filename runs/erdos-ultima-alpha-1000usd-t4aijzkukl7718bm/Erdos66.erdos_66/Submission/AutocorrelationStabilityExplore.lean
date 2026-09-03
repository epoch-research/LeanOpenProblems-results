import Submission.WeightedSquareStabilityExplore

/-! Control of autocorrelation error by sum-convolution error. These estimates
are necessary-condition tools, not a resolution of Erdős 66. -/
namespace Erdos66AutocorrelationStability
open Erdos66MixedEnergy Erdos66ConvolutionSquareStability
  Erdos66DifferenceSignEnergy Erdos66WeightedSquareStability
  Erdos66WeightedPushEnergy Erdos66ResidueSeries Erdos66Generating
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 1800000

section Finite
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma corr_sum_diff (f g : G → ℝ) (z : G) :
    2*(corr f z-corr g z) =
      conv (fun x ↦ f x+g x) (reflect (fun x ↦ f x-g x)) z +
      conv (fun x ↦ f x+g x) (reflect (fun x ↦ f x-g x)) (-z) := by
  have ht : conv (fun x ↦ f x+g x) (reflect (fun x ↦ f x-g x)) z =
      ∑ x : G, (f (x+z)+g (x+z))*(f x-g x) := by
    unfold conv reflect
    rw [← Equiv.sum_comp (Equiv.addRight z)]
    simp only [Equiv.coe_addRight]
    apply Finset.sum_congr rfl
    intro x hx
    have he : -(z-(x+z))=x := by abel
    rw [he]
  rw [ht]
  simp only [conv,reflect,corr,neg_sub,sub_neg_eq_add]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [add_comm x z]
  ring

/-- Autocorrelation is the symmetric part of a reflected convolution.
Taking that symmetric part cannot increase the squared norm. -/
theorem corr_error_le_conv_error (f g : G → ℝ) :
    (∑ z : G, (corr f z-corr g z)^2) ≤
      ∑ z : G, (conv f f z-conv g g z)^2 := by
  let C := conv (fun x ↦ f x+g x) (reflect (fun x ↦ f x-g x))
  have hp (z : G) : (corr f z-corr g z)^2 ≤ (C z^2+C (-z)^2)/2 := by
    have hh := corr_sum_diff f g z
    change 2*(corr f z-corr g z)=C z+C (-z) at hh
    have hs := congrArg (fun x : ℝ ↦ x^2) hh
    nlinarith [sq_nonneg (C z-C (-z))]
  have hneg : (∑ z : G, C (-z)^2) = ∑ z : G, C z^2 := by
    simpa only [Equiv.neg_apply] using Equiv.sum_comp (Equiv.neg G) (fun z ↦ C z^2)
  calc
    _ ≤ ∑ z : G, (C z^2+C (-z)^2)/2 := Finset.sum_le_sum (fun z _ ↦ hp z)
    _ = ∑ z : G, C z^2 := by rw [← Finset.sum_div,Finset.sum_add_distrib,hneg]; ring
    _ = energy (fun x ↦ f x+g x) (fun x ↦ f x-g x) := energy_reflect_right _ _
    _ = _ := by simp only [energy,conv_sum_diff]

end Finite

lemma push_conv_error (m : ℕ) [NeZero m] {f g : ℕ → ℝ} {r : ℝ}
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n))
    (z : ZMod m) :
    conv (push m (fun n ↦ f n*r^n)) (push m (fun n ↦ f n*r^n)) z-
      conv (push m (fun n ↦ g n*r^n)) (push m (fun n ↦ g n*r^n)) z =
      push m (fun n ↦ (sumConv f f n-sumConv g g n)*r^n) z := by
  rw [push_convolution m hf hf,push_convolution m hg hg]
  have hcf : sumConv (fun n ↦ f n*r^n) (fun n ↦ f n*r^n) =
      (fun n ↦ sumConv f f n*r^n) := funext (weighted_convolution f f r)
  have hcg : sumConv (fun n ↦ g n*r^n) (fun n ↦ g n*r^n) =
      (fun n ↦ sumConv g g n*r^n) := funext (weighted_convolution g g r)
  rw [hcf,hcg,← push_sub m (summable_weighted_convolution hf hf)
    (summable_weighted_convolution hg hg)]
  simp only [sub_mul]

/-- One estimate for every cyclic period, with the periodization overhead
explicit. No equidistribution hypothesis is imposed on the sequences. -/
theorem cyclic_weighted_corr_error (m : ℕ) [NeZero m] {f g : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r<1)
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n))
    (hE : Summable (fun n ↦ (sumConv f f n-sumConv g g n)^2*r^n)) :
    (∑ z : ZMod m,
      (corr (push m (fun n ↦ f n*r^n)) z-corr (push m (fun n ↦ g n*r^n)) z)^2) ≤
      (1-r^m)⁻¹*(∑' n, (sumConv f f n-sumConv g g n)^2*r^n) := by
  have hh := corr_error_le_conv_error (push m (fun n ↦ f n*r^n))
    (push m (fun n ↦ g n*r^n))
  simp_rw [push_conv_error m hf hg] at hh
  apply hh.trans
  apply sum_push_sq_le m hr0 hr1 _ hE
  simp only [sub_mul]
  exact (summable_weighted_convolution hf hf).sub (summable_weighted_convolution hg hg)

end Erdos66AutocorrelationStability
