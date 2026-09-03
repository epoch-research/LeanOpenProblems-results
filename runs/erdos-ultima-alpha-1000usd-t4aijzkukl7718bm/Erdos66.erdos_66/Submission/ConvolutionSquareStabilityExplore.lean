import Submission.DifferenceSignEnergyExplore

/-! An elementary reverse estimate for convolution squares. It uses
reflection and the correlation-energy identity, not Fourier transforms. -/
namespace Erdos66ConvolutionSquareStability
open Erdos66MixedEnergy Erdos66DifferenceSignEnergy
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma inner_sq_le_energy (f g : G → ℝ) :
    (∑ x : G, f x*g x)^2 ≤ energy f g := by
  classical
  have hh : (conv f (reflect g) 0)^2 ≤ energy f (reflect g) :=
    Finset.single_le_sum (fun t _ ↦ sq_nonneg (conv f (reflect g) t)) (Finset.mem_univ 0)
  rw [energy_reflect_right] at hh
  simpa only [conv,reflect,zero_sub,neg_neg] using hh

lemma conv_comm (f g : G → ℝ) (z : G) : conv f g z=conv g f z := by
  unfold conv
  rw [← Equiv.sum_comp (Equiv.subLeft z)]
  simp only [Equiv.subLeft_apply,sub_sub_cancel]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma conv_sum_diff (f g : G → ℝ) (z : G) :
    conv (fun x ↦ f x+g x) (fun x ↦ f x-g x) z = conv f f z-conv g g z := by
  have he (x : G) : (f x+g x)*(f (z-x)-g (z-x)) =
      f x*f (z-x)-f x*g (z-x)+g x*f (z-x)-g x*g (z-x) := by ring
  unfold conv
  simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]
  have hh := conv_comm f g z
  unfold conv at hh
  rw [hh]
  ring

/-- The difference of the squared masses is bounded by the L2 norm of the
difference of the convolution squares. -/
theorem square_mass_difference_le (f g : G → ℝ) :
    ((∑ x : G, f x^2)-(∑ x : G, g x^2))^2 ≤
      ∑ z : G, (conv f f z-conv g g z)^2 := by
  have hh := inner_sq_le_energy (fun x ↦ f x+g x) (fun x ↦ f x-g x)
  have he : (∑ x : G, (f x+g x)*(f x-g x)) =
      (∑ x : G, f x^2)-(∑ x : G, g x^2) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he] at hh
  simpa only [energy,conv_sum_diff] using hh

end Erdos66ConvolutionSquareStability
