import Submission.PopulationGibbsEntropy

/-! Signed finite Gibbs entropy production and a sharper resampling constant.
All costs use the actual conditional population. No uniform arithmetic
estimate for these costs, or quadratic Jacobsthal bound, is asserted. -/
namespace Erdos970.FiniteGibbs
open Finset Real GapAverages Resampling
set_option maxHeartbeats 2000000

lemma exp_secant_aux (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ (u-2)*exp u+u+2 := by
  let F : ℝ → ℝ := fun x => (x-2)*exp x+x+2
  have hd (x : ℝ) : HasDerivAt F ((x-1)*exp x+1) x := by
    have hh := ((((hasDerivAt_id x).sub_const 2).mul (hasDerivAt_exp x)).add
      (hasDerivAt_id x)).add_const 2
    convert hh using 1
    dsimp [F]
    ring
  have hm : Monotone F := by
    apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    have hh := mul_le_mul_of_nonneg_right (add_one_le_exp (-x)) (exp_pos x).le
    have he : exp (-x)*exp x = 1 := by rw [← exp_add]; simp
    rw [he] at hh
    nlinarith only [hh]
  have hh := hm hu
  simpa [F] using hh

/-- The arithmetic mean of the endpoint exponentials bounds their logarithmic
mean. This improves the previous factor-one secant estimate by a factor two. -/
lemma exp_pair_difference_half (x y : ℝ) :
    (exp x-exp y)*(x-y) ≤ (exp x+exp y)/2*(x-y)^2 := by
  have hord (x y : ℝ) (hxy : y ≤ x) :
      (exp x-exp y)*(x-y) ≤ (exp x+exp y)/2*(x-y)^2 := by
    have hh := mul_nonneg (exp_secant_aux (x-y) (sub_nonneg.mpr hxy)) (exp_pos y).le
    have he : exp (x-y)*exp y = exp x := by rw [← exp_add]; congr 1; ring
    have hid : ((x-y-2)*exp (x-y)+(x-y)+2)*exp y =
        (x-y-2)*exp x+(x-y+2)*exp y := by
      calc
        _ = (x-y-2)*(exp (x-y)*exp y)+(x-y+2)*exp y := by ring
        _ = _ := by rw [he]
    rw [hid] at hh
    have hs := hh
    have ht := mul_nonneg hs (sub_nonneg.mpr hxy)
    nlinarith only [ht]
  rcases le_total y x with hxy | hyx
  · exact hord x y hxy
  · have hh := hord y x hyx
    nlinarith only [hh]

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Signed entropy production before any square or uniform-cap bound. -/
theorem entropy_exp_le_signed (f : α → ℝ) (t : ℝ) :
    entropy (fun a => exp (-t*f a)) ≤
      t*mean (fun a => exp (-t*f a)*(mean f-f a)) := by
  have hh := entropy_le_log_covariance (fun a => exp (-t*f a)) (fun _ => exp_pos _)
  simp only [log_exp] at hh
  have hleft : mean (fun a => exp (-t*f a)*(-t*f a)) =
      -t*mean (fun a => exp (-t*f a)*f a) := by
    rw [← mean_mul]
    congr 1
    funext a
    ring
  rw [hleft,mean_mul] at hh
  have hright : mean (fun a => exp (-t*f a)*(mean f-f a)) =
      mean (fun a => exp (-t*f a))*mean f-mean (fun a => exp (-t*f a)*f a) := by
    simp only [mul_sub,mean_sub,mean_mul_right]
  rw [hright]
  nlinarith only [hh]

omit [Nonempty α] in
lemma exp_signed_cost_eq_covariance (f : α → ℝ) (t : ℝ) :
    t*mean (fun a => exp (-t*f a)*(mean f-f a)) =
      mean (fun a => exp (-t*f a)*log (exp (-t*f a))) -
        mean (fun a => exp (-t*f a))*mean (fun a => log (exp (-t*f a))) := by
  have he (a : α) : exp (-t*f a)*(-t*f a) = -t*(exp (-t*f a)*f a) := by ring
  simp only [log_exp,he,mul_sub,mean_sub,mean_mul,mean_mul_right]
  ring

/-- The signed covariance itself has the sharper half-resampling bound. -/
theorem exp_signed_cost_le_half_resampling (f : α → ℝ) (t : ℝ) :
    t*mean (fun a => exp (-t*f a)*(mean f-f a)) ≤ t^2/2*mean (fun a => exp (-t*f a)*
      mean (fun b => (f b-f a)^2)) := by
  let w := fun a => exp (-t*f a)
  have hcov := pair_log_covariance w
  have hpoint (a b : α) : (w a-w b)*(log (w a)-log (w b)) ≤
      t^2/2*(w a*(f b-f a)^2+w b*(f a-f b)^2) := by
    have hh := exp_pair_difference_half (-t*f a) (-t*f b)
    dsimp only [w]
    simp only [log_exp]
    convert hh using 1
    ring
  have hh := mean_mono (fun a => mean_mono (fun b => hpoint a b))
  have hswap : mean (fun a => mean (fun b => w b*(f a-f b)^2)) =
      mean (fun a => w a*mean (fun b => (f b-f a)^2)) := by
    rw [mean_comm]
    simp only [mean_mul]
  simp only [mean_mul,mean_add] at hh
  rw [hswap,hcov] at hh
  rw [exp_signed_cost_eq_covariance]
  dsimp only [w] at hh
  nlinarith only [hh]

/-- The full Gibbs-weighted resampling second moment admits coefficient 1/2.
The exponential cost of transporting Gibbs weights is not removed. -/
theorem entropy_exp_le_half_resampling (f : α → ℝ) (t : ℝ) :
    entropy (fun a => exp (-t*f a)) ≤ t^2/2*mean (fun a => exp (-t*f a)*
      mean (fun b => (f b-f a)^2)) :=
  (entropy_exp_le_signed f t).trans (exp_signed_cost_le_half_resampling f t)

#print axioms entropy_exp_le_signed
#print axioms entropy_exp_le_half_resampling
end Erdos970.FiniteGibbs
