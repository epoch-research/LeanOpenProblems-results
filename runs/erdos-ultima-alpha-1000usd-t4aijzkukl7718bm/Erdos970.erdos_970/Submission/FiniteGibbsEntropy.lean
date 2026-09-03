import Submission.GibbsResamplingTransport

/-! Finite positive-function entropy, with its normalization and product
averaging explicit. These lemmas do not assume a critical sieve estimate. -/
namespace Erdos970.FiniteGibbs
open Finset Real
set_option maxHeartbeats 1800000

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def mean (f : α → ℝ) : ℝ := (∑ a, f a)/Fintype.card α

lemma mean_add (f g : α → ℝ) : mean (fun a => f a+g a) = mean f+mean g := by
  simp only [mean,sum_add_distrib,add_div]

lemma mean_sub (f g : α → ℝ) : mean (fun a => f a-g a) = mean f-mean g := by
  simp only [mean,sum_sub_distrib,sub_div]

lemma mean_mul (c : ℝ) (f : α → ℝ) : mean (fun a => c*f a) = c*mean f := by
  simp only [mean,← mul_sum]
  ring

lemma mean_mul_right (c : ℝ) (f : α → ℝ) : mean (fun a => f a*c) = mean f*c := by
  simp only [mean,← sum_mul]
  ring

lemma mean_const [Nonempty α] (c : ℝ) : mean (fun _ : α => c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean,hc]

lemma mean_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_nonneg {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ mean f :=
  div_nonneg (sum_nonneg (fun a _ => h a)) (by positivity)

lemma mean_pos [Nonempty α] {f : α → ℝ} (h : ∀ a, 0 < f a) : 0 < mean f := by
  apply div_pos _ (by exact_mod_cast Fintype.card_pos)
  exact sum_pos (fun a _ => h a) univ_nonempty

lemma mean_comm (f : α → β → ℝ) : mean (fun a => mean (f a)) =
    mean (fun b => mean (fun a => f a b)) := by
  simp only [mean,← sum_div]
  rw [sum_comm]
  ring

noncomputable def entropy (f : α → ℝ) : ℝ :=
  mean (fun a => f a*log (f a))-mean f*log (mean f)

/-- A finite Gibbs variational inequality. Positivity is explicit, so no
zero-log convention is used in expanding the ratios. -/
lemma entropy_variational [Nonempty α] (f g : α → ℝ)
    (hf : ∀ a, 0 < f a) (hg : ∀ a, 0 < g a) :
    mean (fun a => f a*log (g a))-mean f*log (mean g) ≤ entropy f := by
  have hF := mean_pos hf
  have hG := mean_pos hg
  have hpoint (a : α) :
      f a*log (g a*mean f/(f a*mean g)) ≤ (mean f/mean g)*g a-f a := by
    have hfa := hf a
    have hga := hg a
    have hr : 0 < g a*mean f/(f a*mean g) := by positivity
    have hh := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hr) (hf a).le
    convert hh using 1
    field_simp [(hf a).ne',hG.ne']
  have hh := mean_mono hpoint
  rw [mean_sub,mean_mul,div_mul_cancel₀ _ hG.ne',sub_self] at hh
  have he (a : α) : f a*log (g a*mean f/(f a*mean g)) =
      f a*log (g a)+f a*log (mean f)-f a*log (f a)-f a*log (mean g) := by
    rw [log_div (mul_ne_zero (hg a).ne' hF.ne') (mul_ne_zero (hf a).ne' hG.ne'),log_mul (hg a).ne' hF.ne',
      log_mul (hf a).ne' hG.ne']
    ring
  simp_rw [he] at hh
  rw [mean_sub,mean_sub,mean_add,mean_mul_right,mean_mul_right] at hh
  unfold entropy
  linarith only [hh]

lemma entropy_nonneg [Nonempty α] (f : α → ℝ) (hf : ∀ a, 0 < f a) :
    0 ≤ entropy f := by
  have hh := entropy_variational f (fun _ => 1) hf (fun _ => by norm_num)
  simpa only [log_one,mul_zero,mean_const,sub_zero] using hh

/-- Entropy is convex under averaging another finite coordinate. -/
theorem entropy_mean_le_mean_entropy [Nonempty α] [Nonempty β]
    (f : α → β → ℝ) (hf : ∀ a b, 0 < f a b) :
    entropy (fun a => mean (f a)) ≤ mean (fun b => entropy (fun a => f a b)) := by
  let g := fun a => mean (f a)
  have hg : ∀ a, 0 < g a := fun a => mean_pos (hf a)
  have hh := mean_mono (fun b => entropy_variational (fun a => f a b) g
    (fun a => hf a b) hg)
  rw [mean_sub,mean_mul_right] at hh
  have hleft : mean (fun b => mean (fun a => f a b*log (g a))) =
      mean (fun a => g a*log (g a)) := by
    rw [mean_comm]
    simp_rw [mean_mul_right]
    rfl
  rw [hleft,← mean_comm f] at hh
  exact hh

noncomputable def jointEntropy (f : α → β → ℝ) : ℝ :=
  mean (fun a => mean (fun b => f a b*log (f a b)))-
    mean (fun a => mean (f a))*log (mean (fun a => mean (f a)))

lemma entropy_chain (f : α → β → ℝ) : jointEntropy f =
    mean (fun a => entropy (f a))+entropy (fun a => mean (f a)) := by
  simp only [jointEntropy,entropy,mean_sub]
  ring

/-- Two-coordinate tensorization, proved from the exact chain rule and the
variational inequality rather than assumed independence of function values. -/
theorem entropy_two_coordinate [Nonempty α] [Nonempty β]
    (f : α → β → ℝ) (hf : ∀ a b, 0 < f a b) :
    jointEntropy f ≤ mean (fun a => entropy (f a))+
      mean (fun b => entropy (fun a => f a b)) := by
  rw [entropy_chain]
  exact add_le_add le_rfl (entropy_mean_le_mean_entropy f hf)

lemma mean_log_le_log_mean [Nonempty α] (f : α → ℝ) (hf : ∀ a, 0 < f a) :
    mean (fun a => log (f a)) ≤ log (mean f) := by
  have hh := entropy_variational (fun _ => 1) f (fun _ => by norm_num) hf
  simp only [one_mul,mean_const,entropy,log_one,mul_zero,sub_self] at hh
  linarith only [hh]

lemma entropy_le_log_covariance [Nonempty α] (f : α → ℝ) (hf : ∀ a, 0 < f a) :
    entropy f ≤ mean (fun a => f a*log (f a))-mean f*mean (fun a => log (f a)) := by
  have hh := mul_le_mul_of_nonneg_left (mean_log_le_log_mean f hf) (mean_pos hf).le
  unfold entropy
  linarith only [hh]

lemma pair_log_covariance [Nonempty α] (f : α → ℝ) :
    mean (fun a => mean (fun b => (f a-f b)*(log (f a)-log (f b)))) =
      2*(mean (fun a => f a*log (f a))-mean f*mean (fun a => log (f a))) := by
  have he (a b : α) : (f a-f b)*(log (f a)-log (f b)) =
      f a*log (f a)-f a*log (f b)-f b*log (f a)+f b*log (f b) := by ring
  simp_rw [he]
  simp only [mean_add,mean_sub,mean_const,mean_mul,mean_mul_right]
  ring

lemma exp_pair_difference_bound (x y : ℝ) :
    (exp x-exp y)*(x-y) ≤ (exp x+exp y)*(x-y)^2 := by
  have hord (x y : ℝ) (hxy : y ≤ x) :
      (exp x-exp y)*(x-y) ≤ (exp x+exp y)*(x-y)^2 := by
    have hh := mul_le_mul_of_nonneg_left (add_one_le_exp (y-x)) (exp_pos x).le
    have he : exp x*exp (y-x) = exp y := by rw [← exp_add]; congr 1; ring
    rw [he] at hh
    have hsec : exp x-exp y ≤ exp x*(x-y) := by nlinarith only [hh]
    have hprod := mul_le_mul_of_nonneg_right hsec (sub_nonneg.mpr hxy)
    nlinarith only [hprod,mul_nonneg (exp_pos y).le (sq_nonneg (x-y))]
  rcases le_total y x with hxy | hyx
  · exact hord x y hxy
  · have hh := hord y x hyx
    nlinarith only [hh]

/-- A one-coordinate entropy estimate by the full, Gibbs-weighted
resampling second moment. The stated constant is one, not one half. -/
theorem entropy_exp_le_resampling [Nonempty α] (f : α → ℝ) (t : ℝ) :
    entropy (fun a => exp (-t*f a)) ≤ t^2*mean (fun a => exp (-t*f a)*
      mean (fun b => (f b-f a)^2)) := by
  let w := fun a => exp (-t*f a)
  have he := entropy_le_log_covariance w (fun a => exp_pos _)
  have hcov := pair_log_covariance w
  have hpoint (a b : α) : (w a-w b)*(log (w a)-log (w b)) ≤
      t^2*(w a*(f b-f a)^2+w b*(f a-f b)^2) := by
    have hh := exp_pair_difference_bound (-t*f a) (-t*f b)
    dsimp only [w]
    simp only [log_exp]
    convert hh using 1 <;> ring
  have hh := mean_mono (fun a => mean_mono (fun b => hpoint a b))
  have hswap : mean (fun a => mean (fun b => w b*(f a-f b)^2)) =
      mean (fun a => w a*mean (fun b => (f b-f a)^2)) := by
    rw [mean_comm]
    simp only [mean_mul]
  simp only [mean_mul,mean_add] at hh
  rw [hswap,hcov] at hh
  change entropy w ≤ _
  dsimp only [w] at he hh ⊢
  nlinarith only [he,hh]

#print axioms entropy_variational
#print axioms entropy_mean_le_mean_entropy
#print axioms entropy_two_coordinate
#print axioms entropy_exp_le_resampling
end Erdos970.FiniteGibbs
