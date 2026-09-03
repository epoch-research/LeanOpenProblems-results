import Submission.Hypergraph

/-! A finite weighted Bernoulli lower-tail bound. Its variance scale is
maximum weight times mean, rather than ambient cardinality times squared
maximum weight. All expectations are the explicit finite product law. -/
namespace Erdos773.WeightedBernoulliLowerTail
open Finset
set_option maxHeartbeats 2500000
noncomputable section

lemma exp_neg_quadratic {x : ℝ} (hx : 0≤x) : Real.exp (-x)≤1-x+x^2/2 := by
  have hd (z : ℝ) : HasDerivAt (fun y : ℝ => 1-y+y^2/2-Real.exp (-y))
      (-1+z+Real.exp (-z)) z := by
    convert (((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).add
      (((hasDerivAt_id z).pow 2).div_const 2)).sub ((hasDerivAt_id z).neg.exp) using 1 <;> simp only [id_eq,Pi.neg_apply] <;> ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun z => by
    change (0:ℝ)≤-1+z+Real.exp (-z)
    have hh := Real.add_one_le_exp (-z)
    linarith only [hh])
  have hh := hm hx
  norm_num at hh
  linarith only [hh]

variable {α : Type*} [Fintype α] [DecidableEq α]

def value (w : α → ℝ) (f : α → Bool) : ℝ := ∑ a : α, if f a then w a else 0

def mean (w : α → ℝ) (p : ℝ) : ℝ := p*∑ a : α, w a

lemma laplace_identity (w : α → ℝ) (p t : ℝ) :
    (∑ f : α → Bool, trialWeight p f*Real.exp (-t*value w f)) =
      ∏ a : α, (1-p+p*Real.exp (-t*w a)) := by
  have hterm (f : α → Bool) : trialWeight p f*Real.exp (-t*value w f)=
      ∏ a : α, if f a then p*Real.exp (-t*w a) else 1-p := by
    have he : -t*value w f=∑ a : α, if f a then -t*w a else 0 := by
      unfold value
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      split_ifs <;> ring
    rw [he,Real.exp_sum,trialWeight,← prod_mul_distrib]
    apply prod_congr rfl
    intro a ha
    split_ifs <;> simp
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (a : α) (b : Bool) => if b then p*Real.exp (-t*w a) else 1-p)]
  simp [add_comm]

lemma laplace_bound (w : α → ℝ) (W p t : ℝ)
    (hw : ∀ a, 0≤w a) (hW : ∀ a, w a≤W)
    (hp : 0≤p) (hp1 : p≤1) (ht : 0≤t) :
    (∑ f : α → Bool, trialWeight p f*Real.exp (-t*value w f)) ≤
      Real.exp (-t*mean w p+t^2*W*mean w p/2) := by
  rw [laplace_identity]
  have hfac (a : α) : 1-p+p*Real.exp (-t*w a) ≤
      Real.exp (-p*t*w a+p*t^2*(w a)^2/2) := by
    have hh := mul_le_mul_of_nonneg_left (exp_neg_quadratic (mul_nonneg ht (hw a))) hp
    have he := Real.add_one_le_exp (-p*t*w a+p*t^2*(w a)^2/2)
    simp only [← neg_mul] at hh
    nlinarith only [hh,he]
  have hb : (∏ a : α, (1-p+p*Real.exp (-t*w a))) ≤
      ∏ a : α, Real.exp (-p*t*w a+p*t^2*(w a)^2/2) := by
    apply prod_le_prod
    · intro a ha
      exact add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp (Real.exp_pos _).le)
    · intro a ha
      exact hfac a
  apply hb.trans
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hs : (∑ a : α, (w a)^2)≤W*∑ a : α, w a := by
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    nlinarith only [mul_le_mul_of_nonneg_right (hW a) (hw a)]
  have hh := mul_le_mul_of_nonneg_left hs (show 0≤p*t^2/2 by positivity)
  simp only [sum_add_distrib,← sum_div,← mul_sum]
  unfold mean
  nlinarith only [hh]

/-- Unoptimized exponential Markov bound for the lower deviation event. -/
theorem lower_tail_parameter (w : α → ℝ) (W p t a : ℝ)
    (hw : ∀ i, 0≤w i) (hW : ∀ i, w i≤W)
    (hp : 0≤p) (hp1 : p≤1) (ht : 0≤t) :
    (∑ f : α → Bool, if value w f≤ mean w p-a then trialWeight p f else 0) ≤
      Real.exp (-t*a+t^2*W*mean w p/2) := by
  have hpoint (f : α → Bool) :
      (if value w f≤ mean w p-a then trialWeight p f else 0)*Real.exp (-t*(mean w p-a)) ≤
      trialWeight p f*Real.exp (-t*value w f) := by
    split_ifs with h
    · apply mul_le_mul_of_nonneg_left _ (trialWeight_nonneg hp hp1 f)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left h (by linarith)
    · simp only [zero_mul]
      exact mul_nonneg (trialWeight_nonneg hp hp1 f) (Real.exp_pos _).le
  have hh := sum_le_sum (s := (univ : Finset (α → Bool))) (fun f _ => hpoint f)
  rw [← sum_mul] at hh
  calc
    _ ≤ (∑ f : α → Bool, trialWeight p f*Real.exp (-t*value w f))/Real.exp (-t*(mean w p-a)) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr hh
    _ ≤ Real.exp (-t*mean w p+t^2*W*mean w p/2)/Real.exp (-t*(mean w p-a)) :=
      div_le_div_of_nonneg_right (laplace_bound w W p t hw hW hp hp1 ht) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

/-- Multiplicative lower tail with the correct maximum-weight/mean scale.
No independence of hypergraph edge indicators is assumed: only the original
vertex marks are independent. -/
theorem relative_lower_tail (w : α → ℝ) (W p η : ℝ)
    (hw : ∀ i, 0≤w i) (hW : ∀ i, w i≤W) (hWpos : 0<W)
    (hp : 0≤p) (hp1 : p≤1) (hη : 0≤η) :
    (∑ f : α → Bool, if value w f≤(1-η)*mean w p then trialWeight p f else 0) ≤
      Real.exp (-η^2*mean w p/(2*W)) := by
  have hh := lower_tail_parameter w W p (η/W) (η*mean w p) hw hW hp hp1 (div_nonneg hη hWpos.le)
  have ht : -(η/W)*(η*mean w p)+(η/W)^2*W*mean w p/2=-η^2*mean w p/(2*W) := by
    field_simp
    ring
  rw [ht] at hh
  have hm : mean w p-η*mean w p=(1-η)*mean w p := by ring
  rwa [hm] at hh

#print axioms exp_neg_quadratic
#print axioms laplace_identity
#print axioms laplace_bound
#print axioms lower_tail_parameter
#print axioms relative_lower_tail
end
end Erdos773.WeightedBernoulliLowerTail
