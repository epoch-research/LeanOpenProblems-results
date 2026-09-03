import Submission.FirstHitNormalizedCost

/-! A smooth-support saving in the exact canonical Selberg coefficient norm.
An exponentially tilted divisor-weight sum has an absolute mean-value bound. -/
namespace Erdos970.FiniteSelberg
open Finset Real
set_option maxHeartbeats 0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def primeCostWeight (p : ℕ) : ℝ := ((p : ℝ)+1)/(p-1)

lemma primeCostWeight_bounds (p : ℕ) (hp : p.Prime) : 1 ≤ primeCostWeight p ∧ primeCostWeight p ≤ 3 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hd : 0 < (p : ℝ)-1 := by linarith
  unfold primeCostWeight
  constructor
  · apply (le_div_iff₀ hd).mpr; linarith
  · apply (div_le_iff₀ hd).mpr; linarith

lemma exp_le_one_add_two (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : exp t ≤ 1+2*t := by
  have hh := (abs_le.mp (abs_exp_sub_one_le (x := t) (by simpa only [abs_of_nonneg ht0] using ht1))).2
  rw [abs_of_nonneg ht0] at hh
  linarith

lemma bounded_prime_log_sum (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (Y : ℕ) (hY : 1 ≤ log (Y : ℝ))
    (hpY : ∀ i, p i ≤ Y) : (∑ i, log (p i : ℝ)/(p i : ℝ)) ≤ 3*log (Y : ℝ) := by
  have hYpos : 0 < Y := by
    by_contra h
    have : Y = 0 := by omega
    simp only [this,Nat.cast_zero,log_zero] at hY
    linarith
  have hsub : univ.image p ⊆ (Y+1).primesBelow := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
    exact WeightedMertens.mem_primes.mpr ⟨hp i,hpY i⟩
  have hs := sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => log (q : ℝ)/(q : ℝ)) hsub
    (fun q hq hnot => div_nonneg (log_natCast_nonneg q) (Nat.cast_nonneg q))
  rw [sum_image hinj.injOn] at hs
  have hh := WeightedMertens.upper_bound Y hYpos
  change (∑ q ∈ (Y+1).primesBelow, log (q : ℝ)/(q : ℝ)) ≤ log (Y : ℝ)+log 4 at hh
  have hlog4 : log (4 : ℝ) ≤ 2 := by
    have he : log (4 : ℝ) = 2*log 2 := by rw [show (4 : ℝ)=2^2 by norm_num,log_pow]; norm_num
    rw [he]
    linarith [log_two_lt_d9]
  linarith only [hs,hh,hY,hlog4]

/-- The exponential tilt has absolute mean value. Crucially, the elementary
count-of-multiples product uses `(tiltedWeight-1)/p`, not `tiltedWeight/p`. -/
theorem tilted_divisor_cost_sum_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (Y R : ℕ) (hY : 1 ≤ log (Y : ℝ))
    (hpY : ∀ i, p i ≤ Y) :
    (∑ Q ∈ divisorSupport p R, ∏ i ∈ Q, primeCostWeight (p i)*exp (log (p i : ℝ)/log (Y : ℝ))) ≤
      exp 20*(R : ℝ) := by
  let t (i : ι) : ℝ := log (p i : ℝ)/log (Y : ℝ)
  let b (i : ι) : ℝ := primeCostWeight (p i)*exp (t i)-1
  have hlogY : 0 < log (Y : ℝ) := by linarith
  have ht (i : ι) : 0 ≤ t i ∧ t i ≤ 1 := by
    have hp0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
    have hlog := log_le_log hp0 (show (p i : ℝ) ≤ Y by exact_mod_cast hpY i)
    exact ⟨div_nonneg (log_natCast_nonneg _) hlogY.le,(div_le_one hlogY).mpr hlog⟩
  have hb (i : ι) : 0 ≤ b i := by
    have he := one_le_exp (ht i).1
    have hw := (primeCostWeight_bounds (p i) (hp i)).1
    dsimp only [b]
    nlinarith only [he,hw]
  have hterm (i : ι) : b i/(p i : ℝ) ≤
      2/((p i : ℝ)*((p i : ℝ)-1))+(6/log (Y : ℝ))*(log (p i : ℝ)/(p i : ℝ)) := by
    have hp0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
    have hp1 : 0 < (p i : ℝ)-1 := by
      have hh : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
      linarith
    have hw := primeCostWeight_bounds (p i) (hp i)
    have he := exp_le_one_add_two (t i) (ht i).1 (ht i).2
    have hmul := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ primeCostWeight (p i))
    have hwb := mul_le_mul_of_nonneg_right hw.2 (show 0 ≤ 2*t i by positivity)
    have hid : primeCostWeight (p i)-1 = 2/((p i : ℝ)-1) := by
      unfold primeCostWeight
      field_simp
      ring
    have hnum : b i ≤ 2/((p i : ℝ)-1)+6*t i := by dsimp only [b]; nlinarith only [hmul,hwb,hid]
    have hh := div_le_div_of_nonneg_right hnum hp0.le
    convert hh using 1 <;> dsimp only [t]
    field_simp
  have hc : (∑ i, 1/((p i : ℝ)*((p i : ℝ)-1))) ≤ 1 := by
    have hh := WeightedMertens.reciprocal_correction_le_one (univ.image p) (by
      intro q hq
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
      exact (hp i).two_le)
    rw [sum_image hinj.injOn] at hh
    exact hh
  have hs : (∑ i, b i/(p i : ℝ)) ≤ 20 := by
    have hh := sum_le_sum (s := univ) (fun i hi => hterm i)
    rw [sum_add_distrib] at hh
    have he : (∑ i, 2/((p i : ℝ)*((p i : ℝ)-1))) =
        2*∑ i, 1/((p i : ℝ)*((p i : ℝ)-1)) := by rw [mul_sum]; congr 1; funext i; ring
    rw [he,← mul_sum] at hh
    have hlog := mul_le_mul_of_nonneg_left (bounded_prime_log_sum p hp hinj Y hY hpY)
      (show 0 ≤ 6/log (Y : ℝ) by positivity)
    have hid : (6/log (Y : ℝ))*(3*log (Y : ℝ)) = 18 := by field_simp; norm_num
    rw [hid] at hlog
    linarith only [hh,hlog,hc]
  have hprod : (∏ i, (1+b i/(p i : ℝ))) ≤ exp 20 := by
    calc
      _ ≤ ∏ i, exp (b i/(p i : ℝ)) := by
        apply prod_le_prod
        · intro i hi
          have := hb i
          positivity
        · intro i hi
          linarith [add_one_le_exp (b i/(p i : ℝ))]
      _ = exp (∑ i, b i/(p i : ℝ)) := (exp_sum _ _).symm
      _ ≤ _ := exp_le_exp.mpr hs
  have hh := divisor_cost_sum_le_product p hp hinj R b hb
  have he (i : ι) : 1+b i = primeCostWeight (p i)*exp (log (p i : ℝ)/log (Y : ℝ)) := by dsimp [b,t]; ring
  simp_rw [he] at hh
  have hr := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg R)
  exact hh.trans (by simpa only [mul_comm] using hr)

lemma tilted_weight_product (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (Y : ℕ) (Q : Finset ι) :
    (∏ i ∈ Q, primeCostWeight (p i)*exp (log (p i : ℝ)/log (Y : ℝ))) =
      (∏ i ∈ Q, primeCostWeight (p i))*exp (log ((∏ i ∈ Q, p i : ℕ) : ℝ)/log (Y : ℝ)) := by
  rw [prod_mul_distrib,← exp_sum,← sum_div,Nat.cast_prod,log_prod (fun i hi => by exact_mod_cast (hp i).ne_zero)]

/-- Smooth support supplies exponential decay in the ratio log(R)/log(Y),
without altering the source main term or any moment-error hypothesis. -/
theorem smooth_divisor_cost_sum_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (Y R : ℕ) (hY : 1 ≤ log (Y : ℝ))
    (hpY : ∀ i, p i ≤ Y) (hR : 0 < R) :
    (∑ Q ∈ divisorSupport p R, ∏ i ∈ Q, primeCostWeight (p i)) ≤
      (exp 2+exp 20)*(R : ℝ)*exp (-log (R : ℝ)/(2*log (Y : ℝ))) := by
  classical
  let W (Q : Finset ι) : ℝ := ∏ i ∈ Q, primeCostWeight (p i)
  let d (Q : Finset ι) : ℕ := ∏ i ∈ Q, p i
  let S := (divisorSupport p R).filter (fun Q => (d Q : ℝ) ≤ sqrt (R : ℝ))
  let T := (divisorSupport p R).filter (fun Q => ¬(d Q : ℝ) ≤ sqrt (R : ℝ))
  let u := log (R : ℝ)/(2*log (Y : ℝ))
  have hlogY : 0 < log (Y : ℝ) := by linarith
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 ≤ log (R : ℝ) := log_natCast_nonneg R
  have hW (Q : Finset ι) : 0 ≤ W Q := prod_nonneg (fun i hi => (by norm_num : (0 : ℝ) ≤ 1).trans (primeCostWeight_bounds (p i) (hp i)).1)
  have hs : (∑ Q ∈ S, W Q) ≤ exp 2*sqrt (R : ℝ) := by
    have hsub : S ⊆ divisorSupport p ⌊sqrt (R : ℝ)⌋₊ := by
      intro Q hQ
      rw [mem_divisorSupport]
      exact Nat.le_floor (mem_filter.mp hQ).2
    have hh := sum_le_sum_of_subset_of_nonneg (f := W) hsub (fun Q hQ hnot => hW Q)
    have hc := divisor_cost_sum_le p hp hinj ⌊sqrt (R : ℝ)⌋₊
    have hfloor := Nat.floor_le (sqrt_nonneg (R : ℝ))
    exact (hh.trans hc).trans (mul_le_mul_of_nonneg_left hfloor (exp_pos 2).le)
  have ht : (∑ Q ∈ T, W Q) ≤ exp (-u)*(exp 20*(R : ℝ)) := by
    have hterm (Q : Finset ι) (hQ : Q ∈ T) : W Q ≤
        exp (-u)*(∏ i ∈ Q, primeCostWeight (p i)*exp (log (p i : ℝ)/log (Y : ℝ))) := by
      have hd : sqrt (R : ℝ) < (d Q : ℝ) := lt_of_not_ge (mem_filter.mp hQ).2
      have hlog := log_le_log (sqrt_pos.mpr hR0) hd.le
      rw [log_sqrt hR0.le] at hlog
      have hu : u ≤ log (d Q : ℝ)/log (Y : ℝ) := by
        have hh := div_le_div_of_nonneg_right hlog hlogY.le
        dsimp only [u]
        convert hh using 1 <;> ring
      have he := exp_le_exp.mpr hu
      have hm := mul_le_mul_of_nonneg_left he (hW Q)
      have hm' := mul_le_mul_of_nonneg_left hm (exp_pos (-u)).le
      have hid : exp (-u)*exp u = 1 := by rw [← exp_add,neg_add_cancel,exp_zero]
      have heq : exp (-u)*(W Q*exp u) = W Q := by
        calc
          _ = W Q*(exp (-u)*exp u) := by ring
          _ = W Q := by rw [hid,mul_one]
      rw [heq] at hm'
      rw [tilted_weight_product p hp]
      exact hm' 
    have hh := sum_le_sum hterm
    rw [← mul_sum] at hh
    have hsub : T ⊆ divisorSupport p R := filter_subset _ _
    have hs := sum_le_sum_of_subset_of_nonneg
      (f := fun Q : Finset ι => ∏ i ∈ Q, primeCostWeight (p i)*exp (log (p i : ℝ)/log (Y : ℝ)))
      hsub (by
        intro Q hQ hnot
        apply prod_nonneg
        intro i hi
        exact mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (primeCostWeight_bounds (p i) (hp i)).1) (exp_pos _).le)
    exact hh.trans (mul_le_mul_of_nonneg_left
      (hs.trans (tilted_divisor_cost_sum_le p hp hinj Y R hY hpY)) (exp_pos (-u)).le)
  have hsmall : sqrt (R : ℝ) ≤ (R : ℝ)*exp (-u) := by
    have hu : u ≤ log (R : ℝ)/2 := by
      dsimp only [u]
      apply (div_le_iff₀ (by positivity : 0 < 2*log (Y : ℝ))).mpr
      nlinarith only [mul_nonneg hlogR (show 0 ≤ log (Y : ℝ)-1 by linarith)]
    have he : sqrt (R : ℝ) = exp (log (R : ℝ)/2) := by rw [← log_sqrt hR0.le,exp_log (sqrt_pos.mpr hR0)]
    rw [he]
    calc
      _ ≤ exp (log (R : ℝ)-u) := exp_le_exp.mpr (by linarith only [hu])
      _ = _ := by rw [sub_eq_add_neg,exp_add,exp_log hR0]
  have hs' := mul_le_mul_of_nonneg_left hsmall (exp_pos 2).le
  have he := sum_filter_add_sum_filter_not (divisorSupport p R)
    (fun Q => (d Q : ℝ) ≤ sqrt (R : ℝ)) W
  change (∑ Q ∈ S, W Q)+(∑ Q ∈ T, W Q) = _ at he
  change (∑ Q ∈ divisorSupport p R, W Q) ≤ _
  rw [← he]
  have hu : -u = -log (R : ℝ)/(2*log (Y : ℝ)) := by dsimp only [u]; ring
  rw [← hu]
  nlinarith only [hs,ht,hs']

#print axioms tilted_divisor_cost_sum_le
#print axioms smooth_divisor_cost_sum_le
end Erdos970.FiniteSelberg
