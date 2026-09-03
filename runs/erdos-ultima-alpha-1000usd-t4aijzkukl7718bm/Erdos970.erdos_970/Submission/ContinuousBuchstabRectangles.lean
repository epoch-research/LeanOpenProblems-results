import Submission.ContinuousBuchstabMonotone

/-! Explicit rectangle-sum upper approximations for nonnegative antitone
profiles. These bounds allow arbitrarily fine finite prime-sector partitions. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
set_option maxHeartbeats 1000000

lemma antitone_rectangle_bound (f : ℝ → ℝ) (a h : ℝ) (N : ℕ) (hh : 0 < h)
    (hf : AntitoneOn f (Ici a)) (hp : ∀ x : ℝ, a ≤ x → 0 ≤ f x)
    (hi : IntegrableOn f (Ioi a)) :
    (∑ j ∈ Finset.range N, h*f (a+h*j)) ≤ tailIntegral f a+h*f a := by
  have hmono : AntitoneOn (fun x : ℝ => f (a+h*x)) (Icc 0 (0+(N : ℝ))) := by
    intro x hx y hy hxy
    apply hf
    · change a ≤ a+h*x
      have hx0 := (mem_Icc.mp hx).1
      nlinarith only [hh,hx0]
    · change a ≤ a+h*y
      have hy0 := (mem_Icc.mp hy).1
      nlinarith only [hh,hy0]
    · nlinarith only [hh,hxy]
  have hright := hmono.sum_le_integral
  simp only [zero_add] at hright
  rw [intervalIntegral.integral_comp_add_mul f hh.ne' a, mul_zero, add_zero, smul_eq_mul] at hright
  have hr := mul_le_mul_of_nonneg_left hright hh.le
  rw [mul_inv_cancel_left₀ hh.ne'] at hr
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hab : a ≤ a+h*N := by nlinarith only [hh,hN]
  have hint : (∫ x in a..a+h*N, f x) ≤ tailIntegral f a := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hp x (mem_Ioi.mp hx).le
    · exact Eventually.of_forall (fun x hx => (mem_Ioc.mp hx).1)
  have ht := Finset.sum_range_sub' (fun j : ℕ => f (a+h*j)) N
  rw [Finset.sum_sub_distrib] at ht
  simp only [Nat.cast_zero, mul_zero, add_zero] at ht
  have hm := mul_le_mul_of_nonneg_left (hp (a+h*N) hab) hh.le
  have htel := congrArg (fun z : ℝ => h*z) ht
  rw [← Finset.mul_sum]
  nlinarith only [hr,hint,htel,hm]

/-- For every positive interval width and every positive slack, a finite uniform
mesh has an upper rectangle sum within that slack of the full tail integral. -/
theorem exists_rectangular_upper (f : ℝ → ℝ) (a b ε : ℝ) (hab : a < b) (hε : 0 < ε)
    (hf : AntitoneOn f (Ici a)) (hp : ∀ x : ℝ, a ≤ x → 0 ≤ f x)
    (hi : IntegrableOn f (Ioi a)) :
    ∃ N : ℕ, 0 < N ∧
      (∑ j ∈ Finset.range N, ((b-a)/(N : ℝ))*f (a+((b-a)/(N : ℝ))*j)) < tailIntegral f a+ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 ((b-a)*f a/ε))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNnat : 0 < N := by exact_mod_cast hN0
  have hh : 0 < (b-a)/(N : ℝ) := div_pos (sub_pos.mpr hab) hN0
  have he : ((b-a)/(N : ℝ))*f a < ε := by
    have hlt := (le_max_right _ _).trans_lt hN
    have hm := (div_lt_iff₀ hε).mp hlt
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hN0).mpr
    nlinarith only [hm]
  refine ⟨N,hNnat,(antitone_rectangle_bound f a ((b-a)/(N : ℝ)) N hh hf hp hi).trans_lt ?_⟩
  linarith only [he]

#print axioms antitone_rectangle_bound
#print axioms exists_rectangular_upper
end Erdos970.ContinuousBuchstab
