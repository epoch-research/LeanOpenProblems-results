import FormalConjecturesUtil
import Submission.DivisorReindex

/-! Uniform logarithmic cancellation for a von-Mangoldt-weighted bilinear
commutator. For a smooth indicator, the multiplier is INSIDE its smoothness
cutoff. Primes outside that cutoff have coefficient zero, so this does not
estimate the outside-prime blocks in the Erdős 371 reduction. -/

namespace Erdos371LogarithmicSmoothCommutator

open Finset Filter
open scoped Topology

lemma sum_multiples {R : Type*} [AddCommMonoid R] {d N : ℕ} (hd : 0 < d) (f : ℕ → R) :
    (∑ m ∈ (Icc 1 N).filter (fun m => d ∣ m), f m) =
      ∑ k ∈ Icc 1 (N/d), f (k*d) := by
  symm
  apply sum_bij (fun k _ => k*d)
  · intro k hk
    obtain ⟨hk1,hkN⟩ := mem_Icc.mp hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hk1 hd,
      (Nat.le_div_iff_mul_le hd).mp hkN⟩,dvd_mul_left d k⟩
  · intro k hk l hl he
    exact Nat.eq_of_mul_eq_mul_right hd he
  · intro m hm
    obtain ⟨hmI,hdm⟩ := mem_filter.mp hm
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp hmI
    refine ⟨m/d,mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hm1 hdm) hd,
      Nat.div_le_div_right hmN⟩,Nat.div_mul_cancel hdm⟩
  · intro k hk
    rfl

lemma sum_divisors_reindex {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ m ∈ Icc 1 N, ∑ d ∈ m.divisors, f d m) =
      ∑ d ∈ Icc 1 N, ∑ k ∈ Icc 1 (N/d), f d (k*d) := by
  have he : (∑ m ∈ Icc 1 N, ∑ d ∈ m.divisors, f d m) =
      ∑ m ∈ Icc 1 N, ∑ d ∈ Icc 1 N, if d∣m then f d m else 0 := by
    apply sum_congr rfl
    intro m hm
    rw [Erdos371DivisorReindex.divisors_eq_filter_Icc hm,sum_filter]
  rw [he,sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter]
  exact sum_multiples (mem_Icc.mp hd).1 (f d)

noncomputable def bilinear (f : ℕ → ℝ) (d N : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 (N/d), f a*(f (a*d-1)-f (a*d+1))

noncomputable def weightedSum (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d*f d*bilinear f d N

lemma logarithmic_convolution (f : ℕ → ℝ)
    (hmul : ∀ a b, f (a*b)=f a*f b) (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d*f d*f (n/d)) =
      Real.log (n:ℝ)*f n := by
  calc
    _ = ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d*f n := by
      apply sum_congr rfl
      intro d hd
      rw [mul_assoc,← hmul,Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    _ = _ := by rw [← sum_mul,ArithmeticFunction.vonMangoldt_sum]

lemma weightedSum_eq_logarithmic_sum (f : ℕ → ℝ)
    (hmul : ∀ a b, f (a*b)=f a*f b) (N : ℕ) :
    weightedSum f N = ∑ n ∈ Icc 1 N,
      Real.log (n:ℝ)*f n*(f (n-1)-f (n+1)) := by
  have he : weightedSum f N = ∑ n ∈ Icc 1 N,
      ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d*f d*f (n/d)*(f (n-1)-f (n+1)) := by
    rw [sum_divisors_reindex]
    unfold weightedSum bilinear
    apply sum_congr rfl
    intro d hd
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [Nat.mul_div_cancel _ (mem_Icc.mp hd).1]
    ring
  rw [he]
  apply sum_congr rfl
  intro n hn
  rw [← sum_mul,logarithmic_convolution f hmul]

noncomputable def logStep (n : ℕ) : ℝ := Real.log (n+1:ℕ)-Real.log (n:ℝ)

lemma logStep_nonneg (n : ℕ) : 0 ≤ logStep n := by
  cases n with
  | zero => norm_num [logStep]
  | succ n =>
    apply sub_nonneg.mpr
    exact Real.log_le_log (by positivity : (0:ℝ)<(n+1:ℕ))
      (by exact_mod_cast (Nat.le_succ (n+1)))

lemma logStep_sum (N : ℕ) : (∑ n ∈ range N, logStep n) = Real.log (N:ℝ) := by
  simpa [logStep] using (Finset.sum_range_sub (fun n : ℕ => Real.log (n:ℝ)) N)

lemma logarithmic_sum_eq_boundary (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log (n:ℝ)*f n*(f (n-1)-f (n+1))) =
      (∑ n ∈ range N, f n*f (n+1)*logStep n)-Real.log (N:ℝ)*f N*f (N+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega),sum_range_succ,ih]
    simp only [Nat.add_sub_cancel]
    unfold logStep
    ring

/-- Exact identity for every completely multiplicative real-valued function. -/
theorem weightedSum_eq_boundary (f : ℕ → ℝ)
    (hmul : ∀ a b, f (a*b)=f a*f b) (N : ℕ) :
    weightedSum f N = (∑ n ∈ range N, f n*f (n+1)*logStep n)-
      Real.log (N:ℝ)*f N*f (N+1) := by
  rw [weightedSum_eq_logarithmic_sum f hmul,logarithmic_sum_eq_boundary]

/-- This bound is uniform over the whole class of [0,1]-valued completely
multiplicative functions, and therefore also over moving smoothness cutoffs. -/
theorem weightedSum_abs_le_log (f : ℕ → ℝ)
    (hmul : ∀ a b, f (a*b)=f a*f b) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1) (N : ℕ) :
    |weightedSum f N| ≤ Real.log (N:ℝ) := by
  have hp (n : ℕ) : 0 ≤ f n*f (n+1) ∧ f n*f (n+1) ≤ 1 :=
    ⟨mul_nonneg (hf n).1 (hf (n+1)).1,
      (mul_le_mul (hf n).2 (hf (n+1)).2 (hf (n+1)).1 (by norm_num)).trans_eq (by ring)⟩
  have hs0 : 0 ≤ ∑ n ∈ range N, f n*f (n+1)*logStep n :=
    sum_nonneg (fun n hn => mul_nonneg (hp n).1 (logStep_nonneg n))
  have hs1 : (∑ n ∈ range N, f n*f (n+1)*logStep n) ≤ Real.log (N:ℝ) := by
    rw [← logStep_sum]
    exact sum_le_sum (fun n hn => by
      simpa using mul_le_mul_of_nonneg_right (hp n).2 (logStep_nonneg n))
  have hb0 : 0 ≤ Real.log (N:ℝ)*f N*f (N+1) := by
    rw [mul_assoc]
    exact mul_nonneg (Real.log_natCast_nonneg N) (hp N).1
  have hb1 : Real.log (N:ℝ)*f N*f (N+1) ≤ Real.log (N:ℝ) := by
    rw [mul_assoc]
    simpa using mul_le_mul_of_nonneg_left (hp N).2 (Real.log_natCast_nonneg N)
  rw [weightedSum_eq_boundary f hmul]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

noncomputable def smooth (Y n : ℕ) : ℝ :=
  if 0<n ∧ Nat.maxPrimeFac n<Y then 1 else 0

lemma smooth_bounds (Y n : ℕ) : 0 ≤ smooth Y n ∧ smooth Y n ≤ 1 := by
  unfold smooth
  split_ifs <;> norm_num

lemma smooth_mul (Y a b : ℕ) : smooth Y (a*b)=smooth Y a*smooth Y b := by
  by_cases ha : a=0
  · simp [ha,smooth]
  by_cases hb : b=0
  · simp [hb,smooth]
  have ha0 : 0<a := Nat.pos_of_ne_zero ha
  have hb0 : 0<b := Nat.pos_of_ne_zero hb
  simp only [smooth,Nat.mul_pos ha0 hb0,ha0,hb0,true_and,
    Nat.maxPrimeFac_mul ha hb,max_lt_iff]
  split_ifs <;> simp_all

lemma smooth_weightedSum_bound (Y N : ℕ) :
    |weightedSum (smooth Y) N| ≤ Real.log (N:ℝ) :=
  weightedSum_abs_le_log (smooth Y) (smooth_mul Y) (smooth_bounds Y) N

/-- No uniformity hypothesis on the moving cutoff is required for THIS sum. -/
theorem moving_cutoff_mean_zero (Y : ℕ → ℕ) :
    Tendsto (fun N : ℕ => weightedSum (smooth (Y N)) N/N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hu : Tendsto (fun N : ℕ => Real.log (N:ℝ)/N) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    exact abs_nonneg _
  · intro N
    change |weightedSum (smooth (Y N)) N/(N:ℝ)| ≤ Real.log (N:ℝ)/N
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (smooth_weightedSum_bound (Y N) N) (Nat.cast_nonneg N)

/-- In particular, outside primes have ZERO coefficient in the proved sum.
They are exactly the prime range of interest in the original bin reduction. -/
lemma outside_prime_coefficient_zero {p Y : ℕ} (hp : p.Prime) (hY : Y ≤ p) :
    ArithmeticFunction.vonMangoldt p*smooth Y p=0 := by
  simp [smooth,hp.maxPrimeFac_eq_self,not_lt.mpr hY]

end Erdos371LogarithmicSmoothCommutator

#print axioms Erdos371LogarithmicSmoothCommutator.weightedSum_abs_le_log
#print axioms Erdos371LogarithmicSmoothCommutator.moving_cutoff_mean_zero
