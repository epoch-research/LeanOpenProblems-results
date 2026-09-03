import Submission.BuchstabEulerCoordinates
import Submission.ContinuousBuchstabRectangles

/-! Exact shifted-profile comparison for the finite first-hit measure.
Right rectangles in reciprocal Euler coordinates give a one-sided integral
bound with no quadrature remainder and no omitted prime tail. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Finset MeasureTheory Filter
set_option maxHeartbeats 1800000

lemma antitone_right_rectangles (v : ℕ → ℝ) (hv : Antitone v) (N : ℕ)
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici (v N))) :
    (∑ i ∈ range N, (v i-v (i+1))*f (v i)) ≤ ∫ x in v N..v 0, f x := by
  have hi (i : ℕ) (hi : i < N) : IntervalIntegrable f volume (v (i+1)) (v i) := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (hv (Nat.le_succ i))]
    exact hf.mono (fun x hx => (hv (by omega : i+1 ≤ N)).trans hx.1)
  have hrect (i : ℕ) (hiN : i < N) :
      (v i-v (i+1))*f (v i) ≤ ∫ x in v (i+1)..v i, f x := by
    have hh := intervalIntegral.integral_mono_on (hv (Nat.le_succ i))
      (intervalIntegral.intervalIntegrable_const (c := f (v i))) (hi i hiN) (by
        intro x hx
        exact hf ((hv (by omega : i+1 ≤ N)).trans hx.1) (hv hiN.le) hx.2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (fun i hiN => (hi i hiN).symm)
  have hsum' := congrArg (fun x : ℝ => -x) hsum
  dsimp only at hsum'
  rw [← sum_neg_distrib] at hsum'
  simp_rw [← intervalIntegral.integral_symm] at hsum'
  exact (sum_le_sum (fun i hiN => hrect i (mem_range.mp hiN))).trans_eq hsum'

lemma antitone_right_rectangles_le_tail (v : ℕ → ℝ) (hv : Antitone v) (N : ℕ)
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici (v N)))
    (hf0 : ∀ x, v N ≤ x → 0 ≤ f x) (hfi : IntegrableOn f (Ioi (v N))) :
    (∑ i ∈ range N, (v i-v (i+1))*f (v i)) ≤ tailIntegral f (v N) := by
  apply (antitone_right_rectangles v hv N f hf).trans
  rw [intervalIntegral.integral_of_le (hv (Nat.zero_le N))]
  apply setIntegral_mono_set hfi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hf0 x (mem_Ioi.mp hx).le
  · exact Eventually.of_forall (fun x hx => (mem_Ioc.mp hx).1)

/-- Exact reciprocal-coordinate quadrature. The coefficient of the tail
integral is one, independently of the number or spacing of the knots. -/
theorem reciprocal_coordinate_profile_sum (T : ℕ → ℝ) (hT : ∀ i, 0 < T i)
    (hTm : Monotone T) (N : ℕ) (s : ℝ) (hs : 0 < s)
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici (s-1)))
    (hf0 : ∀ x, s-1 ≤ x → 0 ≤ f x) (hfi : IntegrableOn f (Ioi (s-1))) :
    (∑ i ∈ range N, (T N*(1/T i-1/T (i+1)))*f (s*T N/T i-1)) ≤
      tailIntegral f (s-1)/s := by
  let v : ℕ → ℝ := fun i => s*T N/T i-1
  have hv : Antitone v := by
    intro i j hij
    exact sub_le_sub_right
      (div_le_div_of_nonneg_left (mul_pos hs (hT N)).le (hT i) (hTm hij)) 1
  have hvN : v N=s-1 := by dsimp [v]; rw [mul_div_cancel_right₀ _ (hT N).ne']
  have hh := antitone_right_rectangles_le_tail v hv N f
    (by simpa only [hvN] using hf) (by simpa only [hvN] using hf0)
    (by simpa only [hvN] using hfi)
  rw [hvN] at hh
  have hdiv := div_le_div_of_nonneg_right hh hs.le
  rw [sum_div] at hdiv
  apply le_trans _ hdiv
  apply le_of_eq
  apply sum_congr rfl
  intro i hi
  dsimp only [v]
  field_simp [hs.ne',(hT i).ne',(hT (i+1)).ne']
  <;> ring

end Erdos970.ContinuousBuchstab

namespace Erdos970.RecursiveSieve.Buchstab
open Real Set Finset MeasureTheory Filter FiniteSelberg ContinuousBuchstab
set_option maxHeartbeats 1800000

lemma euler_shifted_child_coordinate (C B s : ℝ) (hC : 0 < C)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (k i : ℕ) :
    s*eulerCoordinate C k/eulerCoordinate C i-1 ≤
      (s*eulerCoordinate C k+B-log (nthPrime i : ℝ))/eulerCoordinate C i := by
  have hh := (abs_le.mp (hB i)).1
  have hT := eulerCoordinate_pos C hC i
  apply (le_div_iff₀ hT).mpr
  rw [sub_mul,div_mul_cancel₀ _ hT.ne',one_mul]
  linarith only [hh]

/-- The shift is in the logarithmic level, not an additive summation loss.
Every prime of the strict prefix is retained, including the smallest. -/
theorem euler_shifted_profile_sum (C B s : ℝ) (hC : 0 < C) (hs : 0 < s)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (k : ℕ) (f : ℝ → ℝ) (hf : AntitoneOn f (Ici (s-1)))
    (hf0 : ∀ x, s-1 ≤ x → 0 ≤ f x) (hfi : IntegrableOn f (Ioi (s-1))) :
    (∑ i : Fin k, primeMarginal i.val*prefixDensity primeMarginal i.val*
      f ((s*eulerCoordinate C k+B-log (nthPrime i.val : ℝ))/eulerCoordinate C i.val)) ≤
      prefixDensity primeMarginal k*(tailIntegral f (s-1)/s) := by
  have hTm := eulerCoordinate_monotone C hC
  have hT := eulerCoordinate_pos C hC
  have hd := nthPrime_prefix_density_pos k
  let v : ℕ → ℝ := fun i => s*eulerCoordinate C k/eulerCoordinate C i-1
  let w : ℕ → ℝ := fun i => (s*eulerCoordinate C k+B-log (nthPrime i : ℝ))/eulerCoordinate C i
  have hlow (i : ℕ) (hi : i ≤ k) : s-1 ≤ v i := by
    have hh := div_le_div_of_nonneg_left (mul_pos hs (hT k)).le (hT i) (hTm hi)
    rw [mul_div_cancel_right₀ _ (hT k).ne'] at hh
    exact sub_le_sub_right hh 1
  have hchild (i : ℕ) : v i ≤ w i := euler_shifted_child_coordinate C B s hC hB k i
  have hsum : (∑ i : Fin k, primeMarginal i.val*prefixDensity primeMarginal i.val*f (w i.val)) ≤
      (∑ i : Fin k, primeMarginal i.val*prefixDensity primeMarginal i.val*f (v i.val)) := by
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (hf (hlow i.val i.isLt.le) ((hlow i.val i.isLt.le).trans (hchild i.val)) (hchild i.val))
      (mul_pos (primeMarginal_pos i.val) (nthPrime_prefix_density_pos i.val)).le
  have hquad := reciprocal_coordinate_profile_sum (eulerCoordinate C) hT hTm k s hs f hf hf0 hfi
  have hm := mul_le_mul_of_nonneg_left hquad hd.le
  have he : (∑ i : Fin k, primeMarginal i.val*prefixDensity primeMarginal i.val*f (v i.val)) =
      prefixDensity primeMarginal k*
        (∑ i ∈ range k, (eulerCoordinate C k*(1/eulerCoordinate C i-1/eulerCoordinate C (i+1)))*
          f (s*eulerCoordinate C k/eulerCoordinate C i-1)) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => primeMarginal i*prefixDensity primeMarginal i*f (v i)) k,mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [eulerCoordinate_weight C hC k i]
    dsimp only [v]
    field_simp [hd.ne']
  exact hsum.trans (he ▸ hm)

/-- Exact rescaling of the child divisor level with the shifted coordinate. -/
lemma euler_shifted_child_level (C B b s : ℝ) (hC : 0 < C) (k i : ℕ) :
    exp (s*eulerCoordinate C k+b+B)*primeMarginal i =
      exp (((s*eulerCoordinate C k+B-log (nthPrime i : ℝ))/eulerCoordinate C i)*
        eulerCoordinate C i+b) := by
  have hp0 : (0 : ℝ) < nthPrime i := by exact_mod_cast (nthPrime_prime i).pos
  rw [div_mul_cancel₀ _ (eulerCoordinate_pos C hC i).ne']
  rw [show s*eulerCoordinate C k+B-log (nthPrime i : ℝ)+b=
    (s*eulerCoordinate C k+b+B)-log (nthPrime i : ℝ) by ring,
    exp_sub,exp_log hp0]
  simp only [primeMarginal,mul_one_div]

#print axioms reciprocal_coordinate_profile_sum
#print axioms euler_shifted_profile_sum
#print axioms euler_shifted_child_level
end Erdos970.RecursiveSieve.Buchstab
