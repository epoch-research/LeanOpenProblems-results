import Submission.EulerMassRemainder
import Submission.EulerMassScaling

/-! Quantitative first-hit sector masses. Unlike a fixed-sector limit, the
bound below is uniform over all sector endpoints above a positive scale a.
The exact prime-density telescope, including strict prefixes, is retained. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter
open scoped Topology
set_option maxHeartbeats 1200000

/-- A ratio estimate keeping both additive remainders. -/
lemma abs_ratio_sub_le_of_additive (C A a b x y : ℝ)
    (hC : 0 < C) (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 < b) (hy : 0 < y)
    (hxerr : |x-C*a| ≤ A) (hyerr : |y-C*b| ≤ A) (hlarge : 2*A ≤ C*b) :
    |x/y-a/b| ≤ (2*A/(C*b))*(1+a/b) := by
  have hden : C*b/2 ≤ y := by
    have := (abs_le.mp hyerr).1
    linarith only [this,hlarge]
  have hnum : |(x-C*a)-(a/b)*(y-C*b)| ≤ A+(a/b)*A := by
    calc
      _ ≤ |x-C*a|+|(a/b)*(y-C*b)| := abs_sub _ _
      _ = |x-C*a|+(a/b)*|y-C*b| := by
        rw [abs_mul,abs_of_nonneg (div_nonneg ha hb.le)]
      _ ≤ _ := add_le_add hxerr (mul_le_mul_of_nonneg_left hyerr (div_nonneg ha hb.le))
  have hid : x/y-a/b = ((x-C*a)-(a/b)*(y-C*b))/y := by
    field_simp [hb.ne',hy.ne']
    <;> ring
  rw [hid,abs_div,abs_of_pos hy]
  calc
    _ ≤ (A+(a/b)*A)/y := div_le_div_of_nonneg_right hnum hy.le
    _ ≤ (A+(a/b)*A)/(C*b/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by field_simp <;> ring

/-- A quantitative ratio bound at arbitrary natural indices. -/
theorem initialEulerMass_ratio_remainder (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hlarge : 2*A ≤ C*log (n : ℝ)) :
    |initialEulerMass m/initialEulerMass n-log (m : ℝ)/log (n : ℝ)| ≤
      (2*A/(C*log (n : ℝ)))*(1+log (m : ℝ)/log (n : ℝ)) := by
  exact abs_ratio_sub_le_of_additive C A _ _ _ _ hC hA
    (log_natCast_nonneg m) (log_pos (by exact_mod_cast (show 1 < n by omega)))
    (initialEulerMass_pos n) (hrem m hm) (hrem n hn) hlarge

lemma log_expFloor_abs_error (t L : ℝ) (htL : 2 ≤ t*L) :
    2 ≤ expFloor t L ∧ |log (expFloor t L : ℝ)-t*L| ≤ 1 := by
  have hexp : (2 : ℝ) ≤ exp (t*L) := by linarith [add_one_le_exp (t*L)]
  have hn : 2 ≤ expFloor t L := Nat.le_floor hexp
  have hn0 : (0 : ℝ) < expFloor t L := by exact_mod_cast (show 0 < expFloor t L by omega)
  have hlow : log (expFloor t L : ℝ) ≤ t*L := by
    simpa only [log_exp] using log_le_log hn0 (Nat.floor_le (exp_pos (t*L)).le)
  have hbig : exp (t*L) ≤ 2*(expFloor t L : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (exp (t*L))
    have hnR : (2 : ℝ) ≤ expFloor t L := by exact_mod_cast hn
    change exp (t*L) < (expFloor t L : ℝ)+1 at hfloor
    linarith only [hfloor,hnR]
  have hhigh := log_le_log (exp_pos (t*L)) hbig
  rw [log_exp,log_mul (by norm_num) hn0.ne'] at hhigh
  have hl2 : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num only [show (2 : ℝ)-1=1 by norm_num] at h
    exact h
  refine ⟨hn,?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hlow)]
  linarith only [hhigh,hl2]

/-- The additive error survives the exponential floor with a single constant,
uniformly in both scale and level. -/
theorem scaledEulerMass_additive_remainder (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (t L : ℝ) (htL : 2 ≤ t*L) :
    |initialEulerMass (expFloor t L)-C*(t*L)| ≤ A+C := by
  obtain ⟨hn,hl⟩ := log_expFloor_abs_error t L htL
  have hid : initialEulerMass (expFloor t L)-C*(t*L) =
      (initialEulerMass (expFloor t L)-C*log (expFloor t L : ℝ))+
        C*(log (expFloor t L : ℝ)-t*L) := by ring
  rw [hid]
  calc
    _ ≤ |initialEulerMass (expFloor t L)-C*log (expFloor t L : ℝ)|+
        |C*(log (expFloor t L : ℝ)-t*L)| := abs_add_le _ _
    _ ≤ A+C := by
      rw [abs_mul,abs_of_pos hC]
      have hh := mul_le_mul_of_nonneg_left hl hC.le
      simpa only [mul_one] using add_le_add (hrem _ hn) hh

/-- A quantitative scaled ratio; the endpoints need not be fixed in advance. -/
theorem scaledEulerMass_ratio_remainder (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (v t L : ℝ) (hv : 0 ≤ v) (ht : 0 < t) (hL : 0 < L)
    (hvL : 2 ≤ v*L) (htL : 2 ≤ t*L) (hlarge : 2*(A+C) ≤ C*(t*L)) :
    |initialEulerMass (expFloor v L)/initialEulerMass (expFloor t L)-v/t| ≤
      (2*(A+C)/(C*(t*L)))*(1+v/t) := by
  have hh := abs_ratio_sub_le_of_additive C (A+C) (v*L) (t*L) _ _ hC (by positivity)
    (mul_nonneg hv hL.le) (mul_pos ht hL) (initialEulerMass_pos _)
    (scaledEulerMass_additive_remainder C A hC hA hrem v L hvL)
    (scaledEulerMass_additive_remainder C A hC hA hrem t L htL) hlarge
  have he : (v*L)/(t*L)=v/t := by field_simp
  simpa only [he] using hh

/-- Uniform first-hit sector error. The sector endpoints t,u may vary with L;
only the positive lower scale a and the displayed lower size bounds are needed.
In particular, this is stronger than a pointwise fixed-sector limit. -/
theorem firstHit_sector_uniform_remainder (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (a v t u L : ℝ) (ha : 0 < a) (hv : 0 ≤ v) (hat : a ≤ t) (htu : t ≤ u)
    (hL : 0 < L) (hvL : 2 ≤ v*L) (haL : 2 ≤ a*L)
    (hlarge : 2*(A+C) ≤ C*(a*L)) :
    |initialEulerMass (expFloor v L)*
      (∑ p ∈ (Ioc (expFloor t L) (expFloor u L)).filter Nat.Prime,
        (1/(p : ℝ))*(1/eulerMass p.primesBelow))-(v/t-v/u)| ≤
      (4*(A+C)/(C*(a*L)))*(1+v/a) := by
  have ht : 0 < t := ha.trans_le hat
  have hu : 0 < u := ht.trans_le htu
  have hau : a ≤ u := hat.trans htu
  have hratio (w : ℝ) (haw : a ≤ w) :
      |initialEulerMass (expFloor v L)/initialEulerMass (expFloor w L)-v/w| ≤
        (2*(A+C)/(C*(a*L)))*(1+v/a) := by
    have hw : 0 < w := ha.trans_le haw
    have hscale := mul_le_mul_of_nonneg_right haw hL.le
    have hh := scaledEulerMass_ratio_remainder C A hC hA hrem v w L hv hw hL hvL
      (haL.trans hscale) (hlarge.trans (mul_le_mul_of_nonneg_left hscale hC.le))
    apply hh.trans
    apply mul_le_mul
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hscale hC.le)
    · exact add_le_add le_rfl (div_le_div_of_nonneg_left hv ha haw)
    · positivity
    · positivity
  have htuF : expFloor t L ≤ expFloor u L :=
    Nat.floor_le_floor (exp_le_exp.mpr (mul_le_mul_of_nonneg_right htu hL.le))
  rw [density_annulus_telescope _ _ htuF]
  have hid : initialEulerMass (expFloor v L)*
      (1/initialEulerMass (expFloor t L)-1/initialEulerMass (expFloor u L))-(v/t-v/u) =
      (initialEulerMass (expFloor v L)/initialEulerMass (expFloor t L)-v/t)-
        (initialEulerMass (expFloor v L)/initialEulerMass (expFloor u L)-v/u) := by ring
  rw [hid]
  apply (abs_sub _ _).trans
  have hh := add_le_add (hratio t hat) (hratio u hau)
  convert hh using 1 <;> ring

#print axioms initialEulerMass_ratio_remainder
#print axioms scaledEulerMass_additive_remainder
#print axioms scaledEulerMass_ratio_remainder
#print axioms firstHit_sector_uniform_remainder
end Erdos970.FiniteSelberg
