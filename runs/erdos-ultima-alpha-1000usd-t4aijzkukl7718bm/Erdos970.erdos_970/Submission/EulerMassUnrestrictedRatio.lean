import Submission.EulerMassQuantitativeSectors

/-! Cumulative Euler-ratio errors without a large-denominator restriction.
The harmonic sum is a lower bound for the Euler product. In particular,
`initialEulerMass (floor (exp x)) ≥ x`, which avoids an artificial cutoff
when comparing profile sums close to the smallest primes. -/
namespace Erdos970.FiniteSelberg
open Finset Real
set_option maxHeartbeats 1300000

lemma harmonic_le_initialEulerMass (n : ℕ) : (harmonic n : ℝ) ≤ initialEulerMass n := by
  simpa [initialEulerMass] using harmonic_le_euler_add_tail n n

/-- The lower bound holds at every real exponential scale, not just at infinity. -/
lemma scaledEulerMass_ge_scale (t L : ℝ) : t*L ≤ initialEulerMass (expFloor t L) := by
  have hh := log_le_harmonic_floor (exp (t*L)) (exp_pos _).le
  rw [log_exp] at hh
  exact hh.trans (harmonic_le_initialEulerMass (expFloor t L))

lemma log_expFloor_abs_error_nonneg (t L : ℝ) (htL : 0 ≤ t*L) :
    1 ≤ expFloor t L ∧ |log (expFloor t L : ℝ)-t*L| ≤ 1 := by
  have hn : 1 ≤ expFloor t L := Nat.le_floor (by simpa only [Nat.cast_one] using one_le_exp_iff.mpr htL)
  have hn0 : (0 : ℝ) < expFloor t L := by exact_mod_cast (show 0 < expFloor t L by omega)
  have hlow : log (expFloor t L : ℝ) ≤ t*L := by
    simpa only [log_exp] using log_le_log hn0 (Nat.floor_le (exp_pos (t*L)).le)
  have hbig : exp (t*L) ≤ 2*(expFloor t L : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (exp (t*L))
    have hnR : (1 : ℝ) ≤ expFloor t L := by exact_mod_cast hn
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

lemma initialEulerMass_one : initialEulerMass 1=1 := by
  have he : (2 : ℕ).primesBelow=∅ := by decide +kernel
  simp [initialEulerMass,he,eulerMass]

/-- The additive error remains uniform even if the exponential floor is one. -/
theorem scaledEulerMass_additive_remainder_nonneg (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (t L : ℝ) (htL : 0 ≤ t*L) :
    |initialEulerMass (expFloor t L)-C*(t*L)| ≤ A+C+1 := by
  obtain ⟨hn,hl⟩ := log_expFloor_abs_error_nonneg t L htL
  have hnerr : |initialEulerMass (expFloor t L)-C*log (expFloor t L : ℝ)| ≤ A+1 := by
    by_cases hn2 : 2 ≤ expFloor t L
    · exact (hrem _ hn2).trans (by linarith)
    · have he : expFloor t L=1 := by omega
      rw [he,initialEulerMass_one]
      norm_num
      linarith
  have hid : initialEulerMass (expFloor t L)-C*(t*L) =
      (initialEulerMass (expFloor t L)-C*log (expFloor t L : ℝ))+
        C*(log (expFloor t L : ℝ)-t*L) := by ring
  rw [hid]
  have hh := abs_add_le (initialEulerMass (expFloor t L)-C*log (expFloor t L : ℝ))
    (C*(log (expFloor t L : ℝ)-t*L))
  rw [abs_mul,abs_of_pos hC] at hh
  have he := mul_le_mul_of_nonneg_left hl hC.le
  nlinarith only [hh,hnerr,he]

lemma abs_ratio_sub_le_of_den_lower (C B a b x y : ℝ) (hB : 0 ≤ B)
    (ha : 0 ≤ a) (hb : 0 < b) (hy : b ≤ y)
    (hxerr : |x-C*a| ≤ B) (hyerr : |y-C*b| ≤ B) :
    |x/y-a/b| ≤ (B/b)*(1+a/b) := by
  have hy0 : 0 < y := hb.trans_le hy
  have hnum : |(x-C*a)-(a/b)*(y-C*b)| ≤ B+(a/b)*B := by
    calc
      _ ≤ |x-C*a|+|(a/b)*(y-C*b)| := abs_sub _ _
      _ = |x-C*a|+(a/b)*|y-C*b| := by
        rw [abs_mul,abs_of_nonneg (div_nonneg ha hb.le)]
      _ ≤ _ := add_le_add hxerr (mul_le_mul_of_nonneg_left hyerr (div_nonneg ha hb.le))
  have hid : x/y-a/b = ((x-C*a)-(a/b)*(y-C*b))/y := by
    field_simp [hb.ne',hy0.ne']
    <;> ring
  rw [hid,abs_div,abs_of_pos hy0]
  calc
    _ ≤ (B+(a/b)*B)/y := div_le_div_of_nonneg_right hnum hy0.le
    _ ≤ (B+(a/b)*B)/b := div_le_div_of_nonneg_left (by positivity) hb hy
    _ = _ := by ring

/-- All positive denominator scales are allowed; there is no hypothesis
`2*(A+C) ≤ C*t*L` and no lower bound on t*L beyond positivity. -/
theorem scaledEulerMass_ratio_unrestricted (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (v t L : ℝ) (hv : 0 ≤ v) (ht : 0 < t) (hL : 0 < L) :
    |initialEulerMass (expFloor v L)/initialEulerMass (expFloor t L)-v/t| ≤
      ((A+C+1)/(t*L))*(1+v/t) := by
  have hh := abs_ratio_sub_le_of_den_lower C (A+C+1) (v*L) (t*L) _ _ (by positivity)
    (mul_nonneg hv hL.le) (mul_pos ht hL) (scaledEulerMass_ge_scale t L)
    (scaledEulerMass_additive_remainder_nonneg C A hC hA hrem v L (mul_nonneg hv hL.le))
    (scaledEulerMass_additive_remainder_nonneg C A hC hA hrem t L (mul_pos ht hL).le)
  have he : (v*L)/(t*L)=v/t := by field_simp
  simpa only [he] using hh

#print axioms harmonic_le_initialEulerMass
#print axioms scaledEulerMass_ge_scale
#print axioms scaledEulerMass_additive_remainder_nonneg
#print axioms scaledEulerMass_ratio_unrestricted
end Erdos970.FiniteSelberg
