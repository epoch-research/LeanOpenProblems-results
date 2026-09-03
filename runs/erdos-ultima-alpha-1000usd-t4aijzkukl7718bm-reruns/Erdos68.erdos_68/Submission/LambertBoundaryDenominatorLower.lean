import Submission.FilteredGcdUniformBound
import Submission.LambertBoundaryForms

/-!
A lower divisibility bound for simultaneous clearing of a whole window of
raw Lambert boundaries. This is not a bound on a single aggregate form,
and it does not settle Erdős Problem 68.
-/

namespace LambertBoundaryDenominatorLower

open Finset Erdos68Development LambertDifferenceOperators LambertRawBounds
  LambertBoundaryClearing LambertBoundaryForms BinomialFilteredLambert
  FilteredGcdPolynomialBound FilteredGcdUniformBound

lemma rawApply_translate (ds : List ℕ) (r : ℕ → ℝ) (h n : ℕ) :
    rawApply ds (fun m => r (m+h)) n = rawApply ds r (n+h) := by
  induction ds generalizing r with
  | nil => rfl
  | cons d ds ih =>
    simp only [rawApply]
    have he : rawShift d (fun m => r (m+h)) = fun m => rawShift d r (m+h) := by
      funext m
      simp only [rawShift]
      rw [show m+d+h=m+h+d by omega]
    rw [he, ih]

lemma prefixQ_difference (n : ℕ) :
    prefixQ (n+1)-prefixQ n = (lambertCoeff (n+1) : ℚ)/(n+1).factorial := by
  simp only [prefixQ, Finset.sum_range_succ, add_sub_cancel_left]

/-- The boundary difference is the actual binomially filtered coefficient,
with the full shift in its factorial index included. -/
theorem scaled_boundary_difference (ds : List ℕ) (n : ℕ) :
    ((n+1+ds.sum).factorial : ℚ)*(boundary ds (n+1)-boundary ds n) =
      (factorialProduct ds : ℚ)*(filtered ds (n+1+ds.sum) : ℚ) := by
  have he : (fun m => (prefixQ (m+1) : ℝ)-(prefixQ m : ℝ)) =
      (fun m => (lambertCoeff (m+1) : ℝ)/(m+1).factorial) := by
    funext m
    have hq := congrArg (fun q : ℚ => (q : ℝ)) (prefixQ_difference m)
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using hq
  have hd : (boundary ds (n+1) : ℝ)-(boundary ds n : ℝ) =
      rawApply ds (fun m => (lambertCoeff m : ℝ)/m.factorial) (n+1) := by
    have hsub := congrFun (rawApply_sub ds
      (fun m => (prefixQ (m+1) : ℝ)) (fun m => (prefixQ m : ℝ))) n
    rw [boundary_cast, boundary_cast, ← rawApply_translate ds
      (fun m => (prefixQ m : ℝ)) 1 n, ← hsub, he]
    exact rawApply_translate ds (fun m => (lambertCoeff m : ℝ)/m.factorial) 1 n
  have hreal : ((n+1+ds.sum).factorial : ℝ)*
      ((boundary ds (n+1) : ℝ)-(boundary ds n : ℝ)) =
      (factorialProduct ds : ℝ)*(filtered ds (n+1+ds.sum) : ℝ) := by
    rw [hd, rawApply_eq, ← factorialProduct_cast, mul_left_comm,
      filtered_lambert_scaled_identity]
  exact_mod_cast hreal

lemma boundary_difference (ds : List ℕ) (n : ℕ) :
    boundary ds (n+1)-boundary ds n =
      (factorialProduct ds : ℚ)*(filtered ds (n+1+ds.sum) : ℚ)/
        (n+1+ds.sum).factorial := by
  have hf : ((n+1+ds.sum).factorial : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hf).mpr
  simpa only [mul_comm] using scaled_boundary_difference ds n

/-- A common multiplier of adjacent raw boundaries clears the filtered
individual coefficients after multiplication by the raw operator content. -/
theorem commonDenominator_dvd_boundary_multiplier (ds : List ℕ) (H N D : ℕ)
    (hH : ds.sum < H)
    (hclear : ∀ m ∈ Finset.Icc (H-ds.sum-1) (N-ds.sum),
      ∃ z : ℤ, (D : ℚ)*boundary ds m=z) :
    commonDenominator (filtered ds) H N ∣ D*factorialProduct ds := by
  apply (commonDenominator_dvd_iff_integral (filtered ds) H N
    (D*factorialProduct ds)).mpr
  intro k hk
  have hkH := (Finset.mem_Icc.mp hk).1
  have hkN := (Finset.mem_Icc.mp hk).2
  let m := k-ds.sum-1
  have hindex : m+1+ds.sum=k := by dsimp [m]; omega
  have hm : m ∈ Finset.Icc (H-ds.sum-1) (N-ds.sum) := by
    apply Finset.mem_Icc.mpr
    dsimp [m]
    omega
  have hm1 : m+1 ∈ Finset.Icc (H-ds.sum-1) (N-ds.sum) := by
    apply Finset.mem_Icc.mpr
    dsimp [m]
    omega
  obtain ⟨z0, hz0⟩ := hclear m hm
  obtain ⟨z1, hz1⟩ := hclear (m+1) hm1
  refine ⟨z1-z0, ?_⟩
  have he := boundary_difference ds m
  rw [hindex] at he
  calc
    ((D*factorialProduct ds : ℕ) : ℚ)*(filtered ds k : ℚ)/k.factorial =
        (D : ℚ)*(boundary ds (m+1)-boundary ds m) := by
      rw [he]
      push_cast
      ring
    _ = (z1-z0 : ℤ) := by rw [mul_sub, hz1, hz0]; push_cast; rfl

/-- The lower bound is for simultaneous clearing of every boundary in the
window. It does not constrain the denominator of a chosen weighted sum. -/
theorem factorial_pred_dvd_boundary_multiplier (ds : List ℕ) (K H N D : ℕ)
    (hH : ds.sum < H) (hH2 : 2 ≤ H) (hHN : 2*H ≤ N)
    (hwide : H+K*(K+1) ≤ N)
    (hks : ∀ k ∈ ds, 2 ≤ k ∧ k ≤ K)
    (hclear : ∀ m ∈ Finset.Icc (H-ds.sum-1) (N-ds.sum),
      ∃ z : ℤ, (D : ℚ)*boundary ds m=z) :
    (N-1).factorial ∣ (primorial K)^(2*(K+1))*D*factorialProduct ds := by
  have hcoeff := factorial_pred_dvd_commonDenominator ds K H N hH2 hHN hwide hks
  have hdiv := commonDenominator_dvd_boundary_multiplier ds H N D hH hclear
  exact (hcoeff.trans (Nat.mul_dvd_mul_left _ hdiv)) |>
    fun h => by simpa only [mul_assoc] using h

end LambertBoundaryDenominatorLower

#print axioms LambertBoundaryDenominatorLower.scaled_boundary_difference
#print axioms LambertBoundaryDenominatorLower.commonDenominator_dvd_boundary_multiplier
#print axioms LambertBoundaryDenominatorLower.factorial_pred_dvd_boundary_multiplier
