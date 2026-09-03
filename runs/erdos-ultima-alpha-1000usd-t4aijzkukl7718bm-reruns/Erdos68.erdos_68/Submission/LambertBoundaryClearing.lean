import Submission.LambertDifferenceCheck
import Submission.LambertRawBounds

/-! A common integral clearing factor for a whole finite window of raw
Lambert boundaries. This supplies integrality, not nonvanishing of forms. -/
namespace LambertBoundaryClearing

open Finset Erdos68Development LambertDifferenceOperators LambertRawBounds

def factorialProduct (ds : List ℕ) : ℕ := (ds.map Nat.factorial).prod

def commonMultiplier (ds : List ℕ) (H : ℕ) : ℕ :=
  (H + ds.sum).factorial / factorialProduct ds

lemma factorialProduct_dvd (ds : List ℕ) : factorialProduct ds ∣ ds.sum.factorial := by
  induction ds with
  | nil => simp [factorialProduct]
  | cons d ds ih =>
    simp only [factorialProduct, List.map_cons, List.prod_cons, List.sum_cons] at *
    exact (Nat.mul_dvd_mul_left d.factorial ih).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add d ds.sum)

lemma factorialProduct_pos (ds : List ℕ) : 0 < factorialProduct ds := by
  induction ds with
  | nil => simp [factorialProduct]
  | cons d ds ih =>
    simpa only [factorialProduct, List.map_cons, List.prod_cons] using
      Nat.mul_pos (Nat.factorial_pos d) ih

lemma factorialProduct_dvd_shift (ds : List ℕ) (H : ℕ) :
    factorialProduct ds ∣ (H + ds.sum).factorial :=
  (factorialProduct_dvd ds).trans (Nat.factorial_dvd_factorial (by omega))

lemma commonMultiplier_mul (ds : List ℕ) (H : ℕ) :
    commonMultiplier ds H * factorialProduct ds = (H + ds.sum).factorial :=
  Nat.div_mul_cancel (factorialProduct_dvd_shift ds H)

lemma commonMultiplier_pos (ds : List ℕ) (H : ℕ) :
    0 < commonMultiplier ds H := by
  have h := commonMultiplier_mul ds H
  have hp := Nat.factorial_pos (H + ds.sum)
  by_contra hn
  have hz : commonMultiplier ds H = 0 := by omega
  rw [hz, zero_mul] at h
  omega

lemma factorialProduct_cast (ds : List ℕ) :
    (factorialProduct ds : ℝ) = (ds.map (fun d => (d.factorial : ℝ))).prod := by
  simp [factorialProduct, Nat.cast_list_prod, List.map_map, Function.comp_def]

/-- One natural multiplier clears every boundary in a finite shift window. -/
theorem commonMultiplier_integral (ds : List ℕ) (r : ℕ → ℝ)
    (hr : ∀ n, ∃ z : ℤ, (n.factorial : ℝ) * r n = z)
    (H n : ℕ) (hn : n ≤ H) :
    ∃ z : ℤ, (commonMultiplier ds H : ℝ) * rawApply ds r n = z := by
  obtain ⟨z, hz⟩ := applyShifts_integral ds r 0 0 (by simpa using hr) n (by omega)
  simp only [Nat.add_zero] at hz
  have hd : (n + ds.sum).factorial ∣ (H + ds.sum).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  obtain ⟨a, ha⟩ := hd
  refine ⟨(a : ℤ) * z, ?_⟩
  rw [rawApply_eq, ← factorialProduct_cast, ← mul_assoc]
  have hm : (commonMultiplier ds H : ℝ) * (factorialProduct ds : ℝ) =
      ((H + ds.sum).factorial : ℝ) := by
    exact_mod_cast commonMultiplier_mul ds H
  rw [hm, ha]
  push_cast
  rw [mul_right_comm, hz]
  ring

lemma prefixQ_factorial_integral (n : ℕ) :
    ∃ z : ℤ, (n.factorial : ℝ) * (prefixQ n : ℝ) = z := by
  refine ⟨∑ k ∈ range (n + 1), (lambertCoeff k : ℤ) * (n.factorial / k.factorial : ℕ), ?_⟩
  simp only [prefixQ, Rat.cast_sum, Rat.cast_div, Rat.cast_natCast,
    mul_sum, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply sum_congr rfl
  intro k hk
  rw [Nat.cast_div_charZero (Nat.factorial_dvd_factorial (by
    have := mem_range.mp hk
    omega))]
  ring

theorem commonMultiplier_boundary_integral (ds : List ℕ) (H n : ℕ) (hn : n ≤ H) :
    ∃ z : ℤ, (commonMultiplier ds H : ℝ) *
      rawApply ds (fun n => (prefixQ n : ℝ)) n = z :=
  commonMultiplier_integral ds _ prefixQ_factorial_integral H n hn

/-- The same raw operator over the rationals. -/
def rawApplyQ : List ℕ → (ℕ → ℚ) → (ℕ → ℚ)
  | [], r => r
  | d :: ds, r => rawApplyQ ds (fun n => (d.factorial : ℚ) * r (n + d) - r n)

lemma cast_rawApplyQ (ds : List ℕ) (r : ℕ → ℚ) (n : ℕ) :
    (rawApplyQ ds r n : ℝ) = rawApply ds (fun n => (r n : ℝ)) n := by
  induction ds generalizing r with
  | nil => rfl
  | cons d ds ih =>
    simp only [rawApplyQ, rawApply, ih, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast]
    rfl

def boundary (ds : List ℕ) (n : ℕ) : ℚ := rawApplyQ ds prefixQ n

lemma boundary_cast (ds : List ℕ) (n : ℕ) :
    (boundary ds n : ℝ) = rawApply ds (fun n => (prefixQ n : ℝ)) n :=
  cast_rawApplyQ ds prefixQ n

lemma rational_den_dvd_of_integral_mul (x : ℚ) (C : ℕ) (hC : 0 < C)
    (h : ∃ z : ℤ, (C : ℝ) * (x : ℝ) = z) : x.den ∣ C := by
  obtain ⟨z, hz⟩ := h
  have hq : (C : ℚ) * x = z := by exact_mod_cast hz
  have he : x = Rat.divInt z C := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
    apply (eq_div_iff (by exact_mod_cast hC.ne' : (C : ℚ) ≠ 0)).mpr
    rwa [mul_comm]
  rw [he]
  exact_mod_cast Rat.den_dvd z (C : ℤ)

/-- The reduced denominator of each shifted boundary divides the same
factorial quotient, rather than merely the full final factorial. -/
theorem boundary_den_dvd (ds : List ℕ) (H n : ℕ) (hn : n ≤ H) :
    (boundary ds n).den ∣ commonMultiplier ds H := by
  apply rational_den_dvd_of_integral_mul _ _ (commonMultiplier_pos ds H)
  rw [boundary_cast]
  exact commonMultiplier_boundary_integral ds H n hn

/-- Consequently the least common denominator of an arbitrary finite
window also divides that factorial quotient. -/
theorem boundary_lcm_dvd (ds : List ℕ) (s : Finset ℕ) (H : ℕ)
    (hs : ∀ n ∈ s, n ≤ H) :
    s.lcm (fun n => (boundary ds n).den) ∣ commonMultiplier ds H := by
  apply Finset.lcm_dvd
  intro n hn
  exact boundary_den_dvd ds H n (hs n hn)

end LambertBoundaryClearing

#print axioms LambertBoundaryClearing.commonMultiplier_integral
#print axioms LambertBoundaryClearing.commonMultiplier_boundary_integral

#print axioms LambertBoundaryClearing.boundary_lcm_dvd
