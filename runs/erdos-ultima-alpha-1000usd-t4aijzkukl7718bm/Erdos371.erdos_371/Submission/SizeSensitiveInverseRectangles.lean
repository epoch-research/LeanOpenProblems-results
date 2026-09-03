import Submission.SignedInverseRectangles

/-! Size-sensitive modular-inverse rectangle bounds. Unlike the earlier
uniform rectangle bound, these retain the cardinalities of both tests.
They do not estimate a sum over prime moduli or the smooth-cutoff skew. -/
namespace Erdos371.Kloosterman
open Finset

section Field
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma smoothedIndicator_fourier_product_size_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A B J : Finset F) (hJ : J.Nonempty) :
    (∑ a : F, ‖fourierCoeff ψ (smoothedIndicator A J) a‖) *
      (∑ b : F, ‖fourierCoeff ψ (smoothedIndicator B J) b‖) ≤
        Real.sqrt ((A.card : ℝ) * B.card) / J.card := by
  have hA := Real.le_sqrt_of_sq_le (smoothedIndicator_fourier_l1_sq ψ hψ A J hJ)
  have hB := Real.le_sqrt_of_sq_le (smoothedIndicator_fourier_l1_sq ψ hψ B J hJ)
  have h := mul_le_mul hA hB (sum_nonneg fun b _ => norm_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.sqrt_div (Nat.cast_nonneg A.card), Real.sqrt_div (Nat.cast_nonneg B.card),
    div_mul_div_comm, ← Real.sqrt_mul (Nat.cast_nonneg A.card),
    Real.mul_self_sqrt (Nat.cast_nonneg J.card)] at h
  exact h

lemma smoothed_rectangle_size_error (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A B J : Finset F) (hJ : J.Nonempty) :
    ‖(∑ x : Fˣ, smoothedIndicator A J (x:F) * smoothedIndicator B J (x:F)⁻¹) -
      (Fintype.card Fˣ : ℂ) * ((A.card : ℂ)/Fintype.card F) *
        ((B.card : ℂ)/Fintype.card F)‖ / Fintype.card F ≤
      Real.sqrt (Real.sqrt (3/(Fintype.card F : ℝ))) *
        (Real.sqrt ((A.card : ℝ) * B.card) / J.card) := by
  have h := inverseCorrelation_normalized_error_bound ψ hψ
    (fourierCoeff ψ (smoothedIndicator A J)) (fourierCoeff ψ (smoothedIndicator B J))
  simp only [inverseCorrelation, fourier_inversion ψ hψ, smoothedIndicator_mean ψ _ J hJ] at h
  apply h.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (smoothedIndicator_fourier_product_size_le ψ hψ A B J hJ) (by positivity)

/-- Smoothing retains the geometric mean of the two set cardinalities. -/
theorem inverseRectangleCount_size_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A B J : Finset F) (hJ : J.Nonempty) :
    |(inverseRectangleCount A B : ℝ) - (Fintype.card Fˣ : ℝ) *
      ((A.card : ℝ)/Fintype.card F) * ((B.card : ℝ)/Fintype.card F)| / Fintype.card F ≤
      (smoothingError A J + smoothingError B J)/Fintype.card F +
        Real.sqrt (Real.sqrt (3/(Fintype.card F : ℝ))) *
          (Real.sqrt ((A.card : ℝ) * B.card) / J.card) := by
  have hraw := inverse_rectangle_smoothing_error A B J hJ
  have hsm := smoothed_rectangle_size_error ψ hψ A B J hJ
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (∑ x : Fˣ, setIndicator A (x:F) * setIndicator B (x:F)⁻¹)
    (∑ x : Fˣ, smoothedIndicator A J (x:F) * smoothedIndicator B J (x:F)⁻¹)
    ((Fintype.card Fˣ : ℂ) * ((A.card : ℂ)/Fintype.card F) * ((B.card : ℂ)/Fintype.card F))
  have h := div_le_div_of_nonneg_right htri (Nat.cast_nonneg (α := ℝ) (Fintype.card F))
  rw [add_div] at h
  have hb := h.trans (add_le_add (div_le_div_of_nonneg_right hraw (Nat.cast_nonneg _)) hsm)
  rw [← inverseRectangleCount_eq] at hb
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hb
end Field

section Prime
variable (p : ℕ) [Fact p.Prime]

/-- The previous cost p/H can be replaced by sqrt(L*M)/H. -/
theorem signed_rectangle_size_bound (s : Bool) (L M H : ℕ) (hL : L ≤ p) (hM : M ≤ p)
    (hH : 0 < H) (hHp : H ≤ p) :
    signedIntervalDiscrepancy p s L M ≤
      4*(H : ℝ)/p + Real.sqrt (Real.sqrt (3/(p : ℝ))) * (Real.sqrt ((L : ℝ)*M)/H) := by
  have h := inverseRectangleCount_size_bound ZMod.stdAddChar
    (ZMod.isPrimitive_stdAddChar p) (residueInterval p L) (orientedInterval p s M)
    (residueInterval p H) (residueInterval_nonempty p H hH)
  simp only [ZMod.card, ZMod.card_units, residueInterval_card p L hL,
    orientedInterval_card p s M hM, residueInterval_card p H hHp] at h
  apply h.trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
  have h1 := residueInterval_smoothingError p L H hH hHp
  have h2 := orientedInterval_smoothingError p s M H hH hHp
  linarith

/-- Both signs have the same main term, so it cancels exactly. -/
theorem signed_rectangle_difference_size_bound (L M H : ℕ) (hL : L ≤ p) (hM : M ≤ p)
    (hH : 0 < H) (hHp : H ≤ p) :
    |(signedRectangleCount p true L M : ℝ) - signedRectangleCount p false L M|/p ≤
      8*(H : ℝ)/p + 2*Real.sqrt (Real.sqrt (3/(p : ℝ))) * (Real.sqrt ((L : ℝ)*M)/H) := by
  have ht := signed_rectangle_size_bound p true L M H hL hM hH hHp
  have hf := signed_rectangle_size_bound p false L M H hL hM hH hHp
  have htri := abs_sub_le
    (signedRectangleCount p true L M : ℝ)
    ((p-1 : ℕ)*((L : ℝ)/p)*((M : ℝ)/p))
    (signedRectangleCount p false L M : ℝ)
  rw [abs_sub_comm ((p-1 : ℕ)*((L : ℝ)/p)*((M : ℝ)/p))] at htri
  have h := div_le_div_of_nonneg_right htri (Nat.cast_nonneg (α := ℝ) p)
  rw [add_div] at h
  change _ ≤ signedIntervalDiscrepancy p true L M + signedIntervalDiscrepancy p false L M at h
  apply (h.trans (add_le_add ht hf)).trans_eq
  ring

/-- An explicit optimized bound, including the integer rounding error.
Its scale is p^(3/8)*(L*M)^(1/4), not the expected count L*M/p. -/
theorem signed_rectangle_difference_optimized (L M : ℕ) (hp3 : 3 ≤ p)
    (hL : L ≤ p) (hM : M ≤ p) :
    |(signedRectangleCount p true L M : ℝ) - signedRectangleCount p false L M| ≤
      10*Real.sqrt ((p : ℝ)*Real.sqrt (Real.sqrt (3/(p : ℝ))) *
        Real.sqrt ((L : ℝ)*M)) + 8 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  let η : ℝ := Real.sqrt (Real.sqrt (3/(p : ℝ)))
  let z : ℝ := Real.sqrt ((p : ℝ)*η*Real.sqrt ((L : ℝ)*M))
  have hη0 : 0 ≤ η := Real.sqrt_nonneg _
  have hη1 : η ≤ 1 := by
    have h3 : (3 : ℝ)/p ≤ 1 := (div_le_one hp0).mpr (by exact_mod_cast hp3)
    have h := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h3)
    simpa only [Real.sqrt_one] using h
  have hroot : Real.sqrt ((L : ℝ)*M) ≤ p := by
    have hL' : (L : ℝ) ≤ p := by exact_mod_cast hL
    have hM' : (M : ℝ) ≤ p := by exact_mod_cast hM
    have hprod : (L : ℝ)*M ≤ (p : ℝ)^2 := by
      nlinarith [mul_le_mul hL' hM' (Nat.cast_nonneg (α := ℝ) M) hp0.le]
    simpa only [Real.sqrt_sq hp0.le] using Real.sqrt_le_sqrt hprod
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzs : z^2 = (p : ℝ)*η*Real.sqrt ((L : ℝ)*M) := Real.sq_sqrt (by positivity)
  have hzp : z ≤ p := by
    have hprod : (p : ℝ)*η*Real.sqrt ((L : ℝ)*M) ≤ (p : ℝ)^2 := by
      calc
        _ ≤ (p : ℝ)*Real.sqrt ((L : ℝ)*M) := by
          exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hp0.le hη1)
            (Real.sqrt_nonneg _)
        _ ≤ (p : ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_left hroot hp0.le]
    nlinarith
  let H : ℕ := max 1 ⌈z⌉₊
  have hH : 0 < H := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hHp : H ≤ p := max_le (by omega) (Nat.ceil_le.mpr hzp)
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hzH : z ≤ H := (Nat.le_ceil z).trans (by exact_mod_cast le_max_right 1 ⌈z⌉₊)
  have hHsmall : (H : ℝ) ≤ z+1 := by
    dsimp [H]
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (Nat.ceil_lt_add_one hz0).le
  have hratio : (p : ℝ)*η*Real.sqrt ((L : ℝ)*M)/(H : ℝ) ≤ z := by
    apply (div_le_iff₀ hHr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hzH hz0]
  have hb := signed_rectangle_difference_size_bound p L M H hL hM hH hHp
  have hb' := (div_le_iff₀ hp0).mp hb
  change _ ≤ (8*(H : ℝ)/p + 2*η*(Real.sqrt ((L : ℝ)*M)/H)) * p at hb'
  have he : (8*(H : ℝ)/p + 2*η*(Real.sqrt ((L : ℝ)*M)/H)) * p =
      8*(H : ℝ) + 2*((p : ℝ)*η*Real.sqrt ((L : ℝ)*M)/H) := by
    field_simp
  rw [he] at hb'
  change _ ≤ 10*z+8
  linarith

end Prime

#print axioms inverseRectangleCount_size_bound
#print axioms signed_rectangle_size_bound
#print axioms signed_rectangle_difference_size_bound
#print axioms signed_rectangle_difference_optimized
end Erdos371.Kloosterman
