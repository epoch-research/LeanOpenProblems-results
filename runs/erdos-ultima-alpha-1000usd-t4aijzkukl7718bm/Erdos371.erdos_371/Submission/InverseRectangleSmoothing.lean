import Submission.FiniteFieldFourierInversion

/-! Smoothing bounds for modular-inverse rectangle counts. The errors are
explicit translation L1 errors, not unproved equidistribution assumptions. -/
namespace Erdos371.Kloosterman
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] in
lemma setIndicator_norm_le_one (A : Finset F) (x : F) : ‖setIndicator A x‖≤1 := by
  unfold setIndicator
  split_ifs <;> norm_num

lemma smoothedIndicator_expand (A J : Finset F) (x : F) :
    smoothedIndicator A J x=(∑ y ∈ J, setIndicator A (x-y))/(J.card : ℂ) := by
  unfold smoothedIndicator finiteConvolution
  congr 1
  have ht (y : F) : setIndicator J y*setIndicator A (x-y)=
      if y∈J then setIndicator A (x-y) else 0 := by
    by_cases hy : y∈J <;> simp [setIndicator,hy]
  simp_rw [ht]
  simp

lemma smoothedIndicator_norm_le_one (A J : Finset F) (hJ : J.Nonempty) (x : F) :
    ‖smoothedIndicator A J x‖≤1 := by
  rw [smoothedIndicator_expand,norm_div,Complex.norm_natCast]
  have hj : (0 : ℝ)<J.card := by exact_mod_cast hJ.card_pos
  apply (div_le_iff₀ hj).mpr
  calc
    _ ≤ ∑ y ∈ J, ‖setIndicator A (x-y)‖ := norm_sum_le _ _
    _ ≤ ∑ _y ∈ J, (1 : ℝ) := sum_le_sum fun y _ => setIndicator_norm_le_one A (x-y)
    _ = _ := by simp

lemma smoothedIndicator_mean (ψ : AddChar F ℂ) (A J : Finset F) (hJ : J.Nonempty) :
    fourierCoeff ψ (smoothedIndicator A J) 0=(A.card : ℂ)/(Fintype.card F : ℂ) := by
  rw [smoothedIndicator_coeff,fourierCoeff_zero,fourierCoeff_zero,setIndicator_sum,setIndicator_sum]
  have hj : (J.card : ℂ)≠0 := by exact_mod_cast hJ.card_pos.ne'
  field_simp [field_card_complex_ne_zero,hj]

lemma smoothedIndicator_fourier_product_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A B J : Finset F) (hJ : J.Nonempty) :
    (∑ a : F, ‖fourierCoeff ψ (smoothedIndicator A J) a‖)*
      (∑ b : F, ‖fourierCoeff ψ (smoothedIndicator B J) b‖)≤
        (Fintype.card F : ℝ)/J.card := by
  have hbound (S : Finset F) : (∑ a : F, ‖fourierCoeff ψ (smoothedIndicator S J) a‖) ≤
      Real.sqrt ((Fintype.card F : ℝ)/J.card) := by
    apply Real.le_sqrt_of_sq_le
    apply (smoothedIndicator_fourier_l1_sq ψ hψ S J hJ).trans
    exact div_le_div_of_nonneg_right (by exact_mod_cast S.card_le_univ) (Nat.cast_nonneg _)
  have h := mul_le_mul (hbound A) (hbound B) (sum_nonneg fun a _ => norm_nonneg _) (Real.sqrt_nonneg _)
  rwa [Real.mul_self_sqrt (by positivity)] at h

/-- The smoothed correlation has a power-saving error with explicit cost q/|J|. -/
lemma smoothed_rectangle_normalized_error (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A B J : Finset F) (hJ : J.Nonempty) :
    ‖(∑ x : Fˣ, smoothedIndicator A J (x:F)*smoothedIndicator B J (x:F)⁻¹)-
      (Fintype.card Fˣ : ℂ)*((A.card : ℂ)/Fintype.card F)*((B.card : ℂ)/Fintype.card F)‖ /
        Fintype.card F ≤
    Real.sqrt (Real.sqrt (3/(Fintype.card F : ℝ)))*((Fintype.card F : ℝ)/J.card) := by
  have h := inverseCorrelation_normalized_error_bound ψ hψ
    (fourierCoeff ψ (smoothedIndicator A J)) (fourierCoeff ψ (smoothedIndicator B J))
  simp only [inverseCorrelation,fourier_inversion ψ hψ,smoothedIndicator_mean ψ _ J hJ] at h
  apply h.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (smoothedIndicator_fourier_product_le ψ hψ A B J hJ) (by positivity)

noncomputable def translationError (A : Finset F) (y : F) : ℝ :=
  ∑ x : F, ‖setIndicator A x-setIndicator A (x-y)‖

noncomputable def smoothingError (A J : Finset F) : ℝ :=
  (∑ y ∈ J, translationError A y)/(J.card : ℝ)

lemma smoothedIndicator_point_error (A J : Finset F) (hJ : J.Nonempty) (x : F) :
    setIndicator A x-smoothedIndicator A J x =
      (∑ y ∈ J, (setIndicator A x-setIndicator A (x-y)))/(J.card : ℂ) := by
  rw [smoothedIndicator_expand,sum_sub_distrib]
  simp only [sum_const,nsmul_eq_mul]
  have hj : (J.card : ℂ)≠0 := by exact_mod_cast hJ.card_pos.ne'
  field_simp

lemma smoothedIndicator_l1_error (A J : Finset F) (hJ : J.Nonempty) :
    (∑ x : F, ‖setIndicator A x-smoothedIndicator A J x‖)≤smoothingError A J := by
  simp_rw [smoothedIndicator_point_error A J hJ,norm_div,Complex.norm_natCast]
  unfold smoothingError translationError
  rw [sum_comm,← sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact sum_le_sum fun x _ => norm_sum_le _ _

lemma sum_units_le_univ (f : F → ℝ) (hf : ∀ x, 0≤f x) :
    (∑ x : Fˣ, f (x:F))≤∑ x : F, f x := by
  classical
  have hi : Function.Injective (fun x : Fˣ => (x:F)) := Units.val_injective
  have h := sum_le_sum_of_subset_of_nonneg (f := f)
    (show (univ.image (fun x : Fˣ => (x:F)))⊆univ from subset_univ _)
    (fun x _ _ => hf x)
  rwa [sum_image hi.injOn] at h

lemma sum_inv_units (f : F → ℝ) : (∑ x : Fˣ, f (x:F)⁻¹)=∑ x : Fˣ, f (x:F) := by
  apply Fintype.sum_equiv (Equiv.inv Fˣ)
  intro x
  change f (x:F)⁻¹=f ((x⁻¹:Fˣ):F)
  rw [Units.val_inv_eq_inv_val]

lemma bounded_product_sub (a b c d : ℂ) (hb : ‖b‖≤1) (hc : ‖c‖≤1) :
    ‖a*b-c*d‖≤‖a-c‖+‖b-d‖ := by
  calc
    _ = ‖(a-c)*b+c*(b-d)‖ := by congr 1; ring
    _ ≤ ‖(a-c)*b‖+‖c*(b-d)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) hb)
        (mul_le_of_le_one_left (norm_nonneg _) hc)

lemma inverse_rectangle_smoothing_error (A B J : Finset F) (hJ : J.Nonempty) :
    ‖(∑ x : Fˣ, setIndicator A (x:F)*setIndicator B (x:F)⁻¹)-
      (∑ x : Fˣ, smoothedIndicator A J (x:F)*smoothedIndicator B J (x:F)⁻¹)‖≤
        smoothingError A J+smoothingError B J := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ x : Fˣ, ‖setIndicator A (x:F)*setIndicator B (x:F)⁻¹-
        smoothedIndicator A J (x:F)*smoothedIndicator B J (x:F)⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ x : Fˣ, (‖setIndicator A (x:F)-smoothedIndicator A J (x:F)‖+
        ‖setIndicator B (x:F)⁻¹-smoothedIndicator B J (x:F)⁻¹‖) := by
      exact sum_le_sum fun x _ => bounded_product_sub _ _ _ _
        (setIndicator_norm_le_one B _) (smoothedIndicator_norm_le_one A J hJ _)
    _ = (∑ x : Fˣ, ‖setIndicator A (x:F)-smoothedIndicator A J (x:F)‖)+
        (∑ x : Fˣ, ‖setIndicator B (x:F)-smoothedIndicator B J (x:F)‖) := by
      rw [sum_add_distrib,sum_inv_units (fun z => ‖setIndicator B z-smoothedIndicator B J z‖)]
    _ ≤ (∑ x : F, ‖setIndicator A x-smoothedIndicator A J x‖)+
        (∑ x : F, ‖setIndicator B x-smoothedIndicator B J x‖) :=
      add_le_add (sum_units_le_univ (fun x => ‖setIndicator A x-smoothedIndicator A J x‖) (fun x => norm_nonneg _))
        (sum_units_le_univ (fun x => ‖setIndicator B x-smoothedIndicator B J x‖) (fun x => norm_nonneg _))
    _ ≤ _ := add_le_add (smoothedIndicator_l1_error A J hJ) (smoothedIndicator_l1_error B J hJ)

noncomputable def inverseRectangleCount (A B : Finset F) : ℕ :=
  (univ.filter fun x : Fˣ => (x:F)∈A ∧ (x:F)⁻¹∈B).card

lemma inverseRectangleCount_eq (A B : Finset F) :
    (inverseRectangleCount A B : ℂ) = ∑ x : Fˣ, setIndicator A (x:F)*setIndicator B (x:F)⁻¹ := by
  have ht (x : Fˣ) : setIndicator A (x:F)*setIndicator B (x:F)⁻¹ =
      if (x:F)∈A ∧ (x:F)⁻¹∈B then (1 : ℂ) else 0 := by
    unfold setIndicator; split_ifs <;> simp_all
  simp only [ht,sum_boole,inverseRectangleCount]

/-- Rectangle discrepancy with completely explicit smoothing costs. -/
theorem inverseRectangleCount_smoothing_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A B J : Finset F) (hJ : J.Nonempty) :
    |(inverseRectangleCount A B : ℝ)-(Fintype.card Fˣ : ℝ)*
      ((A.card : ℝ)/Fintype.card F)*((B.card : ℝ)/Fintype.card F)| / Fintype.card F ≤
      (smoothingError A J+smoothingError B J)/Fintype.card F+
        Real.sqrt (Real.sqrt (3/(Fintype.card F : ℝ)))*((Fintype.card F : ℝ)/J.card) := by
  have hraw := inverse_rectangle_smoothing_error A B J hJ
  have hsm := smoothed_rectangle_normalized_error ψ hψ A B J hJ
  have htri := norm_sub_le_norm_sub_add_norm_sub (∑ x : Fˣ, setIndicator A (x:F)*setIndicator B (x:F)⁻¹)
    (∑ x : Fˣ, smoothedIndicator A J (x:F)*smoothedIndicator B J (x:F)⁻¹)
    ((Fintype.card Fˣ : ℂ)*((A.card : ℂ)/Fintype.card F)*((B.card : ℂ)/Fintype.card F))
  have h := div_le_div_of_nonneg_right htri (Nat.cast_nonneg (α := ℝ) (Fintype.card F))
  rw [add_div] at h
  have hb := h.trans (add_le_add (div_le_div_of_nonneg_right hraw (Nat.cast_nonneg _)) hsm)
  rw [← inverseRectangleCount_eq] at hb
  simpa only [← Complex.ofReal_natCast,← Complex.ofReal_div,← Complex.ofReal_mul,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hb

#print axioms smoothed_rectangle_normalized_error
#print axioms smoothedIndicator_l1_error
#print axioms inverseRectangleCount_smoothing_bound
end Erdos371.Kloosterman
