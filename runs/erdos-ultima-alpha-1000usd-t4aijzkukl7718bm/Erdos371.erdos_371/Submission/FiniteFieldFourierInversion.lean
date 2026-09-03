import Submission.KloostermanFourierTests

/-! Fourier inversion, Parseval, and convolution over a finite field. These
are tools for applying the inverse-curve estimate to smoothed interval tests. -/
namespace Erdos371.Kloosterman
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def fourierCoeff (ψ : AddChar F ℂ) (f : F → ℂ) (a : F) : ℂ :=
  (∑ x : F, f x*ψ (-(a*x)))/(Fintype.card F : ℂ)

omit [DecidableEq F] in
lemma field_card_complex_ne_zero : (Fintype.card F : ℂ)≠0 := by
  exact_mod_cast Fintype.card_ne_zero

omit [DecidableEq F] in
lemma fourierCoeff_zero (ψ : AddChar F ℂ) (f : F → ℂ) :
    fourierCoeff ψ f 0=(∑ x : F, f x)/(Fintype.card F : ℂ) := by
  simp [fourierCoeff]

/-- Exact finite Fourier inversion, including its normalization. -/
theorem fourier_inversion (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (f : F → ℂ) (x : F) :
    fourierPolynomial ψ (fourierCoeff ψ f) x=f x := by
  unfold fourierPolynomial
  simp only [fourierCoeff,div_mul_eq_mul_div,sum_mul,← sum_div]
  have he (a y : F) : f y*ψ (-(a*y))*ψ (a*x)=f y*ψ (a*(x-y)) := by
    rw [mul_assoc,← AddChar.map_add_eq_mul]
    congr 2; ring
  simp_rw [he]
  rw [sum_comm]
  simp only [← mul_sum,AddChar.sum_mulShift _ hψ,sub_eq_zero]
  simp only [Nat.cast_ite,Nat.cast_zero,mul_ite,mul_zero,sum_ite_eq,mem_univ,if_true]
  exact mul_div_cancel_right₀ (f x) field_card_complex_ne_zero

/-- A bilinear form of Parseval is convenient before introducing conjugates. -/
lemma fourier_bilinear_parseval (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (f g : F → ℂ) :
    (∑ a : F, fourierCoeff ψ f a*fourierCoeff ψ g (-a)) =
      (∑ x : F, f x*g x)/(Fintype.card F : ℂ) := by
  simp_rw [show ∀ a : F, fourierCoeff ψ g (-a)=
    (∑ x : F, g x*ψ (-((-a)*x)))/(Fintype.card F : ℂ) from fun a => rfl]
  simp only [neg_mul,neg_neg,← mul_div_assoc,mul_sum,← sum_div]
  rw [sum_comm]
  have he (x : F) : (∑ a : F, fourierCoeff ψ f a*(g x*ψ (a*x))) = g x*f x := by
    calc
      _ = g x*fourierPolynomial ψ (fourierCoeff ψ f) x := by
        simp only [fourierPolynomial,mul_sum]; apply sum_congr rfl; intro a ha; ring
      _ = _ := by rw [fourier_inversion ψ hψ]
  simp_rw [he,mul_comm]

omit [DecidableEq F] in
lemma fourierCoeff_conj_neg (ψ : AddChar F ℂ) (f : F → ℂ) (a : F) :
    fourierCoeff ψ (fun x => (starRingEnd ℂ) (f x)) (-a) =
      (starRingEnd ℂ) (fourierCoeff ψ f a) := by
  unfold fourierCoeff
  simp only [map_div₀,map_sum,map_mul,map_natCast,neg_mul,neg_neg,
    ← AddChar.map_neg_eq_conj]

/-- Parseval in real norm-square form. -/
theorem fourier_parseval (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (f : F → ℂ) :
    (∑ a : F, ‖fourierCoeff ψ f a‖^2) =
      (∑ x : F, ‖f x‖^2)/(Fintype.card F : ℝ) := by
  have h := fourier_bilinear_parseval ψ hψ f (fun x => (starRingEnd ℂ) (f x))
  simp_rw [fourierCoeff_conj_neg,Complex.mul_conj,Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

noncomputable def finiteConvolution (f g : F → ℂ) (x : F) : ℂ :=
  ∑ y : F, f y*g (x-y)

omit [DecidableEq F] in
lemma fourierCoeff_convolution (ψ : AddChar F ℂ) (f g : F → ℂ) (a : F) :
    fourierCoeff ψ (finiteConvolution f g) a=
      (Fintype.card F : ℂ)*fourierCoeff ψ f a*fourierCoeff ψ g a := by
  unfold fourierCoeff finiteConvolution
  simp only [sum_mul]
  rw [sum_comm]
  have he (y : F) : (∑ x : F, (f y*g (x-y))*ψ (-(a*x))) =
      f y*ψ (-(a*y))*(∑ z : F, g z*ψ (-(a*z))) := by
    rw [mul_sum]
    apply Fintype.sum_equiv (Equiv.subRight y)
    intro x
    change (f y*g (x-y))*ψ (-(a*x)) = f y*ψ (-(a*y))*(g (x-y)*ψ (-(a*(x-y))))
    have hh : ψ (-(a*x))=ψ (-(a*y))*ψ (-(a*(x-y))) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [hh]; ring
  simp_rw [he,← sum_mul]
  field_simp [field_card_complex_ne_zero]

noncomputable def setIndicator (A : Finset F) (x : F) : ℂ := if x∈A then 1 else 0

omit [Field F] in
lemma setIndicator_sum (A : Finset F) : (∑ x : F, setIndicator A x)=(A.card : ℂ) := by
  simp [setIndicator]

omit [Field F] in
lemma setIndicator_sq_norm_sum (A : Finset F) : (∑ x : F, ‖setIndicator A x‖^2)=(A.card : ℝ) := by
  simp [setIndicator,apply_ite]

lemma fourierCoeff_indicator_parseval (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (A : Finset F) :
    (∑ a : F, ‖fourierCoeff ψ (setIndicator A) a‖^2)=(A.card : ℝ)/(Fintype.card F : ℝ) := by
  rw [fourier_parseval ψ hψ,setIndicator_sq_norm_sum]

noncomputable def smoothedIndicator (A J : Finset F) (x : F) : ℂ :=
  finiteConvolution (setIndicator J) (setIndicator A) x/(J.card : ℂ)

omit [DecidableEq F] in
lemma fourierCoeff_div (ψ : AddChar F ℂ) (f : F → ℂ) (c : ℂ) (a : F) :
    fourierCoeff ψ (fun x => f x/c) a=fourierCoeff ψ f a/c := by
  unfold fourierCoeff
  simp only [div_mul_eq_mul_div,← sum_div]
  ring

lemma smoothedIndicator_coeff (ψ : AddChar F ℂ) (A J : Finset F) (a : F) :
    fourierCoeff ψ (smoothedIndicator A J) a=
      ((Fintype.card F : ℂ)/(J.card : ℂ))*
        fourierCoeff ψ (setIndicator J) a*fourierCoeff ψ (setIndicator A) a := by
  unfold smoothedIndicator
  rw [fourierCoeff_div,fourierCoeff_convolution]
  ring

/-- Smoothing gives a useful L1 Fourier bound without estimating a geometric
sum: it follows from Parseval and Cauchy--Schwarz. -/
theorem smoothedIndicator_fourier_l1_sq (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (A J : Finset F) (hJ : J.Nonempty) :
    (∑ a : F, ‖fourierCoeff ψ (smoothedIndicator A J) a‖)^2≤(A.card : ℝ)/J.card := by
  have hq : (0 : ℝ)<Fintype.card F := by exact_mod_cast (Fintype.card_pos (α := F))
  have hj : (0 : ℝ)<J.card := by exact_mod_cast hJ.card_pos
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset F)
    (fun a => ‖fourierCoeff ψ (setIndicator J) a‖)
    (fun a => ‖fourierCoeff ψ (setIndicator A) a‖)
  rw [fourierCoeff_indicator_parseval ψ hψ,fourierCoeff_indicator_parseval ψ hψ] at h
  have he : (∑ a : F, ‖fourierCoeff ψ (smoothedIndicator A J) a‖) =
      ((Fintype.card F : ℝ)/J.card)*(∑ a : F,
        ‖fourierCoeff ψ (setIndicator J) a‖*‖fourierCoeff ψ (setIndicator A) a‖) := by
    simp only [smoothedIndicator_coeff,norm_mul,norm_div,Complex.norm_natCast,mul_sum,mul_assoc]
  rw [he,mul_pow]
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq
  field_simp

#print axioms fourier_inversion
#print axioms fourier_parseval
#print axioms fourierCoeff_convolution
#print axioms smoothedIndicator_fourier_l1_sq
end Erdos371.Kloosterman
