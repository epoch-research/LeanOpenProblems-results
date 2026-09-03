import Submission.AbelHarmonicSkewKernel

/-! Finite Fourier bounds for antisymmetric shift correlations. A finite positive
shift kernel with uniformly small imaginary multiplier cancels these correlations
on every finite ring with a primitive additive character. -/
namespace Erdos371.SkewKernel
open Finset
variable {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]

noncomputable def fourierCoeff (ψ : AddChar F ℂ) (f : F → ℂ) (a : F) : ℂ :=
  (∑ x, f x*ψ (-(a*x)))/(Fintype.card F : ℂ)

omit [DecidableEq F] in
lemma ring_card_complex_ne_zero : (Fintype.card F : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

lemma fourier_inversion (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (f : F → ℂ) (x : F) :
    (∑ a, fourierCoeff ψ f a * ψ (a*x)) = f x := by
  simp only [fourierCoeff, div_mul_eq_mul_div, sum_mul, ← sum_div]
  have he (a y : F) : f y*ψ (-(a*y))*ψ (a*x)=f y*ψ (a*(x-y)) := by
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [he]
  rw [sum_comm]
  simp only [← mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero]
  simp only [Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
  exact mul_div_cancel_right₀ (f x) ring_card_complex_ne_zero

lemma fourier_bilinear_parseval (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (f g : F → ℂ) :
    (∑ a, fourierCoeff ψ f a*fourierCoeff ψ g (-a)) =
      (∑ x, f x*g x)/(Fintype.card F : ℂ) := by
  simp_rw [show ∀ a : F, fourierCoeff ψ g (-a) =
    (∑ x, g x*ψ (-((-a)*x)))/(Fintype.card F : ℂ) from fun a => rfl]
  simp only [neg_mul, neg_neg, ← mul_div_assoc, mul_sum, ← sum_div]
  rw [sum_comm]
  have he (x : F) : (∑ a, fourierCoeff ψ f a*(g x*ψ (a*x))) = g x*f x := by
    calc
      _ = g x*(∑ a, fourierCoeff ψ f a*ψ (a*x)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [fourier_inversion ψ hψ]
  simp_rw [he, mul_comm]

omit [DecidableEq F] in
lemma fourierCoeff_conj_neg (ψ : AddChar F ℂ) (f : F → ℂ) (a : F) :
    fourierCoeff ψ (fun x => (starRingEnd ℂ) (f x)) (-a) =
      (starRingEnd ℂ) (fourierCoeff ψ f a) := by
  unfold fourierCoeff
  simp only [map_div₀, map_sum, map_mul, map_natCast, neg_mul, neg_neg,
    ← AddChar.map_neg_eq_conj]

lemma fourier_parseval (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (f : F → ℂ) :
    (∑ a, ‖fourierCoeff ψ f a‖^2) =
      (∑ x, ‖f x‖^2)/(Fintype.card F : ℝ) := by
  have h := fourier_bilinear_parseval ψ hψ f (fun x => (starRingEnd ℂ) (f x))
  simp_rw [fourierCoeff_conj_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

omit [DecidableEq F] in
lemma fourierCoeff_shift (ψ : AddChar F ℂ) (f : F → ℂ) (h a : F) :
    fourierCoeff ψ (fun x => f (x+h)) a = fourierCoeff ψ f a * ψ (a*h) := by
  unfold fourierCoeff
  rw [div_mul_eq_mul_div, sum_mul]
  congr 1
  apply Fintype.sum_equiv (Equiv.addRight h)
  intro x
  change f (x+h)*ψ (-(a*x)) = f (x+h)*ψ (-(a*(x+h)))*ψ (a*h)
  rw [mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

noncomputable def shiftCorrelation (f g : F → ℂ) (h : F) : ℂ :=
  (∑ x, f x*g (x+h))/(Fintype.card F : ℂ)

lemma shiftCorrelation_fourier (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (f g : F → ℂ) (h : F) :
    shiftCorrelation f g h = ∑ a, fourierCoeff ψ f a*fourierCoeff ψ g (-a)*ψ (-(a*h)) := by
  rw [shiftCorrelation, ← fourier_bilinear_parseval ψ hψ f (fun x => g (x+h))]
  simp_rw [fourierCoeff_shift, neg_mul, mul_assoc]

omit [DecidableEq F] in
lemma shiftCorrelation_swap (f g : F → ℂ) (h : F) :
    shiftCorrelation g f h = shiftCorrelation f g (-h) := by
  unfold shiftCorrelation
  congr 1
  apply Fintype.sum_equiv (Equiv.addRight h)
  intro x
  simp [mul_comm]

noncomputable def shiftPolynomial (H : ℕ) (w : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ range H, (w k : ℂ)*z^k

lemma shiftPolynomial_conj (H : ℕ) (w : ℕ → ℝ) (z : ℂ) :
    shiftPolynomial H w ((starRingEnd ℂ) z) = (starRingEnd ℂ) (shiftPolynomial H w z) := by
  simp [shiftPolynomial]

lemma shiftPolynomial_conj_difference (H : ℕ) (w : ℕ → ℝ) (z : ℂ) :
    ‖shiftPolynomial H w z - shiftPolynomial H w ((starRingEnd ℂ) z)‖ =
      2*|(shiftPolynomial H w z).im| := by
  rw [shiftPolynomial_conj]
  have he : shiftPolynomial H w z - (starRingEnd ℂ) (shiftPolynomial H w z) =
      (2*(shiftPolynomial H w z).im : ℝ)*Complex.I := by
    apply Complex.ext <;> simp
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

lemma weighted_shiftCorrelation_fourier (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (f g : F → ℂ) (h : F) (H : ℕ) (w : ℕ → ℝ) :
    (∑ k ∈ range H, (w k : ℂ)*shiftCorrelation f g ((k : F)*h)) =
      ∑ a, fourierCoeff ψ f a*fourierCoeff ψ g (-a)*shiftPolynomial H w (ψ ((-a)*h)) := by
  simp_rw [shiftCorrelation_fourier ψ hψ, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  unfold shiftPolynomial
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  have he : ψ (-(a*((k : F)*h))) = (ψ ((-a)*h))^k := by
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  rw [he]
  ring

/-- A uniform bound on the imaginary multiplier controls every antisymmetric
bilinear correlation. No estimate for prime exponential sums is used. -/
theorem weighted_skewCorrelation_sq_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (f g : F → ℂ) (h : F) (H : ℕ) (w : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hw : ∀ z : ℂ, ‖z‖ ≤ 1 → |(shiftPolynomial H w z).im| ≤ ε) :
    ‖∑ k ∈ range H, (w k : ℂ)*(shiftCorrelation f g ((k : F)*h)-shiftCorrelation g f ((k : F)*h))‖^2 ≤
      4*ε^2*((∑ x, ‖f x‖^2)/(Fintype.card F : ℝ))*
        ((∑ x, ‖g x‖^2)/(Fintype.card F : ℝ)) := by
  let cf := fourierCoeff ψ f
  let cg := fourierCoeff ψ g
  have he : (∑ k ∈ range H, (w k : ℂ)*
      (shiftCorrelation f g ((k : F)*h)-shiftCorrelation g f ((k : F)*h))) =
        ∑ a, cf a*cg (-a)*(shiftPolynomial H w (ψ ((-a)*h))-shiftPolynomial H w (ψ (a*h))) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [weighted_shiftCorrelation_fourier ψ hψ, weighted_shiftCorrelation_fourier ψ hψ]
    have hs : (∑ a, fourierCoeff ψ g a*fourierCoeff ψ f (-a)*shiftPolynomial H w (ψ ((-a)*h))) =
        ∑ a, cf a*cg (-a)*shiftPolynomial H w (ψ (a*h)) := by
      apply Fintype.sum_equiv (Equiv.neg F)
      intro a
      simp only [Equiv.neg_apply, neg_neg, cf, cg]
      ring
    rw [hs, ← sum_sub_distrib]
  rw [he]
  have hb : ‖∑ a, cf a*cg (-a)*(shiftPolynomial H w (ψ ((-a)*h))-shiftPolynomial H w (ψ (a*h)))‖ ≤
      2*ε*(∑ a, ‖cf a‖*‖cg (-a)‖) := by
    calc
      _ ≤ ∑ a, ‖cf a*cg (-a)*(shiftPolynomial H w (ψ ((-a)*h))-shiftPolynomial H w (ψ (a*h)))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a, 2*ε*(‖cf a‖*‖cg (-a)‖) := by
        apply sum_le_sum
        intro a _
        have hc : ψ (a*h) = (starRingEnd ℂ) (ψ ((-a)*h)) := by
          rw [← AddChar.map_neg_eq_conj, neg_mul, neg_neg]
        rw [hc, norm_mul, norm_mul, shiftPolynomial_conj_difference]
        have hi := hw (ψ ((-a)*h)) (by rw [ψ.norm_apply])
        nlinarith [mul_nonneg (norm_nonneg (cf a)) (norm_nonneg (cg (-a)))]
      _ = _ := (mul_sum ..).symm
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset F)
    (fun a => ‖cf a‖) (fun a => ‖cg (-a)‖)
  have hneg : (∑ a, ‖cg (-a)‖^2) = ∑ a, ‖cg a‖^2 :=
    Fintype.sum_equiv (Equiv.neg F) _ _ (fun _ => rfl)
  rw [hneg] at hcs
  have hp := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 4*ε^2)
  have hsq := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hb
  rw [mul_pow] at hsq
  have hf := fourier_parseval ψ hψ f
  have hg := fourier_parseval ψ hψ g
  change (∑ a, ‖cf a‖^2) = _ at hf
  change (∑ a, ‖cg a‖^2) = _ at hg
  rw [hf,hg] at hp
  nlinarith

#print axioms weighted_skewCorrelation_sq_le
end Erdos371.SkewKernel
