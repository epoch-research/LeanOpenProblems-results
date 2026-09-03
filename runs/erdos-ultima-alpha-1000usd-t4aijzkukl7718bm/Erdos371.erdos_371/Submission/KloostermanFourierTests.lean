import Submission.KloostermanFourthMoment

/-! Finite Fourier tests for the modular inverse curve, with explicit
Fourier-coefficient costs. No uniform control of the prime-factor cutoffs
or divisor multiplicities is asserted. -/
namespace Erdos371.Kloosterman
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def fourierPolynomial (ψ : AddChar F ℂ) (c : F → ℂ) (x : F) : ℂ :=
  ∑ a : F, c a*ψ (a*x)

noncomputable def inverseCorrelation (ψ : AddChar F ℂ) (c d : F → ℂ) : ℂ :=
  ∑ x : Fˣ, fourierPolynomial ψ c (x:F)*fourierPolynomial ψ d (x:F)⁻¹

lemma inverseCorrelation_expand (ψ : AddChar F ℂ) (c d : F → ℂ) :
    inverseCorrelation ψ c d = ∑ a : F, ∑ b : F, c a*d b*kloostermanSum ψ a b := by
  have hp (x : Fˣ) : fourierPolynomial ψ c (x:F)*fourierPolynomial ψ d (x:F)⁻¹ =
      ∑ a : F, ∑ b : F, c a*d b*ψ (a*(x:F)+b*(x:F)⁻¹) := by
    rw [fourierPolynomial,fourierPolynomial,sum_mul_sum]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    rw [AddChar.map_add_eq_mul]
    ring
  unfold inverseCorrelation
  simp_rw [hp]
  have hs : (∑ x : Fˣ, ∑ a : F, ∑ b : F, c a*d b*ψ (a*(x:F)+b*(x:F)⁻¹)) =
      ∑ a : F, ∑ b : F, ∑ x : Fˣ, c a*d b*ψ (a*(x:F)+b*(x:F)⁻¹) := by
    simpa only [Fintype.sum_prod_type] using
      (sum_comm (s := (univ : Finset Fˣ)) (t := (univ : Finset (F×F)))
        (f := fun x ab => c ab.1*d ab.2*ψ (ab.1*(x:F)+ab.2*(x:F)⁻¹)))
  rw [hs]
  simp only [kloostermanSum,mul_sum]

lemma kloostermanSum_zero (ψ : AddChar F ℂ) :
    kloostermanSum ψ 0 0=Fintype.card Fˣ := by simp [kloostermanSum]

lemma centered_kloosterman_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (a b : F) :
    ‖kloostermanSum ψ a b-(if a=0 ∧ b=0 then (Fintype.card Fˣ : ℂ) else 0)‖ ≤
      Real.sqrt (Real.sqrt (3*(Fintype.card F : ℝ)^3)) := by
  by_cases h : a=0 ∧ b=0
  · rw [if_pos h,h.1,h.2,kloostermanSum_zero,sub_self,norm_zero]
    positivity
  · rw [if_neg h,sub_zero]
    apply kloosterman_norm_bound ψ hψ a b
    tauto

lemma inverseCorrelation_centered (ψ : AddChar F ℂ) (c d : F → ℂ) :
    inverseCorrelation ψ c d-(Fintype.card Fˣ : ℂ)*c 0*d 0 =
      ∑ a : F, ∑ b : F, c a*d b*(kloostermanSum ψ a b-
        (if a=0 ∧ b=0 then (Fintype.card Fˣ : ℂ) else 0)) := by
  rw [inverseCorrelation_expand]
  simp only [mul_sub,sum_sub_distrib]
  congr 1
  have h (a b : F) : c a*d b*(if a=0 ∧ b=0 then (Fintype.card Fˣ : ℂ) else 0) =
      if a=0 then (if b=0 then c 0*d 0*(Fintype.card Fˣ : ℂ) else 0) else 0 := by
    split_ifs <;> simp_all
  simp_rw [h]
  simp [mul_comm,mul_left_comm]

/-- Explicit cancellation against two finite Fourier polynomials. The
coefficient L1 norms are essential and may grow for moving tests. -/
theorem inverseCorrelation_error_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (c d : F → ℂ) :
    ‖inverseCorrelation ψ c d-(Fintype.card Fˣ : ℂ)*c 0*d 0‖ ≤
      Real.sqrt (Real.sqrt (3*(Fintype.card F : ℝ)^3)) *
        (∑ a : F, ‖c a‖)*(∑ b : F, ‖d b‖) := by
  rw [inverseCorrelation_centered]
  calc
    _ ≤ ∑ a : F, ∑ b : F, ‖c a*d b*(kloostermanSum ψ a b-
        (if a=0 ∧ b=0 then (Fintype.card Fˣ : ℂ) else 0))‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : F, ∑ b : F, ‖c a‖*‖d b‖*Real.sqrt (Real.sqrt (3*(Fintype.card F : ℝ)^3)) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      rw [norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_left (centered_kloosterman_bound ψ hψ a b) (by positivity)
    _ = _ := by simp only [← sum_mul,← mul_sum]; ring

lemma centered_kloosterman_normalized_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (a b : F) :
    ‖kloostermanSum ψ a b-(if a=0 ∧ b=0 then (Fintype.card Fˣ : ℂ) else 0)‖ / Fintype.card F ≤
      Real.sqrt (Real.sqrt (3/(Fintype.card F : ℝ))) := by
  by_cases h : a=0 ∧ b=0
  · rw [if_pos h,h.1,h.2,kloostermanSum_zero,sub_self,norm_zero,zero_div]
    positivity
  · rw [if_neg h,sub_zero]
    apply kloosterman_normalized_bound ψ hψ a b
    tauto

/-- Normalized version with the decaying factor made explicit. -/
theorem inverseCorrelation_normalized_error_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (c d : F → ℂ) :
    ‖inverseCorrelation ψ c d-(Fintype.card Fˣ : ℂ)*c 0*d 0‖ / Fintype.card F ≤
      Real.sqrt (Real.sqrt (3/(Fintype.card F : ℝ))) *
        (∑ a : F, ‖c a‖)*(∑ b : F, ‖d b‖) := by
  rw [inverseCorrelation_centered]
  have hs : ‖∑ a : F, ∑ b : F, c a*d b*(kloostermanSum ψ a b-
        (if a=0 ∧ b=0 then (Fintype.card Fˣ : ℂ) else 0))‖ ≤
      ∑ a : F, ∑ b : F, ‖c a*d b*(kloostermanSum ψ a b-
        (if a=0 ∧ b=0 then (Fintype.card Fˣ : ℂ) else 0))‖ :=
    (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_sum_le _ _)
  calc
    _ ≤ (∑ a : F, ∑ b : F, ‖c a*d b*(kloostermanSum ψ a b-
        (if a=0 ∧ b=0 then (Fintype.card Fˣ : ℂ) else 0))‖)/Fintype.card F :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ ≤ ∑ a : F, ∑ b : F, ‖c a‖*‖d b‖*Real.sqrt (Real.sqrt (3/(Fintype.card F : ℝ))) := by
      simp only [sum_div]
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      rw [norm_mul,norm_mul,mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (centered_kloosterman_normalized_bound ψ hψ a b) (by positivity)
    _ = _ := by simp only [← sum_mul,← mul_sum]; ring

open Filter in
/-- Uniformly bounded Fourier coefficient masses give cancellation along
prime moduli, even for endpoint-dependent coefficients. These coefficient
bounds have not been proved for the prime-factor comparison observables. -/
theorem prime_inverseCorrelation_normalized_tendsto (p : ℕ → ℕ)
    [∀ n, Fact (p n).Prime] (hp : Tendsto p atTop atTop)
    (c d : (n : ℕ) → ZMod (p n) → ℂ) (C D : ℝ)
    (hc : ∀ n, (∑ a : ZMod (p n), ‖c n a‖)≤C)
    (hd : ∀ n, (∑ b : ZMod (p n), ‖d n b‖)≤D) :
    Tendsto (fun n =>
      ‖inverseCorrelation ZMod.stdAddChar (c n) (d n)-
        (Fintype.card (ZMod (p n))ˣ : ℂ)*c n 0*d n 0‖/(p n : ℝ))
      atTop (nhds 0) := by
  have hC : 0≤C := (sum_nonneg (fun a _ => norm_nonneg (c 0 a))).trans (hc 0)
  have hD : 0≤D := (sum_nonneg (fun b _ => norm_nonneg (d 0 b))).trans (hd 0)
  have ht := (((((tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp hp).sqrt).sqrt).mul_const C).mul_const D
  simp only [Real.sqrt_zero,zero_mul] at ht
  apply squeeze_zero (fun n => by positivity) _ ht
  intro n
  have h := inverseCorrelation_normalized_error_bound ZMod.stdAddChar
    (ZMod.isPrimitive_stdAddChar (p n)) (c n) (d n)
  simp only [ZMod.card] at h
  apply h.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hc n) (by positivity)) (hd n)
    (sum_nonneg (fun b _ => norm_nonneg (d n b))) (by positivity)

#print axioms inverseCorrelation_expand
#print axioms inverseCorrelation_error_bound
#print axioms inverseCorrelation_normalized_error_bound
#print axioms prime_inverseCorrelation_normalized_tendsto
end Erdos371.Kloosterman
