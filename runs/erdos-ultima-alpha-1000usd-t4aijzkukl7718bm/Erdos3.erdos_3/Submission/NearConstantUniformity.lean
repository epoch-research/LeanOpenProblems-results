import Submission.QuantitativeCyclicInverse

/-! Near a constant, every stored uniformity power is bounded by the squared
mean. This local estimate upgrades coarse polynomial-phase stability to a
square-root defect bound. -/
namespace Erdos3NearConstantUniformity
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3DerivativeSpectrum
  Erdos3HigherUniformityDefect Erdos3HigherUniformityPerturbation
  Erdos3HigherPolynomialSeparation Erdos3HigherPhaseDifferences
  Erdos3HigherLocalPolynomialProgressions Erdos3PolynomialDerivativeConsistency
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- If the trivial Fourier coefficient carries at least half the energy, it
is maximal; hence the fourth Fourier moment is at most that coefficient. -/
lemma uniformity_one_le_zero (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hmean : 1/2 ≤ uniformityPower 0 f) : uniformityPower 1 f ≤ uniformityPower 0 f := by
  have hhat : ‖hat f (1 : AddChar G ℂ)‖^2 = uniformityPower 0 f := by
    simp only [hat,AddChar.one_apply,map_one,mul_one,uniformityPower]
  have htotal : (∑ χ : AddChar G ℂ, ‖hat f χ‖^2) ≤ 1 := by
    rw [parseval]
    apply expect_le univ_nonempty
    intro x _
    nlinarith only [hf x,norm_nonneg (f x)]
  have herase := sum_erase_add univ (fun χ : AddChar G ℂ ↦ ‖hat f χ‖^2) (mem_univ 1)
  have hmax (χ : AddChar G ℂ) : ‖hat f χ‖^2 ≤ uniformityPower 0 f := by
    by_cases hχ : χ = 1
    · subst χ
      exact hhat.le
    · have hs := single_le_sum (fun ψ (_ : ψ ∈ univ.erase (1 : AddChar G ℂ)) ↦
        sq_nonneg ‖hat f ψ‖) (mem_erase.mpr ⟨hχ,mem_univ χ⟩)
      dsimp only at herase
      rw [hhat] at herase
      linarith only [hs,herase,htotal,hmean]
  rw [uniformityPower_one_fourier]
  calc
    _ ≤ ∑ χ : AddChar G ℂ, uniformityPower 0 f*‖hat f χ‖^2 := by
      apply sum_le_sum
      intro χ _
      have hh := mul_le_mul_of_nonneg_right (hmax χ) (sq_nonneg ‖hat f χ‖)
      nlinarith only [hh]
    _ = uniformityPower 0 f*(∑ χ : AddChar G ℂ, ‖hat f χ‖^2) := (mul_sum ..).symm
    _ ≤ uniformityPower 0 f*1 := mul_le_mul_of_nonneg_left htotal (uniformityPower_nonneg _ _)
    _ = _ := mul_one _

lemma mean_square_of_close_one (f : G → ℂ) :
    1-2*meanDistance f (fun _ ↦ 1) ≤ uniformityPower 0 f := by
  have he : ‖(𝔼 x : G, f x)-1‖ ≤ meanDistance f (fun _ ↦ 1) := by
    have hh := RCLike.norm_expect_le (K := ℂ) (s := univ) (f := fun x : G ↦ f x-1)
    simpa only [expect_sub_distrib,Fintype.expect_const,meanDistance] using hh
  have hh := norm_sub_le (𝔼 x : G, f x) ((𝔼 x : G, f x)-1)
  rw [sub_sub_cancel,norm_one] at hh
  have hs := sq_nonneg (‖𝔼 x : G, f x‖-1)
  change _ ≤ ‖𝔼 x : G, f x‖^2
  nlinarith only [he,hh,hs]

noncomputable def localRadius (n : ℕ) : ℝ := (1/2)^(n+3)

lemma localRadius_pos (n : ℕ) : 0 < localRadius n := pow_pos (by norm_num) _
lemma localRadius_succ (n : ℕ) : 2*localRadius (n+1) = localRadius n := by
  unfold localRadius
  rw [show n+1+3 = (n+3)+1 by omega,pow_succ (1/2 : ℝ) (n+3)]
  ring
lemma localRadius_le_eighth (n : ℕ) : localRadius n ≤ 1/8 := by
  have hh := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
    (show 3 ≤ n+3 by omega)
  norm_num only [show (1/2 : ℝ)^3 = 1/8 by norm_num] at hh
  exact hh

/-- A degree-dependent L1 neighborhood of the constant1 has a uniform,
dimension-free upper bound by the squared mean. -/
theorem uniformity_le_mean_near_one (n : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hclose : meanDistance f (fun _ ↦ 1) ≤ localRadius n) :
    uniformityPower n f ≤ uniformityPower 0 f := by
  induction n generalizing f with
  | zero => exact le_rfl
  | succ n ih =>
    have hder (h : G) : meanDistance (derivative f h) (fun _ ↦ 1) ≤ localRadius n := by
      have hh := derivative_meanDistance f (fun _ ↦ 1) hf (fun _ ↦ (norm_one : ‖(1 : ℂ)‖ = 1).le) h
      have he : derivative (fun _ : G ↦ (1 : ℂ)) h = fun _ ↦ 1 := by
        funext x
        simp only [derivative,map_one,mul_one]
      rw [he] at hh
      exact hh.trans ((mul_le_mul_of_nonneg_left hclose (by norm_num)).trans_eq (localRadius_succ n))
    have hmean : 1/2 ≤ uniformityPower 0 f := by
      have hh := mean_square_of_close_one f
      have hr := localRadius_le_eighth (n+1)
      linarith only [hh,hclose,hr]
    calc
      _ ≤ 𝔼 h : G, uniformityPower 0 (derivative f h) :=
        expect_le_expect (fun h _ ↦ ih _ (derivative_norm_le_one f hf h) (hder h))
      _ = uniformityPower 1 f := rfl
      _ ≤ _ := uniformity_one_le_zero f hf hmean

lemma derivative_mul_phase (f : G → ℂ) (q : G → Additive Circle) (h : G) :
    derivative (fun x ↦ f x*phase (q x)) h =
      fun x ↦ derivative f h x*phase (fwdDiff h q x) := by
  funext x
  simp only [derivative,fwdDiff,phase_sub,map_mul]
  ring

/-- Exact invariance under multiplication by a phase polynomial of the
appropriate degree; the complex function need not be unit-valued. -/
theorem uniformity_mul_polynomial (n : ℕ) (f : G → ℂ) (q : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ n q) :
    uniformityPower n (fun x ↦ f x*phase (q x)) = uniformityPower n f := by
  induction n generalizing f q with
  | zero =>
    have hc := global_polynomial_zero_constant q hq
    have he : (fun x ↦ f x*phase (q x)) = fun x ↦ phase (q 0)*f x := by
      funext x
      rw [hc x,mul_comm]
    rw [he,uniformityPower_unit_scale 0 f (phase_norm _)]
  | succ n ih =>
    change (𝔼 h : G, uniformityPower n (derivative (fun x ↦ f x*phase (q x)) h)) = _
    apply expect_congr rfl
    intro h _
    rw [derivative_mul_phase]
    exact ih _ _ (global_polynomial_derivative n q hq h)

#print axioms uniformity_le_mean_near_one
#print axioms uniformity_mul_polynomial
end Erdos3NearConstantUniformity
