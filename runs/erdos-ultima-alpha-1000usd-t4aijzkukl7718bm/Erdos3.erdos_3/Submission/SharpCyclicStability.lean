import Submission.NearConstantUniformity

/-! Square-root stability at maximal higher uniformity. A coarse polynomial
approximation is bootstrapped to mean-square error at most twice the defect. -/
namespace Erdos3SharpCyclicStability
open Finset Erdos3NearConstantUniformity Erdos3QuantitativeCyclicInverse
  Erdos3HigherUniformityPerturbation Erdos3HigherUniformityDefect
  Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
  Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteSamplingMoments
  Erdos3LinearFormsUniformity Erdos3PolynomialDerivativeConsistency
  Erdos3DensePolynomialCocycle
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000
variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def meanSquareDistance (f g : G → ℂ) : ℝ := 𝔼 x : G, ‖f x-g x‖^2

lemma meanDistance_sq_le (f g : G → ℂ) : (meanDistance f g)^2 ≤ meanSquareDistance f g :=
  expect_even_pow_le (by decide : Even 2) _

/-- Unit constants suffice even when the original function has zeros. -/
theorem complex_constant_approximation (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ c : Additive Circle, meanSquareDistance f (fun _ ↦ phase c) ≤ 2*(1-uniformityPower 0 f) := by
  let μ : ℂ := 𝔼 x : G, f x
  let c : Additive Circle := radialPhase (fun _ : G ↦ μ) 0
  have hrec : (‖μ‖ : ℂ)*phase c = μ := radialPhase_reconstruct (fun _ : G ↦ μ) 0
  have hμ : ‖μ‖ ≤ 1 := (RCLike.norm_expect_le (K := ℂ)).trans
    (expect_le univ_nonempty (fun x _ ↦ hf x))
  have hprod : μ*conj (phase c) = (‖μ‖ : ℂ) := by
    calc
      _ = ((‖μ‖ : ℂ)*phase c)*conj (phase c) := by rw [hrec]
      _ = _ := by rw [mul_assoc,mul_conj_eq_one (phase_norm _),mul_one]
  have hcorr : (𝔼 x : G, (f x*conj (phase c)).re) = ‖μ‖ := by
    rw [← expect_re,← expect_mul]
    change (μ*conj (phase c)).re = _
    rw [hprod,Complex.ofReal_re]
  have he (x : G) : ‖f x-phase c‖^2 = ‖f x‖^2+1-2*(f x*conj (phase c)).re := by
    rw [Complex.sq_norm,Complex.normSq_sub,Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq,phase_norm,one_pow]
  have hdist : meanSquareDistance f (fun _ ↦ phase c) = (𝔼 x : G, ‖f x‖^2)+1-2*‖μ‖ := by
    unfold meanSquareDistance
    simp_rw [he]
    rw [expect_sub_distrib,expect_add_distrib,Fintype.expect_const,← mul_expect,hcorr]
  have hL2 : (𝔼 x : G, ‖f x‖^2) ≤ 1 := by
    apply expect_le univ_nonempty
    intro x _
    nlinarith only [hf x,norm_nonneg (f x)]
  have hμsq : ‖μ‖^2 ≤ ‖μ‖ := by nlinarith only [hμ,norm_nonneg μ]
  refine ⟨c,?_⟩
  rw [hdist]
  change _ ≤ 2*(1-‖μ‖^2)
  linarith only [hL2,hμsq]

noncomputable def twist (f : G → ℂ) (q : G → Additive Circle) (x : G) : ℂ :=
  f x*conj (phase (q x))

lemma twist_reconstruct (f : G → ℂ) (q : G → Additive Circle) :
    (fun x ↦ twist f q x*phase (q x)) = f := by
  funext x
  calc
    _ = f x*(phase (q x)*conj (phase (q x))) := by unfold twist; ring
    _ = _ := by rw [mul_conj_eq_one (phase_norm _),mul_one]

lemma twist_distance (f : G → ℂ) (q : G → Additive Circle) (c : Additive Circle) (x : G) :
    ‖f x-phase (q x+c)‖ = ‖twist f q x-phase c‖ := by
  have he : f x-phase (q x+c) = (twist f q x-phase c)*phase (q x) := by
    rw [sub_mul,show twist f q x*phase (q x) = f x from congr_fun (twist_reconstruct f q) x,
      phase_add,mul_comm (phase c)]
  rw [he,norm_mul,phase_norm,mul_one]

lemma twist_meanDistance_one (f : G → ℂ) (q : G → Additive Circle) :
    meanDistance (twist f q) (fun _ ↦ 1) = meanDistance f (fun x ↦ phase (q x)) := by
  unfold meanDistance
  apply expect_congr rfl
  intro x _
  simpa only [add_zero,show phase 0 = (1 : ℂ) from rfl] using (twist_distance f q 0 x).symm

/-- Once an approximation enters the degree-dependent neighborhood, its error
can be improved to an optimal-order square-root bound in the uniformity defect. -/
theorem improve_coarse_polynomial_approximation (n : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (q : G → Additive Circle) (hq : IsLocallyPolynomial Set.univ n q)
    (hclose : meanDistance f (fun x ↦ phase (q x)) ≤ localRadius n) :
    ∃ r : G → Additive Circle, IsLocallyPolynomial Set.univ n r ∧
      meanSquareDistance f (fun x ↦ phase (r x)) ≤ 2*(1-uniformityPower n f) := by
  let g := twist f q
  have hg (x : G) : ‖g x‖ ≤ 1 := by
    dsimp only [g,twist]
    rw [norm_mul,Complex.norm_conj,phase_norm,mul_one]
    exact hf x
  have hdist : meanDistance g (fun _ ↦ 1) ≤ localRadius n := by
    rw [twist_meanDistance_one]
    exact hclose
  have hU : uniformityPower n f = uniformityPower n g := by
    have hh := uniformity_mul_polynomial n g q hq
    rw [twist_reconstruct] at hh
    exact hh
  have hmean : uniformityPower n f ≤ uniformityPower 0 g := by
    rw [hU]
    exact uniformity_le_mean_near_one n g hg hdist
  obtain ⟨c,hc⟩ := complex_constant_approximation g hg
  refine ⟨fun x ↦ q x+c,global_polynomial_add n _ _ hq (global_polynomial_const n c),?_⟩
  have he : meanSquareDistance f (fun x ↦ phase (q x+c)) = meanSquareDistance g (fun _ ↦ phase c) := by
    unfold meanSquareDistance
    exact expect_congr rfl (fun x _ ↦ congrArg (fun t : ℝ ↦ t^2) (twist_distance f q c x))
  rw [he]
  linarith only [hc,hmean]

noncomputable def sharpTolerance (n : ℕ) : ℝ := boundedTolerance n (localRadius n)
lemma sharpTolerance_pos (n : ℕ) : 0 < sharpTolerance n := boundedTolerance_pos n (localRadius_pos n)

/-- On a cyclic group the coarse approximation is automatic below an explicit
fixed defect threshold. The final mean-square constant is universally 2. -/
theorem sharp_cyclic_inverse (n p : ℕ) [NeZero p] (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hU : 1-sharpTolerance n ≤ uniformityPower n f) :
    ∃ q : ZMod p → Additive Circle, IsLocallyPolynomial Set.univ n q ∧
      meanSquareDistance f (fun x ↦ phase (q x)) ≤ 2*(1-uniformityPower n f) := by
  obtain ⟨q,hq,hclose⟩ := quantitative_cyclic_inverse n p (localRadius n) (localRadius_pos n)
    ((localRadius_le_eighth n).trans (by norm_num)) f hf hU
  exact improve_coarse_polynomial_approximation n f hf q hq hclose

/-- In particular the tolerance is quadratic in the requested L1 error, once
capped by the fixed degree-only threshold. -/
theorem sharp_cyclic_inverse_L1 (n p : ℕ) [NeZero p] (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (hU : 1-min (sharpTolerance n) (ε^2/2) ≤ uniformityPower n f) :
    ∃ q : ZMod p → Additive Circle, IsLocallyPolynomial Set.univ n q ∧
      meanDistance f (fun x ↦ phase (q x)) ≤ ε := by
  have hU' : 1-sharpTolerance n ≤ uniformityPower n f := by
    linarith only [hU,min_le_left (sharpTolerance n) (ε^2/2)]
  obtain ⟨q,hq,hmean⟩ := sharp_cyclic_inverse n p f hf hU'
  have hh := meanDistance_sq_le f (fun x ↦ phase (q x))
  refine ⟨q,hq,?_⟩
  nlinarith only [hh,hmean,hU,min_le_right (sharpTolerance n) (ε^2/2),hε]

#print axioms improve_coarse_polynomial_approximation
#print axioms sharp_cyclic_inverse
#print axioms sharp_cyclic_inverse_L1
end Erdos3SharpCyclicStability
