import Submission.HigherUniformityDefect

/-! L1 stability of higher uniformity and radial phase normalization.
Near-maximal uniformity yields small average polynomial-cube defect. This does
not correct the phase to an exact polynomial or handle general positive uniformity. -/
namespace Erdos3HigherUniformityPerturbation
open Finset Erdos3HigherUniformityDefect Erdos3FiniteUniformity
  Erdos3HigherPhaseDifferences
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000
variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def meanDistance (f g : G → ℂ) : ℝ := 𝔼 x : G, ‖f x-g x‖

lemma meanDistance_nonneg (f g : G → ℂ) : 0 ≤ meanDistance f g :=
  expect_nonneg (fun _ _ ↦ norm_nonneg _)

lemma norm_sq_lipschitz {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |‖z‖^2-‖w‖^2| ≤ 2*‖z-w‖ := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg w))]
  rw [mul_comm (‖z‖+‖w‖)]
  calc
    _ ≤ ‖z-w‖*(‖z‖+‖w‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z w) (by positivity)
    _ ≤ ‖z-w‖*2 := mul_le_mul_of_nonneg_left (by linarith only [hz,hw]) (norm_nonneg _)
    _ = _ := mul_comm _ _

lemma derivative_distance_pointwise (f g : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (h x : G) :
    ‖derivative f h x-derivative g h x‖ ≤ ‖f (x+h)-g (x+h)‖+‖f x-g x‖ := by
  calc
    _ = ‖(f (x+h)-g (x+h))*conj (f x)+g (x+h)*conj (f x-g x)‖ := by
      congr 1
      simp only [derivative, map_sub]
      ring
    _ ≤ ‖(f (x+h)-g (x+h))*conj (f x)‖+‖g (x+h)*conj (f x-g x)‖ := norm_add_le _ _
    _ = ‖f (x+h)-g (x+h)‖*‖f x‖+‖g (x+h)‖*‖f x-g x‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    _ ≤ ‖f (x+h)-g (x+h)‖*1+1*‖f x-g x‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hg _) (norm_nonneg _))
    _ = _ := by ring

lemma derivative_meanDistance (f g : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (h : G) :
    meanDistance (derivative f h) (derivative g h) ≤ 2*meanDistance f g := by
  calc
    _ ≤ 𝔼 x : G, (‖f (x+h)-g (x+h)‖+‖f x-g x‖) :=
      expect_le_expect (fun x _ ↦ derivative_distance_pointwise f g hf hg h x)
    _ = (𝔼 x : G, ‖f (x+h)-g (x+h)‖)+meanDistance f g := expect_add_distrib _ _ _
    _ = meanDistance f g+meanDistance f g := by
      congr 1
      exact Fintype.expect_equiv (Equiv.addRight h) _ _ (fun _ ↦ rfl)
    _ = _ := by ring

/-- A dimension-free L1 perturbation bound, with the explicit degree factor. -/
theorem uniformity_lipschitz (n : ℕ) (f g : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) :
    |uniformityPower n f-uniformityPower n g| ≤ (2 : ℝ)^(n+1)*meanDistance f g := by
  induction n generalizing f g with
  | zero =>
    have hfm : ‖𝔼 x : G, f x‖ ≤ 1 :=
      (RCLike.norm_expect_le (K := ℂ)).trans (expect_le univ_nonempty (fun x _ ↦ hf x))
    have hgm : ‖𝔼 x : G, g x‖ ≤ 1 :=
      (RCLike.norm_expect_le (K := ℂ)).trans (expect_le univ_nonempty (fun x _ ↦ hg x))
    have hh := norm_sq_lipschitz hfm hgm
    rw [← expect_sub_distrib] at hh
    exact hh.trans (by simpa only [Nat.zero_add,pow_one,meanDistance] using
      mul_le_mul_of_nonneg_left (RCLike.norm_expect_le (K := ℂ)
        (s := univ) (f := fun x : G ↦ f x-g x)) (by norm_num : (0 : ℝ) ≤ 2))
  | succ n ih =>
    change |(𝔼 h : G, uniformityPower n (derivative f h))-
      (𝔼 h : G, uniformityPower n (derivative g h))| ≤ _
    rw [← expect_sub_distrib]
    calc
      _ ≤ 𝔼 h : G, |uniformityPower n (derivative f h)-uniformityPower n (derivative g h)| :=
        abs_expect_le _ _
      _ ≤ 𝔼 h : G, (2 : ℝ)^(n+1)*meanDistance (derivative f h) (derivative g h) :=
        expect_le_expect (fun h _ ↦ ih _ _ (derivative_norm_le_one f hf h)
          (derivative_norm_le_one g hg h))
      _ ≤ 𝔼 _h : G, (2 : ℝ)^(n+1)*(2*meanDistance f g) :=
        expect_le_expect (fun h _ ↦ mul_le_mul_of_nonneg_left
          (derivative_meanDistance f g hf hg h) (pow_nonneg (by norm_num) _))
      _ = _ := by rw [Fintype.expect_const, pow_succ (2 : ℝ) (n+1)]; ring

/-- Polar normalization chooses 1 at zero, rather than introducing a zero-valued
"phase". All values genuinely lie in the circle. -/
noncomputable def radialPhase (f : G → ℂ) (x : G) : Additive Circle :=
  Additive.ofMul (Circle.exp (Complex.arg (f x)))

lemma radialPhase_reconstruct (f : G → ℂ) (x : G) :
    (‖f x‖ : ℂ)*phase (radialPhase f x) = f x := by
  exact Complex.norm_mul_exp_arg_mul_I _

lemma radialPhase_distance (f : G → ℂ) (x : G) (hf : ‖f x‖ ≤ 1) :
    ‖f x-phase (radialPhase f x)‖ = 1-‖f x‖ := by
  have he : f x-phase (radialPhase f x) =
      ((‖f x‖-1 : ℝ) : ℂ)*phase (radialPhase f x) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul, radialPhase_reconstruct]
  rw [he, norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hf)]
  ring

lemma radialPhase_meanDistance (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    meanDistance f (fun x ↦ phase (radialPhase f x)) = 1-(𝔼 x : G, ‖f x‖) := by
  unfold meanDistance
  simp_rw [radialPhase_distance f _ (hf _)]
  rw [expect_sub_distrib, Fintype.expect_const]

/-- Near-maximal uniformity supplies a nearby unit phase with small cube defect.
This is an approximate polynomiality test, not correction to an exact polynomial. -/
theorem near_maximal_cube_defect (n : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {ε : ℝ} (hU : 1-ε ≤ uniformityPower n f) :
    ∃ q : G → Additive Circle, meanDistance f (fun x ↦ phase (q x)) ≤ ε ∧
      cubeDefect (n+1) q ≤ (2+(2 : ℝ)^(n+2))*ε := by
  let q := radialPhase f
  have hdist : meanDistance f (fun x ↦ phase (q x)) ≤ ε := by
    rw [radialPhase_meanDistance f hf]
    linarith only [hU,uniformity_le_mean_norm n f hf]
  refine ⟨q,hdist,?_⟩
  have hp := uniformity_lipschitz n f (fun x ↦ phase (q x)) hf (fun x ↦ (phase_norm _).le)
  have hle := (le_abs_self (uniformityPower n f-uniformityPower n (fun x ↦ phase (q x)))).trans hp
  have hd := mul_le_mul_of_nonneg_left hdist (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n+1))
  rw [cubeDefect_uniformity, show n+2 = (n+1)+1 by omega, pow_succ (2 : ℝ) (n+1)]
  nlinarith only [hle,hd,hU]

#print axioms uniformity_lipschitz
#print axioms near_maximal_cube_defect
end Erdos3HigherUniformityPerturbation
