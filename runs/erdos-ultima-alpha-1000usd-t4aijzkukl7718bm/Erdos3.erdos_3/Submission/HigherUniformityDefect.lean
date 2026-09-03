import Submission.HigherLocalPolynomialProgressions
import Submission.FiniteUniformity

/-! An exact cube-defect identity for circle-valued phases in every degree.
This identifies the maximal-uniformity case, but is not an inverse theorem
for arbitrary positive uniformity. -/
namespace Erdos3HigherUniformityDefect
open Finset Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
  Erdos3FiniteUniformity Erdos3QuadraticRecurrenceAverages Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Mean squared failure of the kth additive cube difference to vanish. -/
noncomputable def cubeDefect (k : ℕ) (q : G → Additive Circle) : ℝ :=
  𝔼 h : Fin k → G, 𝔼 x : G, ‖phase (cubeDifference k q h x)-1‖^2

lemma phase_eq_one_iff (z : Additive Circle) : phase z = 1 ↔ z = 0 := by
  constructor
  · intro h
    exact Circle.coe_injective h
  · rintro rfl
    rfl

lemma cubeDefect_nonneg (k : ℕ) (q : G → Additive Circle) : 0 ≤ cubeDefect k q :=
  expect_nonneg (fun _ _ ↦ expect_nonneg (fun _ _ ↦ sq_nonneg _))

lemma cubeDefect_zero_iff (k : ℕ) (q : G → Additive Circle) :
    cubeDefect k q = 0 ↔ ∀ h : Fin k → G, ∀ x, cubeDifference k q h x = 0 := by
  unfold cubeDefect
  rw [expect_eq_zero_iff_of_nonneg (fun _ _ ↦ expect_nonneg (fun _ _ ↦ sq_nonneg _))]
  simp only [mem_univ, forall_true_left]
  apply forall_congr'
  intro h
  rw [expect_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  simp only [mem_univ, forall_true_left, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero,
    phase_eq_one_iff]

/-- Separate the first direction from a finite tuple. -/
def directionEquiv (k : ℕ) : (Fin (k+1) → G) ≃ G × (Fin k → G) where
  toFun h := (h 0, fun i ↦ h i.succ)
  invFun h := Fin.cons h.1 h.2
  left_inv h := Fin.cons_self_tail h
  right_inv h := by simp

lemma expect_directions_succ (k : ℕ) (F : (Fin (k+1) → G) → ℝ) :
    (𝔼 h, F h) = 𝔼 a : G, 𝔼 h : Fin k → G, F (Fin.cons a h) := by
  calc
    _ = 𝔼 h : G × (Fin k → G), F (Fin.cons h.1 h.2) :=
      Fintype.expect_equiv (directionEquiv k) _ _ (fun h ↦ by
        exact congrArg F (Fin.cons_self_tail h).symm)
    _ = _ := by
      rw [← univ_product_univ]
      exact expect_product' (univ : Finset G) (univ : Finset (Fin k → G))
        (fun a h ↦ F (Fin.cons a h))

lemma cubeDefect_succ (k : ℕ) (q : G → Additive Circle) :
    cubeDefect (k+1) q = 𝔼 h : G, cubeDefect k (fwdDiff h q) := by
  unfold cubeDefect
  rw [expect_directions_succ]
  apply expect_congr rfl
  intro a _
  apply expect_congr rfl
  intro h _
  simp only [cubeDifference, Fin.cons_zero, Fin.cons_succ]

lemma phase_fwdDiff (q : G → Additive Circle) (h : G) :
    (fun x ↦ phase (fwdDiff h q x)) = derivative (fun x ↦ phase (q x)) h := by
  funext x
  exact phase_sub _ _

lemma cubeDefect_zero (q : G → Additive Circle) :
    cubeDefect 0 q = 𝔼 x : G, ‖phase (q x)-1‖^2 := by
  unfold cubeDefect
  simp only [cubeDifference, Fintype.expect_const]

lemma derivative_re_mean (f : G → ℂ) :
    (𝔼 h : G, 𝔼 x : G, (derivative f h x).re) = ‖𝔼 x : G, f x‖^2 := by
  rw [norm_mean_sq_pair, expect_comm]
  apply expect_congr rfl
  intro x _
  calc
    _ = 𝔼 y : G, (f y*conj (f x)).re :=
      Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun h ↦ rfl)
    _ = 𝔼 y : G, (f x*conj (f y)).re := by
      apply expect_congr rfl
      intro y _
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring

/-- Index n is U^(n+1) to the power 2^(n+1). Thus the defect uses
(n+1)-dimensional cubes, not n-dimensional cubes. -/
theorem cubeDefect_uniformity (n : ℕ) (q : G → Additive Circle) :
    cubeDefect (n+1) q = 2*(1-uniformityPower n (fun x ↦ phase (q x))) := by
  induction n generalizing q with
  | zero =>
    rw [cubeDefect_succ]
    simp_rw [cubeDefect_zero]
    have he (h x : G) : ‖phase (fwdDiff h q x)-1‖^2 =
        2*(1-(derivative (fun x ↦ phase (q x)) h x).re) := by
      rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (phase_norm _)]
      rw [show phase (fwdDiff h q x) = derivative (fun x ↦ phase (q x)) h x from
        congr_fun (phase_fwdDiff q h) x]
    simp_rw [he, ← mul_expect, expect_sub_distrib, Fintype.expect_const]
    rw [derivative_re_mean]
    rfl
  | succ n ih =>
    rw [cubeDefect_succ]
    simp_rw [ih, phase_fwdDiff, ← mul_expect, expect_sub_distrib, Fintype.expect_const]
    rfl

/-- The exact, maximal-uniformity inverse statement, for phases already valued
in the circle. No assertion for an arbitrary lower bound delta>0 is made. -/
theorem uniformity_eq_one_iff_polynomial (n : ℕ) (q : G → Additive Circle) :
    uniformityPower n (fun x ↦ phase (q x)) = 1 ↔
      IsLocallyPolynomial Set.univ n q := by
  have he : uniformityPower n (fun x ↦ phase (q x)) = 1 ↔ cubeDefect (n+1) q = 0 := by
    rw [cubeDefect_uniformity]
    constructor <;> intro h <;> linarith only [h]
  rw [he, cubeDefect_zero_iff]
  unfold IsLocallyPolynomial
  simp only [Set.mem_univ, implies_true, forall_const]
  exact forall_comm

lemma mean_derivative_norm (f : G → ℂ) :
    (𝔼 h : G, 𝔼 x : G, ‖derivative f h x‖) = (𝔼 x : G, ‖f x‖)^2 := by
  rw [expect_comm]
  have he (x : G) : (𝔼 h : G, ‖derivative f h x‖) =
      (𝔼 y : G, ‖f y‖)*‖f x‖ := by
    rw [expect_mul]
    exact Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun h ↦ by
      simp only [derivative, norm_mul, Complex.norm_conj]
      rfl)
  simp_rw [he]
  rw [← mul_expect, pow_two]

lemma uniformity_le_mean_norm (n : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    uniformityPower n f ≤ 𝔼 x : G, ‖f x‖ := by
  have hm2 (g : G → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) :
      (𝔼 x : G, ‖g x‖)^2 ≤ 𝔼 x : G, ‖g x‖ := by
    have hm0 : 0 ≤ 𝔼 x : G, ‖g x‖ := expect_nonneg (fun _ _ ↦ norm_nonneg _)
    have hm1 : (𝔼 x : G, ‖g x‖) ≤ 1 := expect_le univ_nonempty (fun x _ ↦ hg x)
    nlinarith only [hm0,hm1]
  induction n generalizing f with
  | zero =>
    exact (pow_le_pow_left₀ (norm_nonneg _) (RCLike.norm_expect_le (K := ℂ)) 2).trans (hm2 f hf)
  | succ n ih =>
    calc
      _ ≤ 𝔼 h : G, 𝔼 x : G, ‖derivative f h x‖ :=
        expect_le_expect (fun h _ ↦ ih (derivative f h) (derivative_norm_le_one f hf h))
      _ = (𝔼 x : G, ‖f x‖)^2 := mean_derivative_norm f
      _ ≤ _ := hm2 f hf

lemma maximal_uniformity_norm (n : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hU : uniformityPower n f = 1) : ∀ x, ‖f x‖ = 1 := by
  have hm := uniformity_le_mean_norm n f hf
  rw [hU] at hm
  have hz : (𝔼 x : G, (1-‖f x‖)) = 0 := by
    rw [expect_sub_distrib, Fintype.expect_const]
    have h1 := expect_le univ_nonempty (fun x _ ↦ hf x)
    linarith only [hm,h1]
  have hh := (expect_eq_zero_iff_of_nonneg (fun x _ ↦ sub_nonneg.mpr (hf x))).mp hz
  intro x
  linarith only [hh x (mem_univ x)]

/-- Complete classification of one-bounded functions with maximal higher
uniformity. The conclusion is a global circle polynomial of degree at most n. -/
theorem maximal_uniformity_iff_phase_polynomial (n : ℕ) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    uniformityPower n f = 1 ↔ ∃ q : G → Additive Circle,
      (∀ x, f x = phase (q x)) ∧ IsLocallyPolynomial Set.univ n q := by
  constructor
  · intro hU
    have hn := maximal_uniformity_norm n f hf hU
    let q : G → Additive Circle := fun x ↦
      Additive.ofMul (⟨f x, mem_sphere_zero_iff_norm.mpr (hn x)⟩ : Circle)
    have hq : (fun x ↦ phase (q x)) = f := rfl
    exact ⟨q,fun _ ↦ rfl,(uniformity_eq_one_iff_polynomial n q).mp (hq.symm ▸ hU)⟩
  · rintro ⟨q,hq,hpoly⟩
    have he : f = fun x ↦ phase (q x) := funext hq
    rw [he]
    exact (uniformity_eq_one_iff_polynomial n q).mpr hpoly

#print axioms cubeDefect_uniformity
#print axioms uniformity_eq_one_iff_polynomial
#print axioms maximal_uniformity_iff_phase_polynomial
end Erdos3HigherUniformityDefect
