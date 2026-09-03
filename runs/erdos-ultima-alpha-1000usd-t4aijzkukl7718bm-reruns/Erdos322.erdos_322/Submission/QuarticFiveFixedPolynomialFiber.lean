import Submission.QuarticFiveInputAllDegrees
import Submission.HomogeneousTopComponents

/-! Polynomial maps of a fixed five-variable quartic fiber to a constant
four-variable quartic norm. The hypothesis is a polynomial congruence,
not merely an assertion about rational points on a fiber. -/
namespace Erdos322Research.QuarticFormalSpecialization
noncomputable section
open MvPolynomial HomogeneousTopComponents
set_option Elab.async false
set_option maxHeartbeats 0

abbrev MVFive := MvPolynomial (Fin 5) GaussianField

def fiveFiber (N : GaussianField) : MVFive := mvFiveNorm - MvPolynomial.C N

lemma mvFiveNorm_ne_zero : mvFiveNorm ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.finSuccEquiv GaussianField 4).toRingHom h
  change MvPolynomial.finSuccEquiv GaussianField 4 mvFiveNorm = _ at hh
  rw [finSucc_fiveNorm, map_zero] at hh
  exact fiveNorm_monic.ne_zero hh

lemma mvFiveNorm_homogeneous : mvFiveNorm.IsHomogeneous 4 := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_X GaussianField j).pow 4

lemma mvFiveNorm_degree : mvFiveNorm.totalDegree = 4 :=
  mvFiveNorm_homogeneous.totalDegree mvFiveNorm_ne_zero

lemma fiveFiber_degree (N : GaussianField) : (fiveFiber N).totalDegree = 4 := by
  rw [fiveFiber, sub_eq_add_neg, totalDegree_add_eq_left_of_totalDegree_lt,
    mvFiveNorm_degree]
  simp only [totalDegree_neg, totalDegree_C, mvFiveNorm_degree]
  omega

lemma fiveFiber_ne_zero (N : GaussianField) : fiveFiber N ≠ 0 := by
  intro h
  have hh := congrArg totalDegree h
  rw [fiveFiber_degree, totalDegree_zero] at hh
  omega

/-- Multivariate form of the all-degree divisibility theorem. -/
lemma mvFiveNorm_dvd_all (P : Fin 4 → MVFive)
    (h : mvFiveNorm ∣ ∑ i, P i ^ 4) : ∀ i, mvFiveNorm ∣ P i := by
  let E := MvPolynomial.finSuccEquiv GaussianField 4
  have hd := map_dvd E.toRingHom h
  simp only [map_sum, map_pow] at hd
  change E mvFiveNorm ∣ ∑ i, E (P i) ^ 4 at hd
  rw [finSucc_fiveNorm] at hd
  intro i
  obtain ⟨Q, hQ⟩ := fiveNorm_dvd_all (fun i ↦ E (P i)) hd i
  refine ⟨E.symm Q, E.injective ?_⟩
  change E.toRingHom (P i) = E.toRingHom (mvFiveNorm * E.symm Q)
  rw [map_mul]
  change E (P i) = E mvFiveNorm * E (E.symm Q)
  rw [finSucc_fiveNorm, E.apply_symm_apply]
  exact hQ

private lemma norm_difference_degree (P : Fin 4 → MVFive) (c : GaussianField)
    (D : ℕ) (hP : ∀ i, (P i).totalDegree ≤ D) :
    (∑ i, P i ^ 4 - MvPolynomial.C c).totalDegree ≤ 4 * D := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_pow (P i) 4).trans (Nat.mul_le_mul_left 4 (hP i))
  · simp

private lemma top_norm_divisibility (P : Fin 4 → MVFive) (N c : GaussianField)
    (D : ℕ) (hD : 0 < D) (hP : ∀ i, (P i).totalDegree ≤ D)
    (h : fiveFiber N ∣ ∑ i, P i ^ 4 - MvPolynomial.C c) :
    ∀ i, mvFiveNorm ∣ homogeneousComponent D (P i) := by
  obtain ⟨Q, hQ⟩ := h
  have hdeg : Q.totalDegree ≤ 4 * D - 4 := by
    by_cases hz : Q = 0
    · simp [hz]
    have hh := norm_difference_degree P c D hP
    rw [hQ, totalDegree_mul_of_isDomain (fiveFiber_ne_zero N) hz,
      fiveFiber_degree] at hh
    omega
  have hqzero : homogeneousComponent (4 * D) Q = 0 :=
    homogeneousComponent_eq_zero _ Q (by omega)
  have hCzero : homogeneousComponent (4 * D) (MvPolynomial.C c : MVFive) = 0 :=
    homogeneousComponent_eq_zero _ _ (by simp; omega)
  have hnorm : homogeneousComponent 4 mvFiveNorm = mvFiveNorm := by
    simpa using (homogeneousComponent_of_mem (m := 4) mvFiveNorm_homogeneous)
  have he := congrArg (homogeneousComponent (4 * D)) hQ
  rw [map_sub, map_sum, hCzero, sub_zero] at he
  simp_rw [top_pow _ D 4 (hP _)] at he
  have hr : homogeneousComponent (4 * D) (fiveFiber N * Q) =
      mvFiveNorm * homogeneousComponent (4 * D - 4) Q := by
    rw [fiveFiber, sub_mul, map_sub, homogeneousComponent_C_mul, hqzero, mul_zero, sub_zero]
    have hh := top_mul mvFiveNorm Q 4 (4 * D - 4) mvFiveNorm_degree.le hdeg
    rw [show 4 + (4 * D - 4) = 4 * D by omega, hnorm] at hh
    exact hh
  rw [hr] at he
  apply mvFiveNorm_dvd_all (fun i ↦ homogeneousComponent D (P i))
  exact ⟨homogeneousComponent (4 * D - 4) Q, he⟩

/-- Congruence to a constant quartic norm modulo a fixed source fiber forces
all coordinates to be constant modulo the same fiber. -/
theorem fiveFiber_constant_mod_degree (D : ℕ) :
    ∀ (P : Fin 4 → MVFive) (N c : GaussianField),
      (∀ i, (P i).totalDegree ≤ D) →
      fiveFiber N ∣ (∑ i, P i ^ 4) - MvPolynomial.C c →
      ∃ b : Fin 4 → GaussianField, ∀ i, fiveFiber N ∣ P i - MvPolynomial.C (b i) := by
  induction D using Nat.strong_induction_on with
  | h D ih =>
    intro P N c hP hnorm
    by_cases hD : D = 0
    · refine ⟨fun i ↦ (P i).coeff 0, fun i ↦ ?_⟩
      have hp : (P i).totalDegree = 0 := by have := hP i; omega
      rw [(totalDegree_eq_zero_iff_eq_C.mp hp), sub_self]
      exact dvd_zero _
    have hDpos : 0 < D := by omega
    choose Q hQ using top_norm_divisibility P N c D hDpos hP hnorm
    have hQdeg (i : Fin 4) : (Q i).totalDegree < D := by
      by_cases hz : Q i = 0
      · simpa [hz] using hDpos
      have hh := (homogeneousComponent_isHomogeneous D (P i)).totalDegree_le
      rw [hQ i, totalDegree_mul_of_isDomain mvFiveNorm_ne_zero hz,
        mvFiveNorm_degree] at hh
      omega
    let P' (i : Fin 4) := P i - fiveFiber N * Q i
    have hPi (i : Fin 4) : P' i =
        (P i - homogeneousComponent D (P i)) + MvPolynomial.C N * Q i := by
      rw [hQ i]
      dsimp only [P', fiveFiber]
      ring
    have hP'deg (i : Fin 4) : (P' i).totalDegree ≤ D - 1 := by
      have h1 := sub_top_degree_lt (P i) D hDpos (hP i)
      have h2 : (MvPolynomial.C N * Q i).totalDegree < D := by
        exact (totalDegree_mul _ _).trans_lt (by simpa using hQdeg i)
      rw [hPi i]
      have hh := (totalDegree_add _ _).trans_lt (max_lt h1 h2)
      omega
    have hdiff (i : Fin 4) : fiveFiber N ∣ P i - P' i := by
      refine ⟨Q i, ?_⟩
      dsimp only [P']
      ring
    have hpowdiff : fiveFiber N ∣ (∑ i, P i ^ 4) - ∑ i, P' i ^ 4 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.dvd_sum
      intro i _
      exact (hdiff i).trans (sub_dvd_pow_sub_pow (P i) (P' i) 4)
    have hnorm' : fiveFiber N ∣ (∑ i, P' i ^ 4) - MvPolynomial.C c := by
      have hh := dvd_sub hnorm hpowdiff
      convert hh using 1; ring
    obtain ⟨b, hb⟩ := ih (D - 1) (by omega) P' N c hP'deg hnorm'
    refine ⟨b, fun i ↦ ?_⟩
    have hh := dvd_add (hdiff i) (hb i)
    convert hh using 1; ring

/-- The degree-free version of polynomial fixed-fiber rigidity. -/
theorem fiveFiber_constant_mod (P : Fin 4 → MVFive) (N c : GaussianField)
    (h : fiveFiber N ∣ (∑ i, P i ^ 4) - MvPolynomial.C c) :
    ∃ b : Fin 4 → GaussianField, ∀ i, fiveFiber N ∣ P i - MvPolynomial.C (b i) := by
  classical
  exact fiveFiber_constant_mod_degree (Finset.univ.sup (fun i ↦ (P i).totalDegree))
    P N c (fun i ↦ Finset.le_sup (f := fun i ↦ (P i).totalDegree) (Finset.mem_univ i)) h

/-- Evaluation of the fixed-fiber congruence. -/
theorem fiveFiber_constant_values (P : Fin 4 → MVFive) (N c : GaussianField)
    (h : fiveFiber N ∣ (∑ i, P i ^ 4) - MvPolynomial.C c) :
    ∃ b : Fin 4 → GaussianField, ∀ x : Fin 5 → GaussianField,
      (∑ j, x j ^ 4) = N → ∀ i, MvPolynomial.eval x (P i) = b i := by
  obtain ⟨b, hb⟩ := fiveFiber_constant_mod P N c h
  refine ⟨b, fun x hx i ↦ ?_⟩
  obtain ⟨Q, hQ⟩ := hb i
  have hh := congrArg (MvPolynomial.eval x) hQ
  have hf : MvPolynomial.eval x (fiveFiber N) = 0 := by
    simp only [fiveFiber, mvFiveNorm, map_sub, map_sum, map_pow,
      MvPolynomial.eval_X, MvPolynomial.eval_C, hx, sub_self]
  simp only [map_sub, map_mul, MvPolynomial.eval_C, hf, zero_mul] at hh
  exact sub_eq_zero.mp hh

lemma fiveFiber_dvd_polynomial_value (H : Polynomial GaussianField) (N : GaussianField) :
    fiveFiber N ∣ Polynomial.eval₂ MvPolynomial.C mvFiveNorm H - MvPolynomial.C (H.eval N) := by
  have hh := map_dvd (Polynomial.eval₂RingHom MvPolynomial.C mvFiveNorm)
    (Polynomial.X_sub_C_dvd_sub_C_eval (p := H) (a := N))
  simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_C, fiveFiber] using hh

/-- An arbitrary polynomial target H(F), rather than only a monomial target,
forces constancy on every Gaussian source norm fiber. -/
theorem gaussian_polynomial_target_constant_on_levels
    (P : Fin 4 → MVFive) (H : Polynomial GaussianField)
    (h : ∑ i, P i ^ 4 = Polynomial.eval₂ MvPolynomial.C mvFiveNorm H)
    (x y : Fin 5 → GaussianField) (hxy : ∑ j, x j ^ 4 = ∑ j, y j ^ 4)
    (i : Fin 4) : MvPolynomial.eval x (P i) = MvPolynomial.eval y (P i) := by
  let N := ∑ j, x j ^ 4
  have hd : fiveFiber N ∣ (∑ i, P i ^ 4) - MvPolynomial.C (H.eval N) := by
    rw [h]
    exact fiveFiber_dvd_polynomial_value H N
  obtain ⟨b, hb⟩ := fiveFiber_constant_values P N (H.eval N) hd
  exact (hb x rfl i).trans (hb y hxy.symm i).symm

end
end Erdos322Research.QuarticFormalSpecialization
