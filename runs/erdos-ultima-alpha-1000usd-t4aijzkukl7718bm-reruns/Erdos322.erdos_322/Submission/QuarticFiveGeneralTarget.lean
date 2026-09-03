import Submission.QuarticFiveFixedPolynomialFiber

/-! Polynomial targets H(F) in five-input quartic transfers. These are
construction-rigidity results, not estimates for unrestricted representation counts. -/
namespace Erdos322Research.QuarticFormalSpecialization
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0

private abbrev coeffMap5 : MvPolynomial (Fin 5) ℚ →+* MVFive :=
  MvPolynomial.map (Rat.castHom GaussianField)

private lemma coeffMap5_norm : coeffMap5 rationalFiveNorm = mvFiveNorm := by
  simp [rationalFiveNorm, mvFiveNorm]

private lemma coeffMap5_coefficients :
    coeffMap5.comp MvPolynomial.C = MvPolynomial.C.comp (Rat.castHom GaussianField) := by
  ext c
  simp

private lemma coeffMap5_eval (P : MvPolynomial (Fin 5) ℚ) (x : Fin 5 → ℚ) :
    MvPolynomial.eval (fun j ↦ (x j : GaussianField)) (coeffMap5 P) =
      (MvPolynomial.eval x P : GaussianField) := by
  exact (MvPolynomial.map_eval (Rat.castHom GaussianField) x P).symm

/-- Polynomial congruence on one fixed rational source fiber suffices for
constancy of the output coordinates on that fiber. -/
theorem rational_fixed_polynomial_fiber_constant
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (N c : ℚ)
    (h : rationalFiveNorm - MvPolynomial.C N ∣ (∑ i, P i ^ 4) - MvPolynomial.C c)
    (x y : Fin 5 → ℚ) (hx : ∑ j, x j ^ 4 = N) (hy : ∑ j, y j ^ 4 = N)
    (i : Fin 4) : MvPolynomial.eval x (P i) = MvPolynomial.eval y (P i) := by
  have hd := map_dvd coeffMap5 h
  simp only [map_sub, map_sum, map_pow, MvPolynomial.map_C, coeffMap5_norm] at hd
  change fiveFiber (N : GaussianField) ∣
    (∑ i, coeffMap5 (P i) ^ 4) - MvPolynomial.C (c : GaussianField) at hd
  obtain ⟨b, hb⟩ := fiveFiber_constant_values (fun i ↦ coeffMap5 (P i)) _ _ hd
  have hxc : ∑ j, (x j : GaussianField) ^ 4 = (N : GaussianField) := by exact_mod_cast hx
  have hyc : ∑ j, (y j : GaussianField) ^ 4 = (N : GaussianField) := by exact_mod_cast hy
  have hh := (hb (fun j ↦ (x j : GaussianField)) hxc i).trans
    (hb (fun j ↦ (y j : GaussianField)) hyc i).symm
  rw [coeffMap5_eval, coeffMap5_eval] at hh
  exact_mod_cast hh

/-- The full polynomial-target version: no degree, homogeneity, or monomial
restriction on H is required. -/
theorem rational_polynomial_target_constant_on_levels
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i ^ 4 = Polynomial.eval₂ MvPolynomial.C rationalFiveNorm H)
    (x y : Fin 5 → ℚ) (hxy : ∑ j, x j ^ 4 = ∑ j, y j ^ 4) (i : Fin 4) :
    MvPolynomial.eval x (P i) = MvPolynomial.eval y (P i) := by
  have hg : ∑ i, coeffMap5 (P i) ^ 4 =
      Polynomial.eval₂ MvPolynomial.C mvFiveNorm (H.map (Rat.castHom GaussianField)) := by
    have hh := congrArg coeffMap5 h
    simp only [map_sum, map_pow, Polynomial.hom_eval₂, coeffMap5_coefficients,
      coeffMap5_norm] at hh
    rw [Polynomial.eval₂_map]
    exact hh
  have hxy' : ∑ j, (x j : GaussianField) ^ 4 = ∑ j, (y j : GaussianField) ^ 4 := by
    exact_mod_cast hxy
  have hh := gaussian_polynomial_target_constant_on_levels
    (fun i ↦ coeffMap5 (P i)) _ hg (fun j ↦ (x j : GaussianField))
    (fun j ↦ (y j : GaussianField)) hxy' i
  rw [coeffMap5_eval, coeffMap5_eval] at hh
  exact_mod_cast hh

/-- An explicit output-multiplicity statement for arbitrary polynomial targets. -/
theorem rational_polynomial_target_image_card_le_one
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i ^ 4 = Polynomial.eval₂ MvPolynomial.C rationalFiveNorm H)
    (S : Finset (Fin 5 → ℚ)) (N : ℚ) (hS : ∀ x ∈ S, ∑ j, x j ^ 4 = N) :
    (S.image (fun x i ↦ MvPolynomial.eval x (P i))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  funext i
  exact rational_polynomial_target_constant_on_levels P H h x y
    ((hS x hx).trans (hS y hy).symm) i

def targetEval : Polynomial ℚ →+* MvPolynomial (Fin 5) ℚ :=
  Polynomial.eval₂RingHom MvPolynomial.C rationalFiveNorm

lemma eval_targetEval (H : Polynomial ℚ) (x : Fin 5 → ℚ) :
    MvPolynomial.eval x (targetEval H) = H.eval (∑ j, x j ^ 4) := by
  change MvPolynomial.eval x (Polynomial.eval₂ MvPolynomial.C rationalFiveNorm H) = _
  rw [Polynomial.hom_eval₂]
  have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℚ := by
    ext c
    simp
  rw [hc]
  simp only [rationalFiveNorm, map_sum, map_pow, MvPolynomial.eval_X,
    Polynomial.eval₂_id]

/-- Polynomial multipliers in the source norm can be allowed on the left
as well, at every level where the multiplier does not vanish. -/
theorem rational_weighted_target_constant_on_levels
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (L H : Polynomial ℚ)
    (h : targetEval L * (∑ i, P i ^ 4) = targetEval H)
    (x y : Fin 5 → ℚ) (hxy : ∑ j, x j ^ 4 = ∑ j, y j ^ 4)
    (hL : L.eval (∑ j, x j ^ 4) ≠ 0) (i : Fin 4) :
    MvPolynomial.eval x (P i) = MvPolynomial.eval y (P i) := by
  let Q (i : Fin 4) := targetEval L * P i
  have hQ : ∑ i, Q i ^ 4 = targetEval (L ^ 3 * H) := by
    simp only [Q, mul_pow, ← Finset.mul_sum, map_mul, map_pow]
    calc
      targetEval L ^ 4 * (∑ i, P i ^ 4) =
          targetEval L ^ 3 * (targetEval L * (∑ i, P i ^ 4)) := by ring
      _ = _ := by rw [h]
  have hh := rational_polynomial_target_constant_on_levels Q (L ^ 3 * H) hQ x y hxy i
  simp only [Q, map_mul, eval_targetEval] at hh
  rw [← hxy] at hh
  exact mul_left_cancel₀ hL hh

/-- A rational constant-norm identity with an arbitrary polynomial denominator
D(F) is constant on each source norm fiber away from its poles. The identity
need only be assumed at rational inputs where the denominator is nonzero. -/
theorem rational_norm_denominator_constant_on_levels
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (D : Polynomial ℚ) (c : ℚ)
    (h : ∀ z : Fin 5 → ℚ, D.eval (∑ j, z j ^ 4) ≠ 0 →
      (∑ i, (MvPolynomial.eval z (P i) / D.eval (∑ j, z j ^ 4)) ^ 4) = c)
    (x y : Fin 5 → ℚ) (hxy : ∑ j, x j ^ 4 = ∑ j, y j ^ 4)
    (hDx : D.eval (∑ j, x j ^ 4) ≠ 0) (i : Fin 4) :
    MvPolynomial.eval x (P i) / D.eval (∑ j, x j ^ 4) =
      MvPolynomial.eval y (P i) / D.eval (∑ j, y j ^ 4) := by
  let A : MvPolynomial (Fin 5) ℚ :=
    (∑ i, P i ^ 4) - MvPolynomial.C c * targetEval D ^ 4
  have hD0 : targetEval D ≠ 0 := by
    intro hz
    have hh := congrArg (MvPolynomial.eval x) hz
    rw [eval_targetEval, map_zero] at hh
    exact hDx hh
  have hz : targetEval D * A = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, map_zero, eval_targetEval]
    by_cases hd : D.eval (∑ j, z j ^ 4) = 0
    · rw [hd, zero_mul]
    · have hh := h z hd
      simp only [div_pow, ← Finset.sum_div] at hh
      have he := (div_eq_iff (pow_ne_zero 4 hd)).mp hh
      have ha : MvPolynomial.eval z A = 0 := by
        simp only [A, map_sub, map_sum, map_pow, map_mul, MvPolynomial.eval_C,
          eval_targetEval, he, sub_self]
      rw [ha, mul_zero]
  have hA : A = 0 := (mul_eq_zero.mp hz).resolve_left hD0
  have hp : (∑ i, P i ^ 4) = targetEval (Polynomial.C c * D ^ 4) := by
    have hh := sub_eq_zero.mp hA
    change (∑ i, P i ^ 4) = _ at hh
    simpa only [map_mul, map_pow, targetEval, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C] using hh
  have hh := rational_polynomial_target_constant_on_levels P (Polynomial.C c * D ^ 4)
    hp x y hxy i
  rw [hh, hxy]

end
end Erdos322Research.QuarticFormalSpecialization
