import Submission.QuarticFiveVariableDivisibility

/-! All-degree polynomial transfers from five fourth powers to four.
The only norm-power transfers are radial. This does not bound all integer
representations and does not settle the conjecture in `Submission.Spec`. -/
namespace Erdos322Research.QuarticFormalSpecialization
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0

/-- Classification at every surviving power exponent, in the polynomial tower. -/
theorem fiveNorm_transfer_radial (P : Fin 4 → FivePoly) (c : GaussianField) (m : ℕ)
    (h : ∑ i, P i ^ 4 = Polynomial.C (MvPolynomial.C c) * fiveNorm ^ (4 * m)) :
    ∃ b : Fin 4 → GaussianField,
      (∀ i, P i = Polynomial.C (MvPolynomial.C (b i)) * fiveNorm ^ m) ∧
      ∑ i, b i ^ 4 = c := by
  have hd : fiveNorm ^ (4 * m) ∣ ∑ i, P i ^ 4 := by
    rw [h]
    exact dvd_mul_left _ _
  have hd' := fiveNorm_power_dvd_all m P hd
  choose Q hQ using hd'
  have hn : ∑ i, Q i ^ 4 = Polynomial.C (MvPolynomial.C c) := by
    apply mul_left_cancel₀ (pow_ne_zero (4 * m) fiveNorm_monic.ne_zero)
    calc
      fiveNorm ^ (4 * m) * (∑ i, Q i ^ 4) = ∑ i, P i ^ 4 := by
        simp only [hQ, mul_pow, ← pow_mul, Finset.mul_sum]
        rw [Nat.mul_comm m 4]
      _ = fiveNorm ^ (4 * m) * Polynomial.C (MvPolynomial.C c) := by
        rw [h, mul_comm]
  have hconst := polynomial_constant_norm fourPoly_anisotropic Q (MvPolynomial.C c) hn
  let a (i : Fin 4) := (Q i).coeff 0
  have ha : ∑ i, a i ^ 4 = MvPolynomial.C c := by
    have hh := congrArg Polynomial.constantCoeff hn
    simpa only [map_sum, map_pow, Polynomial.constantCoeff_apply,
      Polynomial.coeff_C_zero] using hh
  have hb := mvPolynomial_constant_norm gaussian_anisotropic a c ha
  let b (i : Fin 4) := MvPolynomial.eval (fun _ ↦ 0) (a i)
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hQ i, hconst i]
    change fiveNorm ^ m * Polynomial.C (a i) = _
    rw [hb i]
    ring
  · have hh := congrArg (MvPolynomial.eval (fun _ : Fin 4 ↦ (0 : GaussianField))) ha
    simpa only [map_sum, map_pow, MvPolynomial.eval_C] using hh

/-- The Gaussian multivariate norm. -/
def mvFiveNorm : MvPolynomial (Fin 5) GaussianField :=
  ∑ j : Fin 5, MvPolynomial.X j ^ 4

lemma finSucc_fiveNorm : MvPolynomial.finSuccEquiv GaussianField 4 mvFiveNorm = fiveNorm := by
  rw [MvPolynomial.finSuccEquiv_apply]
  simp [mvFiveNorm, fiveNorm, fourNorm, Fin.sum_univ_succ]
  rfl

lemma finSucc_constant (c : GaussianField) :
    MvPolynomial.finSuccEquiv GaussianField 4 (MvPolynomial.C c) =
      Polynomial.C (MvPolynomial.C c) := by
  simp [MvPolynomial.finSuccEquiv_apply]

/-- Arbitrary-degree Gaussian polynomial norm-power transfers are radial. -/
theorem gaussian_mv_transfer_radial
    (P : Fin 4 → MvPolynomial (Fin 5) GaussianField) (c : GaussianField) (m : ℕ)
    (h : ∑ i, P i ^ 4 = MvPolynomial.C c * mvFiveNorm ^ (4 * m)) :
    ∃ b : Fin 4 → GaussianField,
      (∀ i, P i = MvPolynomial.C (b i) * mvFiveNorm ^ m) ∧
      ∑ i, b i ^ 4 = c := by
  let E := MvPolynomial.finSuccEquiv GaussianField 4
  have he : ∑ i, E (P i) ^ 4 = Polynomial.C (MvPolynomial.C c) * fiveNorm ^ (4 * m) := by
    have hh := congrArg E.toRingHom h
    simp only [map_sum, map_pow, map_mul] at hh
    change ∑ i, E (P i) ^ 4 = E (MvPolynomial.C c) * E mvFiveNorm ^ (4 * m) at hh
    rw [finSucc_constant, finSucc_fiveNorm] at hh
    exact hh
  obtain ⟨b, hb, hc⟩ := fiveNorm_transfer_radial (fun i ↦ E (P i)) c m he
  refine ⟨b, fun i ↦ E.injective ?_, hc⟩
  change E.toRingHom (P i) = E.toRingHom (MvPolynomial.C (b i) * mvFiveNorm ^ m)
  rw [map_mul, map_pow]
  change E (P i) = E (MvPolynomial.C (b i)) * E mvFiveNorm ^ m
  rw [finSucc_constant, finSucc_fiveNorm]
  exact hb i

/-- A nonzero norm-power transfer necessarily has exponent divisible by four. -/
theorem fiveNorm_transfer_exponent (e : ℕ) :
    ∀ (P : Fin 4 → FivePoly) (c : GaussianField), c ≠ 0 →
      (∑ i, P i ^ 4 = Polynomial.C (MvPolynomial.C c) * fiveNorm ^ e) → 4 ∣ e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro P c hc h
    by_cases he : e = 0
    · simp [he]
    have hd : fiveNorm ∣ ∑ i, P i ^ 4 := by
      rw [h]
      exact (dvd_pow_self fiveNorm he).trans (dvd_mul_left _ _)
    choose Q hQ using fiveNorm_dvd_all P hd
    have hEq : fiveNorm ^ 4 * (∑ i, Q i ^ 4) =
        Polynomial.C (MvPolynomial.C c) * fiveNorm ^ e := by
      simpa only [hQ, mul_pow, Finset.mul_sum] using h
    have hC : (Polynomial.C (MvPolynomial.C c) : FivePoly) ≠ 0 := by
      simpa only [ne_eq, Polynomial.C_eq_zero, MvPolynomial.C_eq_zero] using hc
    have hnorm : fiveNorm ≠ 0 := fiveNorm_monic.ne_zero
    have hsum : (∑ i, Q i ^ 4) ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hEq
      exact (mul_ne_zero hC (pow_ne_zero e hnorm)) hEq.symm
    have hdeg := congrArg Polynomial.natDegree hEq
    rw [Polynomial.natDegree_mul (pow_ne_zero 4 hnorm) hsum,
      Polynomial.natDegree_mul hC (pow_ne_zero e hnorm),
      Polynomial.natDegree_pow, Polynomial.natDegree_pow, fiveNorm_degree,
      Polynomial.natDegree_C] at hdeg
    have he4 : 4 ≤ e := by omega
    have hnext : ∑ i, Q i ^ 4 =
        Polynomial.C (MvPolynomial.C c) * fiveNorm ^ (e - 4) := by
      apply mul_left_cancel₀ (pow_ne_zero 4 hnorm)
      rw [hEq, show e = 4 + (e - 4) by omega, pow_add]
      simp only [Nat.add_sub_cancel_left]
      ring
    have hh := ih (e - 4) (by omega) Q c hc hnext
    omega

lemma gaussian_mv_transfer_exponent
    (P : Fin 4 → MvPolynomial (Fin 5) GaussianField) (c : GaussianField)
    (e : ℕ) (hc : c ≠ 0)
    (h : ∑ i, P i ^ 4 = MvPolynomial.C c * mvFiveNorm ^ e) : 4 ∣ e := by
  let E := MvPolynomial.finSuccEquiv GaussianField 4
  have hh := congrArg E.toRingHom h
  simp only [map_sum, map_pow, map_mul] at hh
  change ∑ i, E (P i) ^ 4 = E (MvPolynomial.C c) * E mvFiveNorm ^ e at hh
  rw [finSucc_constant, finSucc_fiveNorm] at hh
  exact fiveNorm_transfer_exponent e (fun i ↦ E (P i)) c hc hh

/-- The original rational-coefficient five-variable norm. -/
def rationalFiveNorm : MvPolynomial (Fin 5) ℚ :=
  ∑ j : Fin 5, MvPolynomial.X j ^ 4

private abbrev rationalMap : MvPolynomial (Fin 5) ℚ →+* MvPolynomial (Fin 5) GaussianField :=
  MvPolynomial.map (Rat.castHom GaussianField)

private lemma rationalMap_injective : Function.Injective rationalMap :=
  MvPolynomial.map_injective _ (Rat.castHom GaussianField).injective

private lemma rationalMap_norm : rationalMap rationalFiveNorm = mvFiveNorm := by
  simp [rationalFiveNorm, mvFiveNorm]

private def firstAxis : Fin 5 → ℚ := ![1, 0, 0, 0, 0]

private lemma rationalFiveNorm_at_axis : MvPolynomial.eval firstAxis rationalFiveNorm = 1 := by
  simp [rationalFiveNorm, firstAxis, Fin.sum_univ_succ]

private lemma rationalMap_eval (P : MvPolynomial (Fin 5) ℚ) (x : Fin 5 → ℚ) :
    MvPolynomial.eval (fun j ↦ (x j : GaussianField)) (rationalMap P) =
      (MvPolynomial.eval x P : GaussianField) := by
  exact (MvPolynomial.map_eval (Rat.castHom GaussianField) x P).symm

/-- Every polynomial transfer at every multiple-of-four exponent is radial.
No homogeneity or numerator-degree hypothesis is needed. -/
theorem rational_transfer_radial
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (c : ℚ) (m : ℕ)
    (h : ∑ i, P i ^ 4 = MvPolynomial.C c * rationalFiveNorm ^ (4 * m)) :
    ∃ b : Fin 4 → ℚ,
      (∀ i, P i = MvPolynomial.C (b i) * rationalFiveNorm ^ m) ∧
      ∑ i, b i ^ 4 = c := by
  have hg : ∑ i, rationalMap (P i) ^ 4 =
      MvPolynomial.C (c : GaussianField) * mvFiveNorm ^ (4 * m) := by
    have hh := congrArg rationalMap h
    simpa only [map_sum, map_pow, map_mul, MvPolynomial.map_C, rationalMap_norm] using hh
  obtain ⟨b, hb, hc⟩ := gaussian_mv_transfer_radial (fun i ↦ rationalMap (P i)) _ m hg
  let a (i : Fin 4) : ℚ := MvPolynomial.eval firstAxis (P i)
  have hab (i : Fin 4) : (a i : GaussianField) = b i := by
    have hh := congrArg (MvPolynomial.eval (fun j ↦ (firstAxis j : GaussianField))) (hb i)
    rw [rationalMap_eval] at hh
    have hn : MvPolynomial.eval (fun j ↦ (firstAxis j : GaussianField)) mvFiveNorm = 1 := by
      rw [← rationalMap_norm, rationalMap_eval, rationalFiveNorm_at_axis]
      simp
    simpa only [map_mul, map_pow, MvPolynomial.eval_C, hn, one_pow, mul_one] using hh
  refine ⟨a, ?_, ?_⟩
  · intro i
    apply rationalMap_injective
    rw [hb i, map_mul, map_pow, rationalMap_norm, MvPolynomial.map_C]
    change MvPolynomial.C (b i) * mvFiveNorm ^ m =
      MvPolynomial.C (a i : GaussianField) * mvFiveNorm ^ m
    rw [hab i]
  · have hh : ((∑ i, a i ^ 4 : ℚ) : GaussianField) = (c : GaussianField) := by
      push_cast
      simpa only [hab] using hc
    exact_mod_cast hh

/-- Complete classification at arbitrary exponent and nonzero multiplier. -/
theorem rational_transfer_iff (P : Fin 4 → MvPolynomial (Fin 5) ℚ)
    (c : ℚ) (e : ℕ) (hc : c ≠ 0) :
    (∑ i, P i ^ 4 = MvPolynomial.C c * rationalFiveNorm ^ e) ↔
      ∃ (m : ℕ) (b : Fin 4 → ℚ), e = 4 * m ∧
        (∀ i, P i = MvPolynomial.C (b i) * rationalFiveNorm ^ m) ∧
        ∑ i, b i ^ 4 = c := by
  constructor
  · intro h
    have hg : ∑ i, rationalMap (P i) ^ 4 =
        MvPolynomial.C (c : GaussianField) * mvFiveNorm ^ e := by
      have hh := congrArg rationalMap h
      simpa only [map_sum, map_pow, map_mul, MvPolynomial.map_C, rationalMap_norm] using hh
    have hc' : (c : GaussianField) ≠ 0 := by exact_mod_cast hc
    obtain ⟨m, hm⟩ := gaussian_mv_transfer_exponent (fun i ↦ rationalMap (P i)) _ e hc' hg
    rw [hm] at h
    obtain ⟨b, hb, hn⟩ := rational_transfer_radial P c m h
    exact ⟨m, b, hm, hb, hn⟩
  · rintro ⟨m, b, rfl, hb, hn⟩
    simp_rw [hb, mul_pow, ← map_pow, ← pow_mul]
    rw [← Finset.sum_mul, ← map_sum, hn, Nat.mul_comm m 4]

/-- Such a transfer has no variation on a fixed source norm fiber. -/
theorem rational_transfer_constant_on_levels
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (c : ℚ) (e : ℕ) (hc : c ≠ 0)
    (h : ∑ i, P i ^ 4 = MvPolynomial.C c * rationalFiveNorm ^ e)
    (x y : Fin 5 → ℚ) (hxy : ∑ j, x j ^ 4 = ∑ j, y j ^ 4) (i : Fin 4) :
    MvPolynomial.eval x (P i) = MvPolynomial.eval y (P i) := by
  obtain ⟨m, b, _, hb, _⟩ := (rational_transfer_iff P c e hc).mp h
  simp only [hb i, map_mul, map_pow, MvPolynomial.eval_C,
    rationalFiveNorm, map_sum, MvPolynomial.eval_X, hxy]

/-- Regardless of the number of source parameters, this entire family produces
at most one distinct output tuple at each source norm level. -/
theorem rational_transfer_image_card_le_one
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (c : ℚ) (e : ℕ) (hc : c ≠ 0)
    (h : ∑ i, P i ^ 4 = MvPolynomial.C c * rationalFiveNorm ^ e)
    (S : Finset (Fin 5 → ℚ)) (N : ℚ)
    (hS : ∀ x ∈ S, ∑ j, x j ^ 4 = N) :
    (S.image (fun x i ↦ MvPolynomial.eval x (P i))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  funext i
  exact rational_transfer_constant_on_levels P c e hc h x y
    ((hS x hx).trans (hS y hy).symm) i

end
end Erdos322Research.QuarticFormalSpecialization
