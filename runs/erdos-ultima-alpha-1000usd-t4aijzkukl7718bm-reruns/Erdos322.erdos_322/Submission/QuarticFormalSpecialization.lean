import Submission.GaussianQuarticObstruction

/-! Anisotropy and fourth roots in formal power series, for a local
specialization argument. These are not representation-count estimates. -/
namespace Erdos322Research.QuarticFormalSpecialization
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0

/-- Anisotropy of the diagonal form with four fourth powers. -/
def FourthAnisotropic (R : Type*) [CommRing R] : Prop :=
  ∀ a : Fin 4 → R, (∑ i, a i ^ 4) = 0 → ∀ i, a i = 0

lemma mvPolynomial_anisotropic {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    {σ : Type*} (hR : FourthAnisotropic R) :
    FourthAnisotropic (MvPolynomial σ R) := by
  intro a ha i
  apply MvPolynomial.funext
  intro x
  have hh := congrArg (MvPolynomial.eval x) ha
  simp only [map_sum, map_pow, map_zero] at hh
  simpa using hR (fun j ↦ MvPolynomial.eval x (a j)) hh i

/-- Leading-order cancellation cannot create isotropy in a power-series ring. -/
theorem powerSeries_anisotropic {R : Type*} [CommRing R] [IsDomain R]
    (hR : FourthAnisotropic R) : FourthAnisotropic (PowerSeries R) := by
  have hcoeff : ∀ n : ℕ, ∀ a : Fin 4 → PowerSeries R,
      (∑ i, a i ^ 4) = 0 → ∀ i, PowerSeries.coeff n (a i) = 0 := by
    intro n
    induction n with
    | zero =>
      intro a ha i
      have hh := congrArg PowerSeries.constantCoeff ha
      simp only [map_sum, map_pow, map_zero] at hh
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
        hR (fun j ↦ PowerSeries.constantCoeff (a j)) hh i
    | succ n ih =>
      intro a ha i
      have hc : ∀ j, PowerSeries.constantCoeff (a j) = 0 := by
        apply hR
        have hh := congrArg PowerSeries.constantCoeff ha
        simpa only [map_sum, map_pow, map_zero] using hh
      have hd : ∀ j, ∃ b : PowerSeries R, a j = PowerSeries.X * b :=
        fun j ↦ PowerSeries.X_dvd_iff.mpr (hc j)
      choose b hb using hd
      have hb0 : (∑ j, b j ^ 4) = 0 := by
        have he : PowerSeries.X ^ 4 * (∑ j, b j ^ 4) = (0 : PowerSeries R) := by
          simpa only [hb, mul_pow, Finset.mul_sum] using ha
        exact (mul_eq_zero.mp he).resolve_left
          (pow_ne_zero _ PowerSeries.X_ne_zero)
      rw [hb i, PowerSeries.coeff_succ_X_mul]
      exact ih b hb0 i
  intro a ha i
  ext n
  simpa using hcoeff n a ha i

/-- Formal fourth roots exist for series with constant coefficient one. -/
theorem fourth_root_one_add {R : Type*} [CommRing R] [Algebra ℚ R]
    (u : PowerSeries R) (hu : PowerSeries.constantCoeff u = 0) :
    ∃ b : PowerSeries R, b ^ 4 = 1 + u := by
  let b := PowerSeries.binomialSeries R (1 / 4 : ℚ)
  have hb : b ^ 4 = 1 + PowerSeries.X := by
    have h2 : b ^ 2 = PowerSeries.binomialSeries R (1 / 2 : ℚ) := by
      rw [pow_two]
      dsimp only [b]
      rw [← PowerSeries.binomialSeries_add]
      norm_num
    calc
      b ^ 4 = (b ^ 2) ^ 2 := by ring
      _ = (PowerSeries.binomialSeries R (1 / 2 : ℚ)) ^ 2 := by rw [h2]
      _ = PowerSeries.binomialSeries R (1 : ℚ) := by
        rw [pow_two]
        rw [← PowerSeries.binomialSeries_add]
        norm_num
      _ = 1 + PowerSeries.X := by
        simpa using (PowerSeries.binomialSeries_nat (R := ℚ) (A := R) 1)
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hu
  refine ⟨PowerSeries.substAlgHom hs b, ?_⟩
  have hh := congrArg (PowerSeries.substAlgHom hs) hb
  simpa only [map_pow, map_add, map_one, PowerSeries.substAlgHom_X] using hh

abbrev GaussianField := GaussianQuartic.GaussianRational
abbrev FourPoly := MvPolynomial (Fin 4) GaussianField

lemma gaussian_anisotropic : FourthAnisotropic GaussianField :=
  GaussianQuartic.gaussian_rational_fourth_sum_zero

lemma fourPoly_anisotropic : FourthAnisotropic FourPoly :=
  mvPolynomial_anisotropic gaussian_anisotropic

lemma fourPoly_series_anisotropic : FourthAnisotropic (PowerSeries FourPoly) :=
  powerSeries_anisotropic fourPoly_anisotropic

/-- A constant norm has no nonconstant polynomial coordinates over an
anisotropic coefficient domain. -/
theorem polynomial_constant_norm {R : Type*} [CommRing R] [IsDomain R]
    (hR : FourthAnisotropic R) (P : Fin 4 → Polynomial R) (c : R)
    (h : ∑ i, P i ^ 4 = Polynomial.C c) :
    ∀ i, P i = Polynomial.C ((P i).coeff 0) := by
  classical
  intro i
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hn
  let D := Finset.univ.sup (fun j ↦ (P j).natDegree)
  have hDi : (P i).natDegree ≤ D := Finset.le_sup (f := fun j ↦ (P j).natDegree)
    (Finset.mem_univ i)
  have hDpos : 0 < D := by omega
  have hD (j : Fin 4) : (P j).natDegree ≤ D :=
    Finset.le_sup (f := fun j ↦ (P j).natDegree) (Finset.mem_univ j)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨i⟩) (fun j ↦ (P j).natDegree)
  change D = (P j).natDegree at hj
  have hp : P j ≠ 0 := by
    intro hz
    simp [hz] at hj
    omega
  have hc : (P j).coeff D ≠ 0 := by
    rw [hj, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have he : (∑ j, P j ^ 4).coeff (4 * D) = ∑ j, (P j).coeff D ^ 4 := by
    simp only [Polynomial.finset_sum_coeff]
    exact Finset.sum_congr rfl (fun j _ ↦ Polynomial.coeff_pow_of_natDegree_le (hD j))
  have hs : (∑ j, (P j).coeff D ^ 4) = 0 := by
    rw [← he, h]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simpa using (show 0 < 4 * D by omega))
  exact hc (hR (fun j ↦ (P j).coeff D) hs j)

/-- The corresponding multivariate statement, without a degree restriction. -/
theorem mvPolynomial_constant_norm {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    {σ : Type*} (hR : FourthAnisotropic R) (P : Fin 4 → MvPolynomial σ R) (c : R)
    (h : ∑ i, P i ^ 4 = MvPolynomial.C c) :
    ∀ i, P i = MvPolynomial.C (MvPolynomial.eval (fun _ ↦ 0) (P i)) := by
  let L (x : σ → R) : MvPolynomial σ R →+* Polynomial R :=
    MvPolynomial.eval₂Hom Polynomial.C (fun j ↦ Polynomial.C (x j) * Polynomial.X)
  have hev (x : σ → R) (t : R) (p : MvPolynomial σ R) :
      (L x p).eval t = MvPolynomial.eval (fun j ↦ x j * t) p := by
    have he : (Polynomial.evalRingHom t).comp (L x) =
        MvPolynomial.eval (fun j ↦ x j * t) := by
      apply MvPolynomial.ringHom_ext <;> intro j <;> simp [L]
    exact congrArg (fun f : MvPolynomial σ R →+* R ↦ f p) he
  intro i
  apply MvPolynomial.funext
  intro x
  have hh : ∑ j, (L x (P j)) ^ 4 = Polynomial.C c := by
    have he := congrArg (L x) h
    simpa [L] using he
  have hp := polynomial_constant_norm hR (fun j ↦ L x (P j)) c hh i
  have h1 := congrArg (Polynomial.evalRingHom (1 : R)) hp
  have h0 := congrArg (Polynomial.evalRingHom (0 : R)) hp
  simp only [Polynomial.coe_evalRingHom, hev, mul_one, mul_zero,
    Polynomial.eval_C] at h1 h0
  simpa using h1.trans h0.symm

end
end Erdos322Research.QuarticFormalSpecialization
