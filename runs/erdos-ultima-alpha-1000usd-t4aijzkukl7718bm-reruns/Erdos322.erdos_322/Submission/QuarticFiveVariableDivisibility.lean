import Submission.QuarticFormalSpecialization

/-! All-degree divisibility by the five-variable quartic norm, proved by
formal specialization at a Gaussian point. No representation-count bound
is asserted here. -/
namespace Erdos322Research.QuarticFormalSpecialization
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0

abbrev FivePoly := Polynomial FourPoly

/-- Four variables are coefficients and the fifth is the polynomial variable. -/
def fourNorm : FourPoly := ∑ j : Fin 4, MvPolynomial.X j ^ 4
def fiveNorm : FivePoly := Polynomial.X ^ 4 + Polynomial.C fourNorm

def gaussianI : GaussianField :=
  algebraMap GaussianInt GaussianField Zsqrtd.sqrtd

lemma gaussianI_sq : gaussianI ^ 2 = -1 := by
  dsimp only [gaussianI]
  rw [← map_pow]
  simpa only [map_neg, map_one] using congrArg (algebraMap GaussianInt GaussianField)
      (show (Zsqrtd.sqrtd : GaussianInt) ^ 2 = -1 by simp [pow_two, Zsqrtd.dmuld])

private def polynomialShift : FourPoly →+* Polynomial FourPoly :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun j ↦ 1 + Polynomial.X * Polynomial.C (MvPolynomial.X j))

private def shiftBack : Polynomial FourPoly →+* FourPoly :=
  (MvPolynomial.eval₂Hom MvPolynomial.C (fun j ↦ MvPolynomial.X j - 1)).comp
    (Polynomial.evalRingHom 1)

private lemma shiftBack_polynomialShift (P : FourPoly) :
    shiftBack (polynomialShift P) = P := by
  have he : shiftBack.comp polynomialShift = RingHom.id FourPoly := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [shiftBack, polynomialShift]
    · intro j
      simp [shiftBack, polynomialShift]
  exact congrArg (fun f : FourPoly →+* FourPoly ↦ f P) he

/-- Independent formal directions through the point `(1,1,1,1)`. -/
def formalShift : FourPoly →+* PowerSeries FourPoly :=
  Polynomial.coeToPowerSeries.ringHom.comp polynomialShift

lemma formalShift_injective : Function.Injective formalShift := by
  intro P Q h
  have hp : polynomialShift P = polynomialShift Q :=
    Polynomial.coe_injective FourPoly h
  have hh := congrArg shiftBack hp
  simpa only [shiftBack_polynomialShift] using hh

@[simp] lemma formalShift_X (j : Fin 4) :
    formalShift (MvPolynomial.X j) =
      1 + PowerSeries.X * PowerSeries.C (MvPolynomial.X j) := by
  simp [formalShift, polynomialShift]
  ring

@[simp] lemma formalShift_C (c : GaussianField) :
    formalShift (MvPolynomial.C c) = PowerSeries.C (MvPolynomial.C c) := by
  simp [formalShift, polynomialShift]

lemma constantCoeff_formalShift_norm :
    PowerSeries.constantCoeff (formalShift fourNorm) = 4 := by
  simp [fourNorm]

private def seriesI : PowerSeries FourPoly :=
  PowerSeries.C (MvPolynomial.C gaussianI)

private lemma seriesI_sq : seriesI ^ 2 = -1 := by
  simp only [seriesI, ← map_pow, gaussianI_sq, map_neg, map_one]

/-- A formal fourth root of the negative shifted four-variable norm. -/
lemma exists_formal_root :
    ∃ y : PowerSeries FourPoly, y ^ 4 = -formalShift fourNorm ∧ y ≠ 0 := by
  let u : PowerSeries FourPoly :=
    PowerSeries.C (MvPolynomial.C (1 / 4 : GaussianField)) * formalShift fourNorm - 1
  have hu : PowerSeries.constantCoeff u = 0 := by
    have hc := congrArg (MvPolynomial.C : GaussianField →+* FourPoly)
      (show (1 / 4 : GaussianField) * 4 - 1 = 0 by norm_num)
    simpa only [u, map_sub, map_mul, map_one, PowerSeries.constantCoeff_C,
      constantCoeff_formalShift_norm, map_ofNat, map_zero] using hc
  obtain ⟨b, hb⟩ := fourth_root_one_add u hu
  let y := (1 + seriesI) * b
  have hI : (1 + seriesI) ^ 4 = (-4 : PowerSeries FourPoly) := by
    linear_combination (seriesI ^ 2 + 4 * seriesI + 5) * seriesI_sq
  have hy : y ^ 4 = -formalShift fourNorm := by
    dsimp only [y]
    rw [mul_pow, hI, hb]
    dsimp only [u]
    have hc : (4 : PowerSeries FourPoly) *
        PowerSeries.C (MvPolynomial.C (1 / 4 : GaussianField)) = 1 := by
      have hh := congrArg (PowerSeries.C.comp
        (MvPolynomial.C : GaussianField →+* FourPoly))
        (show (4 : GaussianField) * (1 / 4) = 1 by norm_num)
      simpa only [map_mul, map_ofNat, map_one, RingHom.comp_apply] using hh
    linear_combination -hc * formalShift fourNorm
  refine ⟨y, hy, ?_⟩
  intro hz
  have hh := congrArg PowerSeries.constantCoeff hy
  rw [hz] at hh
  norm_num [constantCoeff_formalShift_norm] at hh

private def gaussianUnits : Fin 4 → GaussianInt :=
  ![1, -1, Zsqrtd.sqrtd, -Zsqrtd.sqrtd]

private lemma gaussianUnits_injective : Function.Injective gaussianUnits := by
  decide

private lemma gaussianUnits_fourth : ∀ j, gaussianUnits j ^ 4 = 1 := by
  decide

private def gaussianScalar : GaussianInt →+* PowerSeries FourPoly :=
  PowerSeries.C.comp (MvPolynomial.C.comp (algebraMap GaussianInt GaussianField))

private lemma gaussianScalar_injective : Function.Injective gaussianScalar :=
  PowerSeries.C_injective.comp
    ((MvPolynomial.C_injective (Fin 4) GaussianField).comp
      (IsFractionRing.injective GaussianInt GaussianField))

private def fourRoots (y : PowerSeries FourPoly) (j : Fin 4) : PowerSeries FourPoly :=
  gaussianScalar (gaussianUnits j) * y

private lemma fourRoots_injective (y : PowerSeries FourPoly) (hy : y ≠ 0) :
    Function.Injective (fourRoots y) := by
  intro j k h
  exact gaussianUnits_injective (gaussianScalar_injective (mul_right_cancel₀ hy h))

private lemma fourRoots_fourth (y : PowerSeries FourPoly) (j : Fin 4) :
    fourRoots y j ^ 4 = y ^ 4 := by
  simp only [fourRoots, mul_pow, ← map_pow, gaussianUnits_fourth, map_one, one_mul]

lemma fiveNorm_monic : fiveNorm.Monic :=
  Polynomial.monic_X_pow_add_C _ (by decide : 4 ≠ 0)

lemma fiveNorm_degree : fiveNorm.natDegree = 4 :=
  Polynomial.natDegree_X_pow_add_C

lemma fiveNorm_ne_one : fiveNorm ≠ 1 := by
  intro h
  have hh := congrArg Polynomial.natDegree h
  rw [fiveNorm_degree, Polynomial.natDegree_one] at hh
  omega

private lemma eval_fiveNorm_root (y : PowerSeries FourPoly)
    (hy : y ^ 4 = -formalShift fourNorm) (j : Fin 4) :
    Polynomial.eval₂RingHom formalShift (fourRoots y j) fiveNorm = 0 := by
  change Polynomial.eval₂ formalShift (fourRoots y j) fiveNorm = 0
  simp only [fiveNorm, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, fourRoots_fourth, hy, neg_add_cancel]

/-- Divisibility by the five-variable quartic norm forces coordinatewise
    divisibility, at every degree, for four Gaussian-coefficient fourth powers. -/
theorem fiveNorm_dvd_all (P : Fin 4 → FivePoly)
    (h : fiveNorm ∣ ∑ i, P i ^ 4) : ∀ i, fiveNorm ∣ P i := by
  obtain ⟨y, hy, hy0⟩ := exists_formal_root
  have heval (j : Fin 4) (i : Fin 4) :
      Polynomial.eval₂RingHom formalShift (fourRoots y j) (P i) = 0 := by
    apply fourPoly_series_anisotropic
      (fun l ↦ Polynomial.eval₂RingHom formalShift (fourRoots y j) (P l)) ?_ i
    obtain ⟨Q, hQ⟩ := h
    have hh := congrArg (Polynomial.eval₂RingHom formalShift (fourRoots y j)) hQ
    simpa only [map_sum, map_pow, map_mul, eval_fiveNorm_root y hy j,
      zero_mul] using hh
  intro i
  apply (Polynomial.modByMonic_eq_zero_iff_dvd fiveNorm_monic).mp
  let r := P i %ₘ fiveNorm
  have hr : r.natDegree < 4 := by
    simpa only [fiveNorm_degree] using
      Polynomial.natDegree_modByMonic_lt (P i) fiveNorm_monic fiveNorm_ne_one
  have hz : Polynomial.map formalShift r = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Polynomial.map formalShift r) (fourRoots_injective y hy0)
    · intro j
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_modByMonic_eq_self_of_root fiveNorm_monic
        (eval_fiveNorm_root y hy j)).trans (heval j i)
    · exact (Polynomial.natDegree_map_le).trans_lt (by simpa using hr)
  apply Polynomial.map_injective formalShift formalShift_injective
  simpa using hz

/-- The corresponding divisibility for arbitrary powers follows by descent. -/
theorem fiveNorm_power_dvd_all (m : ℕ) (P : Fin 4 → FivePoly)
    (h : fiveNorm ^ (4 * m) ∣ ∑ i, P i ^ 4) :
    ∀ i, fiveNorm ^ m ∣ P i := by
  induction m generalizing P with
  | zero => simp
  | succ m ih =>
    have hd : fiveNorm ∣ ∑ i, P i ^ 4 :=
      (dvd_pow_self fiveNorm (by omega : 4 * (m + 1) ≠ 0)).trans h
    obtain ⟨Q, hQ⟩ := Classical.axiomOfChoice (fiveNorm_dvd_all P hd)
    have he : (∑ i, P i ^ 4) = fiveNorm ^ 4 * (∑ i, Q i ^ 4) := by
      simp only [hQ, mul_pow, Finset.mul_sum]
    have hc : fiveNorm ^ (4 * m) ∣ ∑ i, Q i ^ 4 := by
      rw [he, show 4 * (m + 1) = 4 + 4 * m by omega, pow_add] at h
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ fiveNorm_monic.ne_zero)).mp h
    intro i
    rw [hQ i, pow_succ']
    exact mul_dvd_mul_left _ (ih Q hc i)

end
end Erdos322Research.QuarticFormalSpecialization
