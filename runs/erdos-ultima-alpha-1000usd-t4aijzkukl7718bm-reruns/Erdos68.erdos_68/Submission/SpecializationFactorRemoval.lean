import FormalConjecturesUtil

/-! Removing powers of z-1 preserves formal vanishing at zero and removes
identically zero specialization. No nonvanishing at a specific real root
or small-value family is asserted. The outer polynomial variable is z. -/

namespace SpecializationFactorRemoval

open Polynomial

lemma remove_specialization_factor {R : Type*} [CommRing R] [IsDomain R]
    (P : R[X]) (hP : P ≠ 0) :
    ∃ k : ℕ, ∃ Q : R[X], P = (X - 1) ^ k * Q ∧
      Q.eval 1 ≠ 0 ∧ Q.natDegree ≤ P.natDegree := by
  obtain ⟨Q, hQ, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 1
  refine ⟨P.rootMultiplicity 1, Q, by simpa using hQ, ?_, ?_⟩
  · intro h
    exact hnd (dvd_iff_isRoot.mpr h)
  · exact natDegree_le_of_dvd ⟨(X-C 1)^P.rootMultiplicity 1,
      by simpa [mul_comm] using hQ⟩ hP

noncomputable def substitute (F : PowerSeries ℚ) :
    Polynomial (Polynomial ℤ) →+* PowerSeries ℚ :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Int.castRingHom (PowerSeries ℚ)) F)
    PowerSeries.X

lemma substitute_X_sub_one (F : PowerSeries ℚ) :
    substitute F (X - 1) = PowerSeries.X - 1 := by
  simp [substitute]

lemma series_X_sub_one_unit : IsUnit ((PowerSeries.X : PowerSeries ℚ) - 1) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  norm_num

lemma vanishing_preserved (F : PowerSeries ℚ)
    (P Q : Polynomial (Polynomial ℤ)) (k N : ℕ)
    (h : P = (X - 1) ^ k * Q) :
    ((PowerSeries.X : PowerSeries ℚ) ^ N ∣ substitute F P) ↔
      ((PowerSeries.X : PowerSeries ℚ) ^ N ∣ substitute F Q) := by
  rw [h, map_mul, map_pow, substitute_X_sub_one]
  exact (series_X_sub_one_unit.pow k).dvd_mul_left

/-- The same rational formal series can be substituted before and after
removal, with precisely the same vanishing jets at zero. -/
theorem nonzero_specialization_preserving_jets
    (P : Polynomial (Polynomial ℤ)) (hP : P ≠ 0) :
    ∃ Q : Polynomial (Polynomial ℤ), Q.eval 1 ≠ 0 ∧
      Q.natDegree ≤ P.natDegree ∧
      ∀ (F : PowerSeries ℚ) (N : ℕ),
        (∀ n < N, PowerSeries.coeff n (substitute F P) = 0) ↔
        (∀ n < N, PowerSeries.coeff n (substitute F Q) = 0) := by
  obtain ⟨k, Q, h, hn, hd⟩ := remove_specialization_factor P hP
  refine ⟨Q, hn, hd, fun F N => ?_⟩
  rw [← PowerSeries.X_pow_dvd_iff, ← PowerSeries.X_pow_dvd_iff]
  exact vanishing_preserved F P Q k N h

end SpecializationFactorRemoval

#print axioms SpecializationFactorRemoval.nonzero_specialization_preserving_jets
