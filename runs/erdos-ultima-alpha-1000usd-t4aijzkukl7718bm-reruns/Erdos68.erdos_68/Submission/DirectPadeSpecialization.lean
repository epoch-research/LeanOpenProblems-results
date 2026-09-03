import Submission.ScaledDenominatorRoughness

/-!
A divisibility constraint on direct-series Padé specialization. These are
auxiliary arithmetic statements, not an irrationality proof.
-/

namespace DirectPadeSpecialization

open Finset

lemma integer_multiple_of_coprime_den (M : ℕ) (r : ℚ) (z : ℤ)
    (hc : M.Coprime r.den) (he : (M : ℚ) * r = z) : (M : ℤ) ∣ z := by
  have he' : (z : ℚ) * r.den = (M : ℚ) * r.num := by
    rw [← he, mul_assoc, Rat.mul_den_eq_num]
  have heZ : z * (r.den : ℤ) = (M : ℤ) * r.num := by exact_mod_cast he'
  have hcZ : IsCoprime (M : ℤ) (r.den : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hc
  exact hcZ.dvd_of_dvd_mul_right ⟨r.num, heZ⟩

lemma integer_quotient_den_coprime (M d : ℕ) (z : ℤ)
    (hd : 0 < d) (hc : M.Coprime d) :
    M.Coprime ((z : ℚ) / (d : ℚ)).den := by
  rw [div_eq_mul_inv]
  apply Nat.Coprime.of_dvd_right (Rat.mul_den_dvd _ _)
  simpa [Rat.inv_natCast_den_of_pos hd] using hc

/-- A vanishing integer-weighted relation between sufficiently late direct
coefficients forces factorial divisibility of the sum of its weights. -/
theorem factorial_dvd_weight_sum {ι : Type*} (s : Finset ι)
    (w : ι → ℤ) (n : ι → ℕ) (L : ℕ) (hL : 2 ≤ L)
    (hn : ∀ i ∈ s, L ≤ n i)
    (hzero : ∑ i ∈ s, (w i : ℚ) / ((n i).factorial - 1 : ℚ) = 0) :
    (L.factorial : ℤ) ∣ ∑ i ∈ s, w i := by
  let r : ℚ := ∑ i ∈ s,
    (w i * ((n i).factorial / L.factorial : ℕ) : ℤ) /
      (((n i).factorial - 1 : ℕ) : ℚ)
  have hpos : ∀ i ∈ s, 0 < (n i).factorial - 1 := by
    intro i hi
    have hf : 2 ≤ (n i).factorial := by
      simpa using Nat.factorial_le (hL.trans (hn i hi))
    omega
  have hc : L.factorial.Coprime r.den := by
    apply ScaledDenominatorRoughness.coprime_sum_den
    intro i hi
    apply integer_quotient_den_coprime _ _ _ (hpos i hi)
    exact ScaledDenominatorRoughness.factorial_pred_coprime (hn i hi)
  apply integer_multiple_of_coprime_den L.factorial r _ hc
  have hrow : ∀ i ∈ s,
      (L.factorial : ℚ) *
          ((w i * ((n i).factorial / L.factorial : ℕ) : ℤ) /
            (((n i).factorial - 1 : ℕ) : ℚ)) =
        (w i : ℚ) + (w i : ℚ) / ((n i).factorial - 1 : ℚ) := by
    intro i hi
    have hdiv := Nat.factorial_dvd_factorial (hn i hi)
    have hne : (L.factorial : ℚ) ≠ 0 := by positivity
    have hf : 1 ≤ (n i).factorial := Nat.factorial_pos _
    have hd : ((n i).factorial - 1 : ℚ) ≠ 0 := by
      have hp := hpos i hi
      have he : (((n i).factorial - 1 : ℕ) : ℚ) =
          ((n i).factorial - 1 : ℚ) := by simp [Nat.cast_sub hf]
      rw [← he]
      exact_mod_cast hp.ne'
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div hdiv hne, Nat.cast_sub hf]
    push_cast
    field_simp
    ring
  dsimp only [r]
  rw [Finset.mul_sum]
  calc
    _ = ∑ i ∈ s, ((w i : ℚ) + (w i : ℚ) / ((n i).factorial - 1 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i hi
    _ = _ := by
      rw [Finset.sum_add_distrib, hzero, add_zero]
      simp

/-- The highest vanishing Padé coefficient already forces divisibility of
Q(1). Here the direct generating series starts at index two, and all indices
appearing in this coefficient equation are at least two. -/
theorem factorial_dvd_specialization (Q : Polynomial ℤ) (N : ℕ)
    (hgap : Q.natDegree + 2 ≤ N)
    (hjet : ∑ j ∈ range (Q.natDegree + 1),
      (Q.coeff j : ℚ) / ((N-j).factorial - 1 : ℚ) = 0) :
    ((N-Q.natDegree).factorial : ℤ) ∣ Q.eval 1 := by
  have h := factorial_dvd_weight_sum (range (Q.natDegree+1)) Q.coeff
    (fun j => N-j) (N-Q.natDegree) (by omega)
    (by intro j hj; dsimp only; have := mem_range.mp hj; omega) hjet
  simpa [Polynomial.eval_eq_sum_range] using h

noncomputable def directSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => 1 / (n.factorial - 1 : ℚ)

lemma direct_coefficient_zero : PowerSeries.coeff 0 directSeries = 0 := by
  simp [directSeries]

lemma direct_coefficient_one : PowerSeries.coeff 1 directSeries = 0 := by
  simp [directSeries]

lemma direct_product_coefficient (Q : Polynomial ℤ) (N : ℕ)
    (hN : Q.natDegree ≤ N) :
    PowerSeries.coeff N
        ((Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) * directSeries) =
      ∑ j ∈ range (Q.natDegree + 1),
        (Q.coeff j : ℚ) / ((N-j).factorial - 1 : ℚ) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i
        (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) *
          PowerSeries.coeff j directSeries) N]
  simp only [Polynomial.coeff_coe, Polynomial.coeff_map, directSeries,
    PowerSeries.coeff_mk, mul_one_div]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j _ hj
  have hdeg : Q.natDegree < j := by
    simp only [Finset.mem_range] at hj
    omega
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]

/-- Formal-power-series version: no analytic evaluation or rationality
hypothesis is involved in this divisibility statement. -/
theorem pade_factorial_dvd_specialization (P : Polynomial ℚ) (Q : Polynomial ℤ)
    (N : ℕ) (hP : P.natDegree < N) (hQ : Q.natDegree + 2 ≤ N)
    (hjet : PowerSeries.coeff N
      ((Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) * directSeries -
        (P : PowerSeries ℚ)) = 0) :
    ((N-Q.natDegree).factorial : ℤ) ∣ Q.eval 1 := by
  apply factorial_dvd_specialization Q N hQ
  rw [map_sub, Polynomial.coeff_coe,
    Polynomial.coeff_eq_zero_of_natDegree_lt hP, sub_zero,
    direct_product_coefficient Q N (by omega)] at hjet
  exact hjet

/-- A common degree-bound formulation of the Padé divisibility. -/
theorem pade_factorial_dvd_of_degree_bounds (P : Polynomial ℚ) (Q : Polynomial ℤ)
    (M N : ℕ) (hP : P.natDegree ≤ M) (hQ : Q.natDegree ≤ M)
    (hgap : M + 2 ≤ N)
    (hjet : PowerSeries.coeff N
      ((Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) * directSeries -
        (P : PowerSeries ℚ)) = 0) :
    ((N-M).factorial : ℤ) ∣ Q.eval 1 := by
  have hd := pade_factorial_dvd_specialization P Q N (by omega) (by omega) hjet
  have hf : (N-M).factorial ∣ (N-Q.natDegree).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  exact (show ((N-M).factorial : ℤ) ∣ ((N-Q.natDegree).factorial : ℤ) by
    exact_mod_cast hf).trans hd

/-- At a rational input, the retained coefficient already clears that
input's denominator once the gap is large enough. No nonzero or small-error
assertion is included. -/
theorem rational_form_integer (Q : Polynomial ℤ) (N : ℕ) (q : ℚ) (b : ℤ)
    (hgap : Q.natDegree + 2 ≤ N)
    (hjet : ∑ j ∈ range (Q.natDegree + 1),
      (Q.coeff j : ℚ) / ((N-j).factorial - 1 : ℚ) = 0)
    (hden : q.den ≤ N-Q.natDegree) :
    ∃ z : ℤ, ((Q.eval 1 : ℤ) : ℚ) * q - b = z := by
  have hd := factorial_dvd_specialization Q N hgap hjet
  have hq : (q.den : ℤ) ∣ Q.eval 1 := by
    apply dvd_trans _ hd
    exact_mod_cast Nat.dvd_factorial q.den_pos hden
  obtain ⟨k, hk⟩ := hq
  refine ⟨k*q.num-b, ?_⟩
  rw [hk]
  push_cast
  calc
    _ = (k : ℚ) * (q * q.den) - b := by ring
    _ = _ := by rw [Rat.mul_den_eq_num]

lemma eval_one_abs_bound (Q : Polynomial ℤ) (H : ℕ)
    (hH : ∀ j ≤ Q.natDegree, |Q.coeff j| ≤ (H : ℤ)) :
    |Q.eval 1| ≤ ((Q.natDegree+1)*H : ℕ) := by
  rw [Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one]
  calc
    _ ≤ ∑ j ∈ range (Q.natDegree+1), |Q.coeff j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range (Q.natDegree+1), (H : ℤ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hH j (by have := mem_range.mp hj; omega)
    _ = _ := by simp

/-- Nonzero specialization imposes a factorial lower bound on the ordinary
integer coefficient height. This alone is not a lower bound on the
primitive integer form after specializing and reducing its content. -/
theorem specialization_height_bound (Q : Polynomial ℤ) (N H : ℕ)
    (hgap : Q.natDegree + 2 ≤ N)
    (hjet : ∑ j ∈ range (Q.natDegree + 1),
      (Q.coeff j : ℚ) / ((N-j).factorial - 1 : ℚ) = 0)
    (hQ : Q.eval 1 ≠ 0)
    (hH : ∀ j ≤ Q.natDegree, |Q.coeff j| ≤ (H : ℤ)) :
    (N-Q.natDegree).factorial ≤ (Q.natDegree+1)*H := by
  have hd := factorial_dvd_specialization Q N hgap hjet
  have hlo : ((N-Q.natDegree).factorial : ℤ) ≤ |Q.eval 1| :=
    Int.le_of_dvd (abs_pos.mpr hQ) ((dvd_abs _ _).mpr hd)
  exact_mod_cast hlo.trans (eval_one_abs_bound Q H hH)

theorem specialization_zero_of_small_height (Q : Polynomial ℤ) (N H : ℕ)
    (hgap : Q.natDegree + 2 ≤ N)
    (hjet : ∑ j ∈ range (Q.natDegree + 1),
      (Q.coeff j : ℚ) / ((N-j).factorial - 1 : ℚ) = 0)
    (hH : ∀ j ≤ Q.natDegree, |Q.coeff j| ≤ (H : ℤ))
    (hsmall : (Q.natDegree+1)*H < (N-Q.natDegree).factorial) : Q.eval 1 = 0 := by
  by_contra hQ
  exact (Nat.not_lt_of_ge (specialization_height_bound Q N H hgap hjet hQ hH)) hsmall

end DirectPadeSpecialization

#print axioms DirectPadeSpecialization.factorial_dvd_weight_sum
#print axioms DirectPadeSpecialization.pade_factorial_dvd_specialization
#print axioms DirectPadeSpecialization.specialization_height_bound
#print axioms DirectPadeSpecialization.specialization_zero_of_small_height
