import FormalConjectures.Util.ProblemImports

open Int
open Polynomial

/--
A217703: $a(0)=1$, $a(1)=0$, and $a(n+1) = 2n(n+1)a(n)-n^4 a(n-1)$ for $n>0$.
-/
def A217703 (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | 1 => 0
  | k + 2 =>
    -- The index being computed is $k+2$. The OEIS coefficient index is $n = k+1$.
    -- Recurrence: A(k+2) = 2(k+1)(k+2) A(k+1) - (k+1)^4 A(k)
    let m : ℤ := (k + 1 : ℕ)
    let a_k_plus_1 : ℤ := A217703 (k + 1)
    let a_k : ℤ := A217703 k
    (2 * m * (m + 1)) * a_k_plus_1 - (m ^ 4) * a_k

/--
A217703 related polynomials: $S_0(x)=1$, $S_1(x)=x$, and $S_{n+1}(x)=(x+2n(n+1))S_n(x)-n^4 S_{n-1}(x)$ for $n>0$.
$S_n(x)$ is a polynomial with integer coefficients.
-/
noncomputable def Sn (n : ℕ) : Polynomial ℤ :=
  match n with
  | 0 => 1
  | 1 => X
  | k + 2 =>
    -- $n = k+1$ in the OEIS recurrence $S_{n+1}$
    let m : ℕ := k + 1
    let Sm : Polynomial ℤ := Sn m
    let S_m_minus_1 : Polynomial ℤ := Sn k

    let m_int : ℤ := m
    let coeff_int : ℤ := 2 * m_int * (m_int + 1)
    let coeff_poly : Polynomial ℤ := Polynomial.X + Polynomial.C coeff_int
    coeff_poly * Sm - Polynomial.C (m_int ^ 4) * S_m_minus_1

lemma Sn_zero : Sn 0 = 1 := rfl
lemma Sn_one : Sn 1 = X := rfl

lemma Sn_add_two (k : ℕ) :
  Sn (k + 2) = (X + C (2 * (k + 1 : ℤ) * (k + 2 : ℤ))) * Sn (k + 1) - C ((k + 1 : ℤ) ^ 4) * Sn k := by
  rfl

theorem Sn_natDegree (n : ℕ) : (Sn n).natDegree = n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · rw [Sn_zero, natDegree_one]
  · rw [Sn_one, natDegree_X]
  · rw [Sn_add_two]
    have ih1 : (Sn (k + 1)).natDegree = k + 1 := ih (k + 1) (by omega)
    have ih2 : (Sn k).natDegree = k := ih k (by omega)
    have h1 : ((X + C (2 * (k + 1 : ℤ) * (k + 2 : ℤ))) * Sn (k + 1)).natDegree = k + 2 := by
      rw [natDegree_mul]
      · have : (X + C (2 * (k + 1 : ℤ) * (k + 2 : ℤ))).natDegree = 1 := by
          apply natDegree_X_add_C
        rw [this, ih1]
        omega
      · intro h
        have h_coeff : (X + C (2 * (k + 1 : ℤ) * (k + 2 : ℤ))).leadingCoeff = 0 := leadingCoeff_eq_zero.mpr h
        have h_X : (X + C (2 * (k + 1 : ℤ) * (k + 2 : ℤ))).leadingCoeff = 1 := by
          rw [leadingCoeff_X_add_C]
        rw [h_X] at h_coeff
        contradiction
      · intro h
        have h_coeff : (Sn (k + 1)).leadingCoeff = 0 := leadingCoeff_eq_zero.mpr h
        have h_deg : (Sn (k + 1)).natDegree = 0 := by
          rw [leadingCoeff_eq_zero.mp h_coeff, natDegree_zero]
        rw [ih1] at h_deg
        contradiction
    have h2 : (C ((k + 1 : ℤ) ^ 4) * Sn k).natDegree ≤ k := by
      apply natDegree_mul_le.trans
      have : (C ((k + 1 : ℤ) ^ 4)).natDegree = 0 := natDegree_C _
      rw [this, ih2, zero_add]
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · exact h1
    · rw [h1]
      exact h2.trans_lt (by omega)

theorem Sn_monic (n : ℕ) : (Sn n).Monic := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · rw [Sn_zero]
    exact monic_one
  · rw [Sn_one]
    exact monic_X
  · rw [Sn_add_two]
    have ih1 : (Sn (k + 1)).Monic := ih (k + 1) (by omega)
    have ih2 : (Sn k).Monic := ih k (by omega)
    have h_mul_monic : ((X + C (2 * (k + 1 : ℤ) * (k + 2 : ℤ))) * Sn (k + 1)).Monic := by
      apply Monic.mul
      · exact monic_X_add_C _
      · exact ih1
    rw [sub_eq_add_neg]
    apply Monic.add_of_left h_mul_monic
    rw [degree_neg]
    have hdeg1 : ((X + C (2 * (k + 1 : ℤ) * (k + 2 : ℤ))) * Sn (k + 1)).degree = ↑(k + 2) := by
      rw [degree_eq_natDegree h_mul_monic.ne_zero]
      have : ((X + C (2 * (k + 1 : ℤ) * (k + 2 : ℤ))) * Sn (k + 1)).natDegree = k + 2 := by
        rw [natDegree_mul]
        · have hdegX : (X + C (2 * (k + 1 : ℤ) * (k + 2 : ℤ))).natDegree = 1 := natDegree_X_add_C _
          rw [hdegX, Sn_natDegree]
          omega
        · intro h
          have := leadingCoeff_eq_zero.mpr h
          rw [leadingCoeff_X_add_C] at this
          contradiction
        · intro h
          exact ih1.ne_zero h
      rw [this]
    have hdeg2 : (C ((k + 1 : ℤ) ^ 4) * Sn k).degree < ↑(k + 2) := by
      apply (degree_mul_le _ _).trans_lt
      have hdeg_C : (C ((k + 1 : ℤ) ^ 4)).degree ≤ 0 := degree_C_le
      have hdeg_S : (Sn k).degree = ↑k := by
        rw [degree_eq_natDegree ih2.ne_zero, Sn_natDegree]
      rw [hdeg_S]
      have : (C ((k + 1 : ℤ) ^ 4)).degree + (↑k : WithBot ℕ) ≤ 0 + ↑k := add_le_add hdeg_C le_rfl
      apply this.trans_lt
      simp only [zero_add]
      norm_cast
      omega
    rw [hdeg1]
    exact hdeg2

lemma Sn_two_eq : Polynomial.map (Int.castRingHom ℚ) (Sn 2) = X^2 + 4 * X - 1 := by
  rw [Sn_add_two 0]
  rw [Sn_one, Sn_zero]
  simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X]
  ring

lemma not_isSquare_five : ¬ IsSquare (5 : ℚ) := by
  norm_num

lemma no_roots_S2 (x : ℚ) : x^2 + 4*x - 1 ≠ 0 := by
  intro h
  have hsq : (x + 2)^2 = 5 := by
    calc (x + 2)^2 = x^2 + 4*x + 4 := by ring
    _ = (x^2 + 4*x - 1) + 5 := by ring
    _ = 0 + 5 := by rw [h]
    _ = 5 := by ring
  have hsq2 : (x + 2) * (x + 2) = 5 := by
    rw [← pow_two]
    exact hsq
  have h_is_sq : IsSquare (5 : ℚ) := ⟨x + 2, hsq2.symm⟩
  exact not_isSquare_five h_is_sq

lemma Sn_three_eq : Polynomial.map (Int.castRingHom ℚ) (Sn 3) = X^3 + 16 * X^2 + 31 * X - 12 := by
  have h3 : Sn 3 = (X + C (2 * (1 + 1 : ℤ) * (1 + 2 : ℤ))) * Sn 2 - C ((1 + 1 : ℤ) ^ 4) * Sn 1 := rfl
  have h2 : Sn 2 = (X + C (2 * (0 + 1 : ℤ) * (0 + 2 : ℤ))) * Sn 1 - C ((0 + 1 : ℤ) ^ 4) * Sn 0 := rfl
  rw [h3, h2, Sn_one, Sn_zero]
  simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X]
  ring

lemma no_roots_S3 (x : ℚ) : x^3 + 16 * x^2 + 31 * x - 12 ≠ 0 := by
  intro h
  have h_aeval : aeval x (Sn 3) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    change eval x (Polynomial.map (Int.castRingHom ℚ) (Sn 3)) = 0
    rw [Sn_three_eq]
    simp [h]
  have h_roots := exists_integer_of_is_root_of_monic (Sn_monic 3) h_aeval
  rcases h_roots with ⟨r', hr', hdvd⟩
  rw [hr'] at h
  have h_coeff : (Sn 3).coeff 0 = -12 := by
    have h3 : Sn 3 = (X + C (2 * (1 + 1 : ℤ) * (1 + 2 : ℤ))) * Sn 2 - C ((1 + 1 : ℤ) ^ 4) * Sn 1 := rfl
    have h2 : Sn 2 = (X + C (2 * (0 + 1 : ℤ) * (0 + 2 : ℤ))) * Sn 1 - C ((0 + 1 : ℤ) ^ 4) * Sn 0 := rfl
    rw [h3, h2, Sn_one, Sn_zero]
    simp
  rw [h_coeff] at hdvd
  have hdvd_abs : r'.natAbs ∣ 12 := by
    have : r' ∣ 12 := by
      have : r' ∣ -12 := hdvd
      exact dvd_neg.mp this
    exact Int.natAbs_dvd_natAbs.mpr this
  have hr'_ne : r' ≠ 0 := by
    intro hr'0
    subst hr'0
    have : (0 : ℤ) ∣ -12 := hdvd
    have h_zero := zero_dvd_iff.mp this
    contradiction
  have h_abs_ne : r'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hr'_ne
  have h_abs_pos : 0 < r'.natAbs := Nat.pos_of_ne_zero h_abs_ne
  generalize hd : r'.natAbs = d
  rw [hd] at hdvd_abs h_abs_pos
  have h_abs_le : d ≤ 12 := Nat.le_of_dvd (by decide) hdvd_abs
  interval_cases d
  · -- d = 1
    have h_abs : r'.natAbs = 1 := by rw [← hd]
    rcases Int.natAbs_eq_iff.mp h_abs with rfl | rfl <;> { revert h; norm_num }
  · -- d = 2
    have h_abs : r'.natAbs = 2 := by rw [← hd]
    rcases Int.natAbs_eq_iff.mp h_abs with rfl | rfl <;> { revert h; norm_num }
  · -- d = 3
    have h_abs : r'.natAbs = 3 := by rw [← hd]
    rcases Int.natAbs_eq_iff.mp h_abs with rfl | rfl <;> { revert h; norm_num }
  · -- d = 4
    have h_abs : r'.natAbs = 4 := by rw [← hd]
    rcases Int.natAbs_eq_iff.mp h_abs with rfl | rfl <;> { revert h; norm_num }
  · exfalso; revert hdvd_abs; decide
  · -- d = 6
    have h_abs : r'.natAbs = 6 := by rw [← hd]
    rcases Int.natAbs_eq_iff.mp h_abs with rfl | rfl <;> { revert h; norm_num }
  · exfalso; revert hdvd_abs; decide
  · exfalso; revert hdvd_abs; decide
  · exfalso; revert hdvd_abs; decide
  · exfalso; revert hdvd_abs; decide
  · exfalso; revert hdvd_abs; decide
  · -- d = 12
    have h_abs : r'.natAbs = 12 := by rw [← hd]
    rcases Int.natAbs_eq_iff.mp h_abs with rfl | rfl <;> { revert h; norm_num }

/--
Conjectures from OEIS A217703:
(i) $S_n(x)$ is irreducible over the field of rational numbers for every $n=1,2,3,...$
-/
theorem oeis_217703_conjecture_i :
  ∀ (n : ℕ), 1 ≤ n → Irreducible (Polynomial.map (Int.castRingHom ℚ) (Sn n)) := by
  intro n hn
  rcases n with _ | n
  · contradiction
  · rcases n with _ | n
    · -- n = 1
      rw [Sn_one]
      rw [Polynomial.map_X]
      exact irreducible_X
    · rcases n with _ | n
      · -- n = 2
        have h_deg : (Polynomial.map (Int.castRingHom ℚ) (Sn 2)).natDegree ∈ Finset.Icc 1 3 := by
          rw [natDegree_map_eq_of_injective Int.cast_injective, Sn_natDegree]
          decide
        rw [Sn_two_eq] at h_deg ⊢
        apply irreducible_of_degree_le_three_of_not_isRoot h_deg
        intro x
        rw [IsRoot.def]
        simp
        exact no_roots_S2 x
      · rcases n with _ | n
        · -- n = 3
          have h_deg : (Polynomial.map (Int.castRingHom ℚ) (Sn 3)).natDegree ∈ Finset.Icc 1 3 := by
            rw [natDegree_map_eq_of_injective Int.cast_injective, Sn_natDegree]
            decide
          apply irreducible_of_degree_le_three_of_not_isRoot h_deg
          intro x
          rw [IsRoot.def]
          rw [Sn_three_eq]
          simp
          exact no_roots_S3 x
        · -- n >= 4
          sorry

#print axioms oeis_217703_conjecture_i

