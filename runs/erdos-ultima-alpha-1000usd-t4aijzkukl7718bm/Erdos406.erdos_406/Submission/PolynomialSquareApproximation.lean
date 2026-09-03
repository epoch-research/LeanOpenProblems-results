import FormalConjecturesUtil

/-! Polynomial square-root truncation at infinity. This is an algebraic
preparation for a fixed-polynomial finiteness argument, not a uniform bound
for all binary digit polynomials. -/
namespace Erdos406Runge
open Polynomial

lemma monic_equal_degree_sub_bound (P Q : ℚ[X]) (n : ℕ)
    (hn : 0 < n) (hP : P.IsMonicOfDegree n) (hQ : Q.IsMonicOfDegree n) :
    (P - Q).natDegree < n := by
  have hb : (P - Q).natDegree ≤ n := by
    have hh := natDegree_sub_le P Q
    rw [hP.natDegree_eq, hQ.natDegree_eq, max_self] at hh
    exact hh
  have hc : (P - Q).coeff n = 0 := by
    rw [coeff_sub, ← hP.natDegree_eq, hP.monic.coeff_natDegree]
    rw [hP.natDegree_eq, ← hQ.natDegree_eq, hQ.monic.coeff_natDegree]
    ring
  by_cases hz : P - Q = 0
  · simpa [hz] using hn
  have hne : (P - Q).natDegree ≠ n := by
    intro he
    have hh := coeff_natDegree (p := P - Q)
    rw [he, hc] at hh
    exact hz (leadingCoeff_eq_zero.mp hh.symm)
  omega

/-- Correct the highest remaining coefficient of an approximate square root. -/
lemma improve_square_approximation (P Q : ℚ[X]) (d : ℕ) (hd : 0 < d)
    (hQ : Q.IsMonicOfDegree d)
    (hlo : d ≤ (P - Q^2).natDegree) (hhi : (P - Q^2).natDegree < 2*d) :
    ∃ S : ℚ[X], S.IsMonicOfDegree d ∧
      (P - S^2).natDegree < (P - Q^2).natDegree := by
  let R := P - Q^2
  let r := R.natDegree
  let U : ℚ[X] := C (R.leadingCoeff / 2) * X^(r-d)
  obtain ⟨E, hQE, hE⟩ := hQ.exists_natDegree_lt (by omega)
  have hU : U.natDegree ≤ r-d := natDegree_C_mul_X_pow_le _ _
  have hUd : U.natDegree < d := by dsimp [r, R] at hU; omega
  have hSU : (Q + U).IsMonicOfDegree d := hQ.add_right hUd
  have hrpos : 0 < r := by dsimp [r, R]; omega
  have hrd : d ≤ r := hlo
  have hcancel : C (2 : ℚ) * X^d * U = C R.leadingCoeff * X^r := by
    dsimp [U]
    calc
      _ = (C 2 * C (R.leadingCoeff / 2)) * (X^d * X^(r-d)) := by ring
      _ = _ := by
        rw [← C_mul, show 2 * (R.leadingCoeff / 2) = R.leadingCoeff by ring,
          ← pow_add, Nat.add_sub_of_le hrd]
  have hident : P - (Q+U)^2 = R.eraseLead - (C 2 * E * U + U^2) := by
    have herase := R.eraseLead_add_C_mul_X_pow
    change R.eraseLead + C R.leadingCoeff * X^r = R at herase
    rw [← hcancel] at herase
    dsimp only [R] at herase
    dsimp only [R]
    rw [hQE] at herase ⊢
    norm_num only [map_ofNat] at herase ⊢
    linear_combination -herase
  have hsmall : (C (2 : ℚ) * E * U + U^2).natDegree < r := by
    have hEU := natDegree_mul_le (p := C (2 : ℚ) * E) (q := U)
    have hCE := natDegree_C_mul_le (2 : ℚ) E
    have hUU := natDegree_pow_le (p := U) (n := 2)
    have hs := natDegree_add_le (C (2 : ℚ) * E * U) (U^2)
    omega
  have hEr : R.eraseLead.natDegree < r := by
    have hh := R.eraseLead_natDegree_le
    dsimp only [r]
    omega
  refine ⟨Q + U, hSU, ?_⟩
  rw [hident]
  have hh := natDegree_sub_le R.eraseLead (C (2 : ℚ) * E * U + U^2)
  change _ < r
  omega

/-- A monic polynomial of degree 2d has a monic rational polynomial square
root up to an error of degree strictly less than d. -/
theorem square_approximation (P : ℚ[X]) (d : ℕ) (hd : 0 < d)
    (hP : P.IsMonicOfDegree (2*d)) :
    ∃ Q : ℚ[X], Q.IsMonicOfDegree d ∧ (P - Q^2).natDegree < d := by
  have descend : ∀ r : ℕ, ∀ Q : ℚ[X], Q.IsMonicOfDegree d →
      (P-Q^2).natDegree = r → r < 2*d →
      ∃ S : ℚ[X], S.IsMonicOfDegree d ∧ (P-S^2).natDegree < d := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro Q hQ hr hlt
      by_cases hsmall : r < d
      · exact ⟨Q, hQ, by omega⟩
      obtain ⟨S, hS, hrem⟩ := improve_square_approximation P Q d hd hQ
        (by omega) (by omega)
      exact ih (P-S^2).natDegree (by omega) S hS rfl (by omega)
  have hX : (X^d : ℚ[X]).IsMonicOfDegree d := isMonicOfDegree_X_pow ℚ d
  have hX2 : ((X^d : ℚ[X])^2).IsMonicOfDegree (2*d) := by
    simpa [Nat.mul_comm] using hX.pow 2
  exact descend _ (X^d) hX rfl
    (monic_equal_degree_sub_bound P ((X^d)^2) (2*d) (by omega) hP hX2)

#print axioms square_approximation
end Erdos406Runge
