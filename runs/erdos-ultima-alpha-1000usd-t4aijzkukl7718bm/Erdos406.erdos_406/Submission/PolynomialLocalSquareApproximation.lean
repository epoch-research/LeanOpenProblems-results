import FormalConjecturesUtil

/-! Integer square-root truncations at zero, with dyadic denominators.
These are fixed-polynomial certificates; no uniform digit-pattern bound
is asserted. -/
namespace Erdos406LocalRunge
open Polynomial

/-- An integer-scaled square-root expansion to any prescribed order. -/
theorem local_square_approximation (P : ℤ[X]) (h0 : P.coeff 0 = 1) (n : ℕ) :
    ∃ s : ℕ, ∃ R : ℤ[X], R.natDegree ≤ n ∧ R.coeff 0 = (2 : ℤ)^s ∧
      X^(n+1) ∣ C ((2 : ℤ)^(2*s)) * P - R^2 := by
  induction n with
  | zero =>
    refine ⟨0, 1, by simp, by simp, ?_⟩
    simp only [Nat.zero_add, one_pow, pow_one]
    exact X_dvd_iff.mpr (by simp [h0])
  | succ n ih =>
    obtain ⟨s, R, hR, hR0, hdiv⟩ := ih
    let q : ℤ := 2^s
    let E : ℤ[X] := C (q^2) * P - R^2
    let c : ℤ := E.coeff (n+1)
    let T : ℤ[X] := C (2*q) * R + C c * X^(n+1)
    have hs : (2 : ℤ)^(2*s) = q^2 := by
      dsimp [q]
      rw [Nat.mul_comm 2 s, pow_mul]
    have hq' : (2 : ℤ)^(2*s+1) = 2*q^2 := by
      rw [pow_add, hs, pow_one]
      ring
    have hq : (2 : ℤ)^(2*(2*s+1)) = (2*q^2)^2 := by
      rw [Nat.mul_comm 2 (2*s+1), pow_mul, hq']
    have hdivE : X^(n+1) ∣ E := by
      simpa only [E, hs] using hdiv
    have hcoefE := X_pow_dvd_iff.mp hdivE
    have hident : C ((2*q^2)^2) * P - T^2 =
        C (4*q^2) * E - C (4*q*c) * R * X^(n+1) - C (c^2) * X^(2*(n+1)) := by
      dsimp [T, E]
      simp only [map_mul, map_pow, map_ofNat, pow_mul]
      ring
    refine ⟨2*s+1, T, ?_, ?_, ?_⟩
    · exact (natDegree_add_le _ _).trans (max_le
        ((natDegree_C_mul_le _ _).trans (by omega)) (natDegree_C_mul_X_pow_le _ _))
    · rw [hq']
      simp only [T, coeff_add, coeff_C_mul, coeff_X_pow,
        if_neg (by omega : ¬ 0 = n+1), mul_zero, add_zero, hR0]
      change 2*q*q = 2*q^2
      ring
    · rw [hq, hident]
      apply X_pow_dvd_iff.mpr
      intro i hi
      have h2 : ¬ 2*(n+1) ≤ i := by omega
      simp only [coeff_sub, coeff_C_mul, coeff_mul_X_pow', if_neg h2, sub_zero]
      by_cases hin : i < n+1
      · rw [hcoefE i hin, if_neg (by omega : ¬ n+1 ≤ i)]
        ring
      · have he : i = n+1 := by omega
        subst i
        simp only [le_refl, if_true, Nat.sub_self, hR0]
        change 4*q^2*c - 4*q*c*q = 0
        ring

#print axioms local_square_approximation
end Erdos406LocalRunge
