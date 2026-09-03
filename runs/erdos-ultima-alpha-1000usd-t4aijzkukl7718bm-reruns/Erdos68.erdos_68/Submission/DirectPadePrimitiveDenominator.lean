import Submission.DirectPadeDerivativeCongruence

/-!
A cancellation-aware denominator consequence of the direct Padé congruence.
This is auxiliary arithmetic, not a settlement of Erdős problem 68.
-/

namespace DirectPadePrimitiveDenominator

open Finset DirectPadeSpecialization DirectPadeDerivativeCongruence

lemma quotient_gcd_dvd_of_dvd_mul (M c d : ℕ) (hM : 0 < M) (hd : M ∣ c*d) :
    M / Nat.gcd M c ∣ d := by
  have hh : M ∣ Nat.gcd M c * d := dvd_gcd_mul_of_dvd_mul hd
  have hg : 0 < Nat.gcd M c := Nat.gcd_pos_of_pos_left c hM
  apply (Nat.mul_dvd_mul_iff_left hg).mp
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left M c)]
  exact hh

/-- This statement concerns the denominator after reduction to lowest terms. -/
lemma congruence_dvd_derivative_times_reduced_denominator
    (M : ℕ) (D a b c : ℤ) (ha : a ≠ 0)
    (hMa : (M : ℤ) ∣ a) (hcong : (M : ℤ) ∣ D*(b-c)) :
    M ∣ (D*c).natAbs * ((b : ℚ) / (a : ℚ)).den := by
  let r : ℚ := (b : ℚ) / (a : ℚ)
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have he : (a : ℚ) * r = b := by dsimp [r]; field_simp
  have he' : (a : ℚ) * r.num = (b : ℚ) * r.den := by
    rw [← Rat.mul_den_eq_num, ← mul_assoc, he]
  have heZ : a * (r.num : ℤ) = b * (r.den : ℤ) := by exact_mod_cast he'
  have hb : (M : ℤ) ∣ b * (r.den : ℤ) := by
    rw [← heZ]
    exact dvd_mul_of_dvd_left hMa _
  have hDb : (M : ℤ) ∣ D * (b * (r.den : ℤ)) := dvd_mul_of_dvd_right hb D
  have hc' : (M : ℤ) ∣ D*(b-c)*(r.den : ℤ) := dvd_mul_of_dvd_left hcong _
  have hh : (M : ℤ) ∣ (D*c)*(r.den : ℤ) := by
    convert dvd_sub hDb hc' using 1
    ring
  have hn := Int.natCast_dvd.mp hh
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hn

/-- An explicit factor that survives all common-factor cancellation. -/
theorem reduced_denominator_retains_congruence
    (M : ℕ) (D a b c : ℤ) (hM : 0 < M) (ha : a ≠ 0)
    (hMa : (M : ℤ) ∣ a) (hcong : (M : ℤ) ∣ D*(b-c)) :
    M / Nat.gcd M (D*c).natAbs ∣ ((b : ℚ) / (a : ℚ)).den := by
  exact quotient_gcd_dvd_of_dvd_mul M _ _ hM
    (congruence_dvd_derivative_times_reduced_denominator M D a b c ha hMa hcong)

/-- Direct-series specialization with a possibly rational numerator polynomial.
Only its value at one is required to be integral. -/
theorem primitive_pade_denominator_divisible
    (P : Polynomial ℚ) (Q : Polynomial ℤ) (N L : ℕ) (b : ℤ)
    (hP : P.natDegree < N) (hL : 2 ≤ L) (hgap : Q.natDegree + L ≤ N)
    (hjet : ∀ k ≤ N, PowerSeries.coeff k
      ((Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) * directSeries -
        (P : PowerSeries ℚ)) = 0)
    (hb : P.eval 1 = b) (hQ : Q.eval 1 ≠ 0) :
    L.factorial / Nat.gcd L.factorial
        (((directPrefix L).den : ℤ) * Q.derivative.eval 1).natAbs ∣
      ((b : ℚ) / ((Q.eval 1 : ℤ) : ℚ)).den := by
  have hdiv := pade_factorial_dvd_specialization P Q N hP (by omega) (hjet N le_rfl)
  have hfac : (L.factorial : ℤ) ∣ ((N-Q.natDegree).factorial : ℤ) := by
    exact_mod_cast Nat.factorial_dvd_factorial (show L ≤ N-Q.natDegree by omega)
  exact reduced_denominator_retains_congruence L.factorial (directPrefix L).den
    (Q.eval 1) b (Q.derivative.eval 1) (Nat.factorial_pos L) hQ
    (hfac.trans hdiv)
    (pade_factorial_dvd_numerator_sub_derivative P Q N L b hP hL hgap hjet hb)

/-- The corresponding numerical lower bound, when Q'(1) is nonzero. -/
theorem factorial_le_derivative_times_primitive_denominator
    (P : Polynomial ℚ) (Q : Polynomial ℤ) (N L : ℕ) (b : ℤ)
    (hP : P.natDegree < N) (hL : 2 ≤ L) (hgap : Q.natDegree + L ≤ N)
    (hjet : ∀ k ≤ N, PowerSeries.coeff k
      ((Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) * directSeries -
        (P : PowerSeries ℚ)) = 0)
    (hb : P.eval 1 = b) (hQ : Q.eval 1 ≠ 0) (hQ' : Q.derivative.eval 1 ≠ 0) :
    L.factorial ≤ (directPrefix L).den * (Q.derivative.eval 1).natAbs *
      ((b : ℚ) / ((Q.eval 1 : ℤ) : ℚ)).den := by
  have hdiv := pade_factorial_dvd_specialization P Q N hP (by omega) (hjet N le_rfl)
  have hfac : (L.factorial : ℤ) ∣ ((N-Q.natDegree).factorial : ℤ) := by
    exact_mod_cast Nat.factorial_dvd_factorial (show L ≤ N-Q.natDegree by omega)
  have hd := congruence_dvd_derivative_times_reduced_denominator L.factorial
    (directPrefix L).den (Q.eval 1) b (Q.derivative.eval 1) hQ (hfac.trans hdiv)
    (pade_factorial_dvd_numerator_sub_derivative P Q N L b hP hL hgap hjet hb)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hd
  apply Nat.le_of_dvd _ hd
  exact Nat.mul_pos
    (Nat.mul_pos (directPrefix L).den_pos (Int.natAbs_pos.mpr hQ'))
    (Rat.den_pos _)

/-- A coprimality condition that guarantees the entire factorial survives.
No such condition for a useful approximation family is asserted here. -/
theorem full_factorial_dvd_primitive_denominator
    (P : Polynomial ℚ) (Q : Polynomial ℤ) (N L : ℕ) (b : ℤ)
    (hP : P.natDegree < N) (hL : 2 ≤ L) (hgap : Q.natDegree + L ≤ N)
    (hjet : ∀ k ≤ N, PowerSeries.coeff k
      ((Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) * directSeries -
        (P : PowerSeries ℚ)) = 0)
    (hb : P.eval 1 = b) (hQ : Q.eval 1 ≠ 0)
    (hc : Nat.Coprime L.factorial
      (((directPrefix L).den : ℤ) * Q.derivative.eval 1).natAbs) :
    L.factorial ∣ ((b : ℚ) / ((Q.eval 1 : ℤ) : ℚ)).den := by
  simpa only [hc.gcd_eq_one, Nat.div_one] using
    primitive_pade_denominator_divisible P Q N L b hP hL hgap hjet hb hQ

end DirectPadePrimitiveDenominator

#print axioms DirectPadePrimitiveDenominator.reduced_denominator_retains_congruence
#print axioms DirectPadePrimitiveDenominator.primitive_pade_denominator_divisible
#print axioms DirectPadePrimitiveDenominator.factorial_le_derivative_times_primitive_denominator
#print axioms DirectPadePrimitiveDenominator.full_factorial_dvd_primitive_denominator
