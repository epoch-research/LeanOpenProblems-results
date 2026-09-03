import FormalConjecturesUtil

/-! A diagnostic distinguishing two descent claims for sixth powers.
This is not a proof or disproof of Erdős 406: the example has odd prime
factor eleven. No assertion about all sixth powers is made. -/

namespace Erdos406SixthPowerDiagnostic

lemma eleven_sixth_good : Nat.digits 3 (11 ^ 6) ⊆ [0, 1] := by
  decide +kernel

lemma eleven_square_good : Nat.digits 3 (11 ^ 2) ⊆ [0, 1] := by
  decide +kernel

lemma eleven_cube_bad : ¬ Nat.digits 3 (11 ^ 3) ⊆ [0, 1] := by
  decide +kernel

/-- Square descent fails even when the square root is itself a cube.
This does not negate cube descent restricted to square roots. -/
theorem square_descent_on_cubes_false :
    ¬ (∀ n : ℕ, Nat.digits 3 (n ^ 6) ⊆ [0, 1] →
      Nat.digits 3 (n ^ 3) ⊆ [0, 1]) := by
  intro h
  exact eleven_cube_bad (h 11 eleven_sixth_good)

lemma eleven_sixth_not_power_of_two : ¬ (11 ^ 6 : ℕ).isPowerOfTwo := by
  rintro ⟨k, hk⟩
  have hd : 11 ∣ (2 : ℕ) ^ k := by
    rw [← hk]
    exact dvd_pow_self 11 (by decide)
  have hp : Nat.Prime 11 := by decide
  have hh := hp.dvd_of_dvd_pow hd
  norm_num at hh

lemma eleven_scaled_sixth_good : Nat.digits 3 (4 * 11 ^ 6) ⊆ [0, 1] := by
  decide +kernel

lemma eleven_scaled_sixth_not_power_of_two :
    ¬ (4 * 11 ^ 6 : ℕ).isPowerOfTwo := by
  rintro ⟨k, hk⟩
  have hd : 11 ∣ (2 : ℕ) ^ k := by
    rw [← hk]
    exact dvd_mul_of_dvd_right (dvd_pow_self 11 (by decide)) 4
  have hp : Nat.Prime 11 := by decide
  have hh := hp.dvd_of_dvd_pow hd
  norm_num at hh

#print axioms eleven_scaled_sixth_good
#print axioms eleven_scaled_sixth_not_power_of_two
#print axioms square_descent_on_cubes_false
#print axioms eleven_sixth_not_power_of_two

end Erdos406SixthPowerDiagnostic
