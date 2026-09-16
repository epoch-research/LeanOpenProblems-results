import Submission.Spec
open Nat

lemma dvd_of_169 (a b b' : ℕ) (h : 169 ∣ 2^a * 3^b * b') : 13^2 ∣ b' := by
  have hc : Coprime 169 (2^a * 3^b) := by
    apply Coprime.mul_right
    · exact (Coprime.pow_right a (by decide))
    · exact (Coprime.pow_right b (by decide))
  exact hc.dvd_of_dvd_mul_left h

set_option exponentiation.threshold 100000
set_option maxRecDepth 1000000

theorem test_padic (a b b' : ℕ) (hsq : Squarefree b')
    (h : A070823 20 = 2^a * 3^b * b') : False := by
  have h1 : A070823 20 % 169 = 0 := by rfl
  have h2 : 169 ∣ A070823 20 := Nat.dvd_of_mod_eq_zero h1
  have h3 : 169 ∣ 2^a * 3^b * b' := by rw [← h]; exact h2
  have h4 : 13^2 ∣ b' := dvd_of_169 a b b' h3
  have h5 : IsUnit 13 := hsq 13 h4
  rw [Nat.isUnit_iff] at h5
  contradiction
