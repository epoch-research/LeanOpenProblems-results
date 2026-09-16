import Mathlib
import Submission.Spec
open Finset

lemma if_direction {n : ℕ} (hp : n.Prime) (hodd : n ≠ 2) :
  (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  have H := A000224_prime_A000224 n hp hodd
  rw [H]
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hodd
  have h1 : (n + 1) / 2 = k + 1 := by
    rw [hk]
    omega
  have h2 : (n - 1) / 2 = k := by
    rw [hk]
    omega
  rw [h1, h2]
  have h_pos : 1 ≤ n * n := by nlinarith [hp.two_le]
  apply Nat.ModEq.symm
  apply (Nat.modEq_iff_dvd' h_pos).mpr
  have h_eq : n * n - 1 = 4 * ((k + 1) * k) := by
    rw [hk]
    have H1 : (2 * k + 1) * (2 * k + 1) = 4 * k * k + 4 * k + 1 := by ring
    rw [H1]
    have H2 : 4 * k * k + 4 * k + 1 - 1 = 4 * k * k + 4 * k := by omega
    rw [H2]
    ring
  rw [h_eq]
  exact dvd_mul_left _ _
