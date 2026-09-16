import Mathlib

open Nat Finset

def M_val (p : ℕ) : ℕ := (p - 1) * (p - 3) / 2 * p + 1

lemma hL1_val_eq (p M : ℕ) (hp : 5 ≤ p) (hM_ge : p ≤ M) :
  p * (p - 2) * (p * (p - 2) - 1) / 2 = p * M ↔
  p * (p * p - 4 * p + 3) + 2 = 2 * M := sorry

lemma H_M_val_eq (p : ℕ) (hp : 5 ≤ p) (hp_prime : p.Prime) :
  let M := M_val p
  p * (p - 2) * (p * (p - 2) - 1) / 2 = p * M := by
  intro M
  have hM_ge : p ≤ M := by
    dsimp [M, M_val]
    have H : 2 ≤ (p - 1) * (p - 3) := by
      have : 4 ≤ p - 1 := by omega
      have : 2 ≤ p - 3 := by omega
      nlinarith
    have h_div : 1 ≤ (p - 1) * (p - 3) / 2 := by
      rw [Nat.le_div_iff_mul_le (by decide)]
      exact H
    nlinarith
  rw [hL1_val_eq p M hp hM_ge]
  dsimp [M, M_val]
  have H : p * (p * p - 4 * p + 3) + 2 = 2 * ((p - 1) * (p - 3) / 2 * p + 1) := by
    -- 2 * ((p-1)*(p-3)/2 * p + 1) = 2 * ((p-1)*(p-3)/2) * p + 2 = (p-1)*(p-3)*p + 2
    have hp_odd : Odd p := hp_prime.odd_of_ne_two (by omega)
    have H1 : 2 ∣ (p - 1) := by
      obtain ⟨k, hk⟩ := hp_odd
      use k
      omega
    have H1_mul : 2 ∣ (p - 1) * (p - 3) := dvd_mul_of_dvd_left H1 (p - 3)
    have H2 : 2 * ((p - 1) * (p - 3) / 2) = (p - 1) * (p - 3) := Nat.mul_div_cancel' H1_mul
    have H3 : 2 * ((p - 1) * (p - 3) / 2 * p + 1) = (p - 1) * (p - 3) * p + 2 := by
      calc 2 * ((p - 1) * (p - 3) / 2 * p + 1) = 2 * ((p - 1) * (p - 3) / 2 * p) + 2 * 1 := by ring
      _ = 2 * ((p - 1) * (p - 3) / 2) * p + 2 := by ring
      _ = (p - 1) * (p - 3) * p + 2 := by rw [H2]
    rw [H3]
    -- p*(p*p - 4*p + 3) = (p-1)*(p-3)*p
    have H_cast : ((p * (p * p - 4 * p + 3) + 2 : ℕ) : ℤ) = (((p - 1) * (p - 3) * p + 2 : ℕ) : ℤ) := by
      have hp4 : 4 * p ≤ p * p := by
        have : 4 * 5 ≤ p * p := by nlinarith
        nlinarith
      have hp1 : 1 ≤ p := by omega
      have hp3 : 3 ≤ p := by omega
      push_cast [Nat.cast_sub hp4, Nat.cast_sub hp1, Nat.cast_sub hp3]
      ring
    exact_mod_cast H_cast
  exact H
