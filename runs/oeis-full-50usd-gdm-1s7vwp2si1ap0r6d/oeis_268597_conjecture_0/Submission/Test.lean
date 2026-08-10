import Mathlib

open Nat

lemma totient_divisor_sol (d : ℕ) (hd_div : d.totient ∣ d) (q : ℕ) (hq : q.Prime) (hdq : d.Coprime q) (c : ℕ) (hc : c ≥ 1) (h_ineq : q - 1 ≥ d / d.totient) :
    (d * q^(c+1) - 1) % (d.totient * q^c * (q - 1)) = d * q^c - 1 := by
  have hd_pos : d > 0 := by
    by_contra hc
    have : d = 0 := by omega
    subst this
    have h_gcd : Nat.gcd 0 q = q := Nat.gcd_zero_left q
    have h_cop : Nat.gcd 0 q = 1 := hdq
    rw [h_gcd] at h_cop
    subst h_cop
    exact Nat.not_prime_one hq
  have hq_pos : q > 0 := by
    have : q ≥ 2 := hq.two_le
    omega
  have h_qc_pos : q^c > 0 := by positivity
  have h_d_qc_pos : d * q^c > 0 := Nat.mul_pos hd_pos h_qc_pos
  have hd_eq : d = (d / d.totient) * d.totient := (Nat.div_mul_cancel hd_div).symm
  set k := d / d.totient
  have h_eq : d * q^(c+1) - 1 = k * (d.totient * q^c * (q - 1)) + (d * q^c - 1) := by
    rw [pow_succ q c]
    have h1 : d * (q^c * q) - 1 = d * q^c * q - 1 := by ring
    rw [h1]
    have h2 : k * (d.totient * q^c * (q - 1)) = d * q^c * (q - 1) := by
      calc k * (d.totient * q^c * (q - 1))
        _ = (k * d.totient) * q^c * (q - 1) := by ring
        _ = d * q^c * (q - 1) := by rw [← hd_eq]
    rw [h2]
    -- Now we need d * q^c * q - 1 = d * q^c * (q - 1) + (d * q^c - 1)
    have h_assoc : d * q^c * (q - 1) + (d * q^c - 1) = d * q^c * (q - 1) + d * q^c - 1 := by omega
    rw [h_assoc]
    have h_sub : q - 1 + 1 = q := by omega
    have h_mul : d * q^c * (q - 1) + d * q^c = d * q^c * (q - 1 + 1) := by ring
    rw [h_mul, h_sub]
  rw [h_eq]
  have h_mod : (k * (d.totient * q^c * (q - 1)) + (d * q^c - 1)) % (d.totient * q^c * (q - 1)) = (d * q^c - 1) % (d.totient * q^c * (q - 1)) := by
    rw [add_comm]
    have h_comm : k * (d.totient * q^c * (q - 1)) = (d.totient * q^c * (q - 1)) * k := by ring
    rw [h_comm]
    rw [Nat.add_mul_mod_self_left]
  rw [h_mod]
  apply Nat.mod_eq_of_lt
  have : d * q^c - 1 < d * q^c := by omega
  have : d * q^c ≤ d.totient * q^c * (q - 1) := by
    have h_mul_ineq : d.totient * (q - 1) ≥ d := by
      calc d.totient * (q - 1)
        _ ≥ d.totient * k := Nat.mul_le_mul_left d.totient h_ineq
        _ = d := by
          rw [mul_comm]
          exact hd_eq.symm
    calc d * q^c
      _ ≤ (d.totient * (q - 1)) * q^c := Nat.mul_le_mul_right (q^c) h_mul_ineq
      _ = d.totient * q^c * (q - 1) := by ring
  omega




