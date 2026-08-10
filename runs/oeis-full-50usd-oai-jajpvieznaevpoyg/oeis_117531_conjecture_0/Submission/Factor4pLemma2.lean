import FormalConjectures.Util.ProblemImports
open Finset Nat

lemma dvd_value_of_dvd_four_p_sub_one {p q : ℕ} (hqodd : q % 2 = 1)
    (hdiv : q ∣ 4*p - 1) :
    q ∣ ((q+1)/2)^2 - ((q+1)/2) + p := by
  have hqpos : 0 < q := by
    by_contra h
    have : q = 0 := Nat.eq_zero_of_not_pos h
    simp [this] at hqodd
  have hq_ne0 : q ≠ 0 := Nat.ne_of_gt hqpos
  have hodd2 : (q + 1) / 2 * 2 = q + 1 := by
    rw [Nat.div_mul_cancel]
    omega
  -- Work by showing q divides four times the value, then cancel gcd(q,4)=1.
  have hcancel : Nat.Coprime q 4 := by
    rw [Nat.coprime_comm]
    -- q odd => coprime with 2 hence with 4
    have h2 : Nat.Coprime q 2 := by
      rw [Nat.coprime_two_right]
      omega
    simpa [show 4 = 2^2 by norm_num] using h2.coprime_pow_right 2
  apply hcancel.dvd_of_dvd_mul_right
  let k := (q + 1) / 2
  have hk2 : 2 * k = q + 1 := by omega
  have hcalc : 4 * (k^2 - k + p) = q * q + (4*p - 1) := by
    have hk2' : 2*k = q+1 := hk2
    nlinarith [hk2']
  rw [show ((q + 1) / 2) = k by rfl]
  rw [← hcalc]
  exact dvd_add (dvd_mul_right q q) hdiv
