import FormalConjectures.Util.ProblemImports
open Finset Nat

lemma odd_coprime_four {q : ℕ} (hqodd : q % 2 = 1) : Nat.Coprime q 4 := by
  have hOdd : Odd q := Nat.odd_iff.mpr hqodd
  rw [show 4 = 2 ^ 2 by norm_num]
  exact Nat.Coprime.pow_right 2 ((Nat.coprime_two_right).2 hOdd)

lemma dvd_value_of_dvd_four_p_sub_one {p q : ℕ} (hqodd : q % 2 = 1)
    (hdiv : q ∣ 4*p - 1) :
    q ∣ ((q+1)/2)^2 - ((q+1)/2) + p := by
  let k := (q + 1) / 2
  have hk2 : 2 * k = q + 1 := by
    dsimp [k]
    omega
  have hqeq : q = 2 * k - 1 := by omega
  have hkpos : 1 ≤ k := by omega
  have hcancel : Nat.Coprime q 4 := odd_coprime_four hqodd
  apply hcancel.dvd_of_dvd_mul_right
  have hcalc : 4 * (k^2 - k + p) = q * q + (4*p - 1) := by
    have : q = 2*k - 1 := hqeq
    nlinarith
  have h4 : q ∣ 4 * (k^2 - k + p) := by
    rw [hcalc]
    exact dvd_add (dvd_mul_right q q) hdiv
  simpa [k, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h4
