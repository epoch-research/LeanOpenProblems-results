import FormalConjectures.Util.ProblemImports
open Finset Nat

lemma odd_coprime_four {q : ℕ} (hqodd : q % 2 = 1) : Nat.Coprime q 4 := by
  have hOdd : Odd q := by
    rw [← Nat.coprime_two_right]
    -- easier prove gcd q 2 = 1 from mod eq 1
    rw [Nat.coprime_comm]
    rw [Nat.coprime_two_left]
    exact by omega
  rw [show 4 = 2 ^ 2 by norm_num]
  exact Nat.Coprime.pow_right 2 ((Nat.coprime_two_right).2 hOdd)

lemma dvd_value_of_dvd_four_p_sub_one {p q : ℕ} (hqodd : q % 2 = 1)
    (hdiv : q ∣ 4*p - 1) :
    q ∣ ((q+1)/2)^2 - ((q+1)/2) + p := by
  let k := (q + 1) / 2
  have hk2 : 2 * k = q + 1 := by
    dsimp [k]
    have : (q + 1) % 2 = 0 := by omega
    exact (Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_of_mod_eq_zero this)) |> by
      intro h; omega
  have hqeq : q = 2 * k - 1 := by omega
  have hcancel : Nat.Coprime q 4 := odd_coprime_four hqodd
  apply hcancel.dvd_of_dvd_mul_right
  have h4 : q ∣ 4 * (k^2 - k + p) := by
    have hcalc : 4 * (k^2 - k + p) = q * q + (4*p - 1) := by
      subst q
      have hkpos : 1 ≤ k := by omega
      nlinarith
    rw [hcalc]
    exact dvd_add (dvd_mul_right q q) hdiv
  simpa [k, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h4
