import FormalConjectures.Util.ProblemImports
open Rat Nat

def HasOddDen (q : ℚ) : Prop := q.den % 2 ≠ 0

lemma odd_of_dvd_odd {a b : ℕ} (h_odd : a % 2 ≠ 0) (h_dvd : b ∣ a) : b % 2 ≠ 0 := by
  intro h_even
  rcases h_dvd with ⟨c, rfl⟩
  have h_mul : (b * c) % 2 = (b % 2) * (c % 2) % 2 := Nat.mul_mod b c 2
  rw [h_even] at h_mul
  simp only [zero_mul, zero_mod] at h_mul
  contradiction

lemma odd_den_add (q1 q2 : ℚ) (h1 : HasOddDen q1) (h2 : HasOddDen q2) : HasOddDen (q1 + q2) := by
  unfold HasOddDen at h1 h2
  unfold HasOddDen
  have h_dvd : (q1 + q2).den ∣ q1.den * q2.den := Rat.add_den_dvd q1 q2
  have h_lt1 : q1.den % 2 < 2 := Nat.mod_lt _ (by decide)
  have h_lt2 : q2.den % 2 < 2 := Nat.mod_lt _ (by decide)
  have hq1 : q1.den % 2 = 1 := by omega
  have hq2 : q2.den % 2 = 1 := by omega
  have h_mod : (q1.den * q2.den) % 2 = (q1.den % 2) * (q2.den % 2) % 2 := Nat.mul_mod q1.den q2.den 2
  have h_mul_odd : (q1.den * q2.den) % 2 ≠ 0 := by
    rw [h_mod, hq1, hq2]
    decide
  exact odd_of_dvd_odd h_mul_odd h_dvd

lemma odd_den_mul (q1 q2 : ℚ) (h1 : HasOddDen q1) (h2 : HasOddDen q2) : HasOddDen (q1 * q2) := by
  unfold HasOddDen at h1 h2
  unfold HasOddDen
  have h_dvd : (q1 * q2).den ∣ q1.den * q2.den := Rat.mul_den_dvd q1 q2
  have h_lt1 : q1.den % 2 < 2 := Nat.mod_lt _ (by decide)
  have h_lt2 : q2.den % 2 < 2 := Nat.mod_lt _ (by decide)
  have hq1 : q1.den % 2 = 1 := by omega
  have hq2 : q2.den % 2 = 1 := by omega
  have h_mod : (q1.den * q2.den) % 2 = (q1.den % 2) * (q2.den % 2) % 2 := Nat.mul_mod q1.den q2.den 2
  have h_mul_odd : (q1.den * q2.den) % 2 ≠ 0 := by
    rw [h_mod, hq1, hq2]
    decide
  exact odd_of_dvd_odd h_mul_odd h_dvd

lemma odd_den_inv_of_odd_nat (n : ℕ) (hn : n % 2 ≠ 0) : HasOddDen (n : ℚ)⁻¹ := by
  unfold HasOddDen
  have h_pos : 0 < n := by omega
  have h_den : ((n : ℚ)⁻¹).den = n := by
    exact Rat.inv_natCast_den_of_pos h_pos
  rw [h_den]
  exact hn
