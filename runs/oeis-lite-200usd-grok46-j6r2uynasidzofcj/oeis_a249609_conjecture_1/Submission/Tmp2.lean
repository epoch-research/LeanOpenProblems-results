import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open Nat

lemma descFactorial_ten (n : ℕ) :
    n.descFactorial 10 =
      (n - 9) * (n - 8) * (n - 7) * (n - 6) * (n - 5) *
        (n - 4) * (n - 3) * (n - 2) * (n - 1) * n := by
  simp [Nat.descFactorial_succ]
  ring

lemma choose_two_pow_ten (m : ℕ) (hm : 10 ≤ m) :
    Nat.choose (2 ^ m) 10 =
      2 ^ (m - 1) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
          (2 ^ m - 9) / 14175) := by
  have h10le : 10 ≤ 2 ^ m := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 10 ≤ 16 := by decide
         _ = 2 ^ 4 := by decide
         _ ≤ 2 ^ m := this
  have hdesc : (2 ^ m).descFactorial 10 =
      (2 ^ m - 9) * (2 ^ m - 8) * (2 ^ m - 7) * (2 ^ m - 6) * (2 ^ m - 5) *
        (2 ^ m - 4) * (2 ^ m - 3) * (2 ^ m - 2) * (2 ^ m - 1) * 2 ^ m :=
    descFactorial_ten _
  have h8 : 2 ^ m - 8 = 8 * (2 ^ (m - 3) - 1) := by
    have : 2 ^ m = 8 * 2 ^ (m - 3) := by
      have : 2 ^ m = 2 ^ (m - 3 + 3) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_add]
      have : (2 : ℕ) ^ 3 = 8 := by decide
      rw [this, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 3) := Nat.one_le_pow _ _ (by decide)
    omega
  have h4 : 2 ^ m - 4 = 4 * (2 ^ (m - 2) - 1) := by
    have : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have : 2 ^ m = 2 ^ (m - 2 + 2) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_add, pow_two, mul_comm]
      ring
    have hle : 1 ≤ 2 ^ (m - 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have h2 : 2 ^ m - 2 = 2 * (2 ^ (m - 1) - 1) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have h6 : 2 ^ m - 6 = 2 * (2 ^ (m - 1) - 3) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 3 ≤ 2 ^ (m - 1) := by
      have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      calc 3 ≤ 4 := by decide
           _ = 2 ^ 2 := by decide
           _ ≤ 2 ^ (m - 1) := this
    omega
  have hprod :
      (2 ^ m).descFactorial 10 =
        2 ^ (m + 7) *
          ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
            (2 ^ m - 9)) := by
    rw [hdesc, h8, h4, h2, h6]
    ring_nf
  have hfac : (2 ^ m).descFactorial 10 = 3628800 * Nat.choose (2 ^ m) 10 := by
    have : 10 ! = 3628800 := by decide
    rw [Nat.descFactorial_eq_factorial_mul_choose, this]
  rw [hprod] at hfac
  have h256 : 2 ^ (m + 7) = 256 * 2 ^ (m - 1) := by
    have : m + 7 = (m - 1) + 8 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 8 = 256 from rfl, mul_comm]
  rw [h256] at hfac
  have : 256 * (2 ^ (m - 1) *
      ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
        (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
        (2 ^ m - 9))) =
      256 * (14175 * Nat.choose (2 ^ m) 10) := by
    have h3628800 : (3628800 : ℕ) = 256 * 14175 := by decide
    rw [h3628800] at hfac
    convert hfac using 1 <;> ring
  have hcancel := Nat.mul_left_cancel (by decide : 0 < 256) this
  have h14175dvd : 14175 ∣ (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) *
      (2 ^ (m - 2) - 1) * (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) *
      (2 ^ (m - 3) - 1) * (2 ^ m - 9) := by
    have : 14175 ∣ 2 ^ (m - 1) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
          (2 ^ m - 9)) :=
      ⟨Nat.choose (2 ^ m) 10, by
        have := hcancel.symm
        convert this using 1 <;> ring⟩
    have hcop : Nat.Coprime 14175 (2 ^ (m - 1)) := by
      have : Nat.Coprime 14175 2 := by decide
      simpa using this.pow_right (m - 1)
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop this
  have : Nat.choose (2 ^ m) 10 =
      (2 ^ (m - 1) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
          (2 ^ m - 9))) / 14175 := by
    apply Nat.eq_div_of_mul_eq_left (by decide : (14175 : ℕ) ≠ 0)
    convert hcancel.symm using 1 <;> ring
  rw [this, Nat.mul_div_assoc _ h14175dvd]
