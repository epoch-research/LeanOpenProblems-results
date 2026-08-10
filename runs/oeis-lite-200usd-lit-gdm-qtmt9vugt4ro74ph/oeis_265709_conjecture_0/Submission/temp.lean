import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

lemma q_adic_contradiction (q1 q2 : ℚ) (hq1_pos : q1.num > 0) (hq2_pos : q2.num > 0)
  (hden12 : (q1 * q2).den = 1) (h_cop : q1.den.Coprime q2.den)
  (q : ℕ) (hq_prime : q.Prime) (hq_dvd : q ∣ q1.den) : False := by
  have h_prime_fact : Fact q.Prime := ⟨hq_prime⟩
  have h_val_n : padicValRat q (q1 * q2) ≥ 0 := by
    exact padicValRat_nonneg_of_den_eq_one q hq_prime _ hden12
  have h_val_mul : padicValRat q (q1 * q2) = padicValRat q q1 + padicValRat q q2 := by
    exact padicValRat.mul q1 q2
  have h_val_q1 : padicValRat q q1 = padicValInt q q1.num - padicValNat q q1.den := by
    exact padicValRat_def q q1
  have h_val_q2 : padicValRat q q2 = padicValInt q q2.num - padicValNat q q2.den := by
    exact padicValRat_def q q2
  have h_num1_cop : q1.num.natAbs.Coprime q1.den := q1.reduced
  have h_q_not_dvd_num1 : ¬ (q : ℤ) ∣ q1.num := by
    intro h_dvd
    have h_dvd' : q ∣ q1.num.natAbs := by
      exact_mod_cast h_dvd
    have h_gcd : q ∣ Nat.gcd q1.num.natAbs q1.den := Nat.dvd_gcd h_dvd' hq_dvd
    rw [h_num1_cop] at h_gcd
    have : q ≤ 1 := Nat.le_of_dvd (by decide) h_gcd
    have : q ≥ 2 := hq_prime.two_le
    omega
  have h_val_num1 : padicValInt q q1.num = 0 := by
    exact padicValInt.eq_zero_of_not_dvd h_q_not_dvd_num1
  have h_val_den1 : padicValNat q q1.den ≥ 1 := by
    exact one_le_padicValNat_of_dvd (by omega) hq_dvd
  have h_q_not_dvd_den2 : ¬ q ∣ q2.den := by
    intro h_dvd
    have h_gcd : q ∣ Nat.gcd q1.den q2.den := Nat.dvd_gcd hq_dvd h_dvd
    rw [h_cop] at h_gcd
    have : q ≤ 1 := Nat.le_of_dvd (by decide) h_gcd
    have : q ≥ 2 := hq_prime.two_le
    omega
  have h_val_den2 : padicValNat q q2.den = 0 := by
    exact padicValNat.eq_zero_of_not_dvd h_q_not_dvd_den2
  have h_val_q1_neg : padicValRat q q1 ≤ -1 := by
    rw [h_val_q1, h_val_num1]
    omega
  have h_val_q2_nonneg : padicValRat q q2 ≥ 0 := by
    rw [h_val_q2, h_val_den2]
    simp only [CharP.cast_eq_zero, sub_zero, Int.cast_nonneg]
    exact padicValInt_nonneg q q2.num
  omega
