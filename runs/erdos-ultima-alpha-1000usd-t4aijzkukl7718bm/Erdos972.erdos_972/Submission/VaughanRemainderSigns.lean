import Submission.DoubleVaughan

/-! Exact sign checks for the genuine Vaughan remainder. In particular the
Type-I part is not automatically a pointwise Mangoldt majorant. -/
namespace Erdos972VaughanRemainderSigns

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972DoubleVaughan

lemma mangoldt_zero_two_primes {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpn : p ∣ n) (hqn : q ∣ n) : vonMangoldt n = 0 := by
  apply vonMangoldt_eq_zero_iff.mpr
  intro hn
  obtain ⟨r, hr, hu⟩ := isPrimePow_iff_unique_prime_dvd.mp hn
  exact hpq ((hu p ⟨hp, hpn⟩).trans (hu q ⟨hq, hqn⟩).symm)

lemma typeII_thirty : typeIIPart 3 3 30 = Real.log 5 := by
  have hd : (30 : ℕ).divisorsAntidiagonal =
      {(1,30), (2,15), (3,10), (5,6), (6,5), (10,3), (15,2), (30,1)} := by decide
  have h6 : (6 : ℕ).divisors = {1,2,3,6} := by decide
  have hΛ6 : vonMangoldt 6 = 0 := mangoldt_zero_two_primes (by decide : Nat.Prime 2) (by decide : Nat.Prime 3) (by decide) (by decide) (by decide)
  have hΛ10 : vonMangoldt 10 = 0 := mangoldt_zero_two_primes (by decide : Nat.Prime 2) (by decide : Nat.Prime 5) (by decide) (by decide) (by decide)
  have hΛ15 : vonMangoldt 15 = 0 := mangoldt_zero_two_primes (by decide : Nat.Prime 3) (by decide : Nat.Prime 5) (by decide) (by decide) (by decide)
  have hΛ30 : vonMangoldt 30 = 0 := mangoldt_zero_two_primes (by decide : Nat.Prime 2) (by decide : Nat.Prime 3) (by decide) (by decide) (by decide)
  have hμ6 : μ 6 = 1 := by
    rw [show 6 = 2*3 by norm_num, isMultiplicative_moebius.map_mul_of_coprime (by decide),
      moebius_apply_prime (by decide : Nat.Prime 2), moebius_apply_prime (by decide : Nat.Prime 3)]
    norm_num
  unfold typeIIPart
  rw [ArithmeticFunction.mul_apply, hd]
  norm_num only [sum_insert, mem_insert, mem_singleton, Prod.mk.injEq, Nat.reduceEqDiff, and_false,
    false_and, or_self, not_false_eq_true, sum_singleton]
  simp only [tail, Erdos972Vaughan.sub_apply, cutoff_apply, hΛ6, hΛ10, hΛ15, hΛ30,
    vonMangoldt_apply_one, Nat.reduceLeDiff, ite_true, ite_false, sub_self, sub_zero, mul_zero, zero_mul, add_zero, zero_add]
  rw [ArithmeticFunction.coe_mul_zeta_apply, h6]
  norm_num [hμ6, vonMangoldt_apply_prime (by decide : Nat.Prime 5)]

lemma typeII_thirtyfive : typeIIPart 3 3 35 = -(Real.log 5+Real.log 7) := by
  have hd : (35 : ℕ).divisorsAntidiagonal = {(1,35), (5,7), (7,5), (35,1)} := by decide
  have hΛ35 : vonMangoldt 35 = 0 := mangoldt_zero_two_primes (by decide : Nat.Prime 5) (by decide : Nat.Prime 7) (by decide) (by decide) (by decide)
  have h5 : (5 : ℕ).divisors = {1,5} := (by decide : Nat.Prime 5).divisors
  have h7 : (7 : ℕ).divisors = {1,7} := (by decide : Nat.Prime 7).divisors
  have hμ5 : μ 5 = -1 := moebius_apply_prime (by decide)
  have hμ7 : μ 7 = -1 := moebius_apply_prime (by decide)
  unfold typeIIPart
  rw [ArithmeticFunction.mul_apply, hd]
  norm_num only [sum_insert, mem_insert, mem_singleton, Prod.mk.injEq, Nat.reduceEqDiff, and_false,
    false_and, or_self, not_false_eq_true, sum_singleton]
  simp only [tail, Erdos972Vaughan.sub_apply, cutoff_apply, hΛ35, vonMangoldt_apply_one,
    Nat.reduceLeDiff, ite_true, ite_false, sub_self, sub_zero, mul_zero, zero_mul, add_zero, zero_add]
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_mul_zeta_apply, h5, h7]
  norm_num [hμ5, hμ7, vonMangoldt_apply_prime (by decide : Nat.Prime 5), vonMangoldt_apply_prime (by decide : Nat.Prime 7)]

/-- No pointwise sign may be assigned to the large-input remainder. -/
theorem typeII_both_signs :
    (∃ n : ℕ, 0 < typeIIPart 3 3 n) ∧ (∃ n : ℕ, typeIIPart 3 3 n < 0) := by
  refine ⟨⟨30, ?_⟩, ⟨35, ?_⟩⟩
  · rw [typeII_thirty]
    exact Real.log_pos (by norm_num)
  · rw [typeII_thirtyfive]
    have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have h7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
    linarith

/-- In particular the Type-I part cannot be used as an upper sieve without
proving additional pointwise majorant inequalities. -/
theorem typeI_not_mangoldt_majorant : ¬ (∀ n : ℕ, vonMangoldt n ≤ typeIPart 3 3 n) := by
  intro h
  have hh := congrArg (fun f : ArithmeticFunction ℝ => f 30) (mangoldt_split 3 3)
  simp only [ArithmeticFunction.add_apply] at hh
  rw [typeII_thirty] at hh
  linarith [h 30, Real.log_pos (by norm_num : (1 : ℝ)<5)]

#print axioms typeII_both_signs
#print axioms typeI_not_mangoldt_majorant

end Erdos972VaughanRemainderSigns
