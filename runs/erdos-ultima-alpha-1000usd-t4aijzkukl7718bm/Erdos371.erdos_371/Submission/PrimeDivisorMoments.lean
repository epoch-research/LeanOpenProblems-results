import Submission.SieveFactorMean

/-! Elementary second moments for nonnegative sums over the prime divisors
of an integer. These bounds concern a single integer, not shifted correlations. -/

namespace Erdos371
namespace FiniteSieve
open Finset

lemma prime_pair_divisibility_count (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (((range N).filter (fun n => p ∣ n+1 ∧ q ∣ n+1)).card : ℝ) ≤
      (N : ℝ)/((p : ℝ)*q) + if p=q then (N : ℝ)/p else 0 := by
  classical
  by_cases he : p=q
  · subst q
    simp only [and_self, if_true, Nat.card_multiples]
    exact (Nat.cast_div_le (m := N) (n := p)).trans (le_add_of_nonneg_left (by positivity))
  · have hc : p.Coprime q := (Nat.coprime_primes hp hq).mpr he
    have heq (n : ℕ) : (p ∣ n+1 ∧ q ∣ n+1) ↔ p*q ∣ n+1 := by
      exact ⟨fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2,
        fun h => ⟨(Nat.dvd_mul_right p q).trans h, (Nat.dvd_mul_left q p).trans h⟩⟩
    simp only [heq, Nat.card_multiples, if_neg he, add_zero]
    simpa only [Nat.cast_mul] using (Nat.cast_div_le (m := N) (n := p*q) (α := ℝ))

/-- A finite second-moment bound using only exact counts of multiples. -/
theorem prime_divisor_sum_sq_mean_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p ∈ S, 0 ≤ w p) (N : ℕ) :
    (∑ n ∈ range N, (∑ p ∈ S, if p ∣ n+1 then w p else 0)^2) ≤
      N * ((∑ p ∈ S, w p/p)^2 + ∑ p ∈ S, (w p)^2/p) := by
  classical
  have hpq (p q : ℕ) (hp : p ∈ S) (hq : q ∈ S) :
      (∑ n ∈ range N, (if p ∣ n+1 then w p else 0) *
        (if q ∣ n+1 then w q else 0)) ≤
      N * (w p/p)*(w q/q) + if p=q then N*(w p)^2/p else 0 := by
    have ht (n : ℕ) : (if p ∣ n+1 then w p else 0) *
        (if q ∣ n+1 then w q else 0) =
      if p ∣ n+1 ∧ q ∣ n+1 then w p*w q else 0 := by
      split_ifs <;> simp_all
    simp_rw [ht]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hb := mul_le_mul_of_nonneg_right (prime_pair_divisibility_count N p q (hS p hp) (hS q hq))
      (mul_nonneg (hw p hp) (hw q hq))
    convert hb using 1
    by_cases he : p=q
    · subst q
      simp only [if_true]
      ring
    · simp only [if_neg he]
      ring
  calc
    _ = ∑ p ∈ S, ∑ q ∈ S, ∑ n ∈ range N,
        (if p ∣ n+1 then w p else 0) * (if q ∣ n+1 then w q else 0) := by
      simp only [pow_two, sum_mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      rw [sum_comm]
    _ ≤ ∑ p ∈ S, ∑ q ∈ S,
        (N * (w p/p)*(w q/q) + if p=q then N*(w p)^2/p else 0) :=
      sum_le_sum fun p hp => sum_le_sum fun q hq => hpq p q hp hq
    _ = _ := by
      simp only [sum_add_distrib, sum_mul, mul_sum, mul_add, pow_two]
      apply congrArg₂ (· + ·)
      · apply sum_congr rfl
        intro p hp
        apply sum_congr rfl
        intro q hq
        ring
      · apply sum_congr rfl
        intro p hp
        simp only [sum_ite_eq, if_pos hp, mul_div_assoc]

noncomputable def squarefreeSmallPrimeLog (B n : ℕ) : ℝ :=
  ∑ p ∈ B.primesBelow, if p ∣ n then Real.log p else 0

lemma squarefreeSmallPrimeLog_nonneg (B n : ℕ) : 0 ≤ squarefreeSmallPrimeLog B n := by
  apply sum_nonneg
  intro p hp
  split_ifs
  · exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_le)
  · rfl

lemma prime_log_div_sum_le (B : ℕ) :
    (∑ p ∈ B.primesBelow, Real.log p / (p : ℝ)) ≤ 4 * Real.log B := by
  apply le_trans _ (prime_log_div_pred_sum_le B)
  apply sum_le_sum
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
  apply div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) (by linarith) (by linarith)

lemma prime_log_sq_div_sum_le (B : ℕ) :
    (∑ p ∈ B.primesBelow, (Real.log p)^2 / (p : ℝ)) ≤ 4 * (Real.log B)^2 := by
  calc
    _ ≤ ∑ p ∈ B.primesBelow, Real.log B * (Real.log p / (p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpB,hpp⟩ := Nat.mem_primesBelow.mp hp
      have hlog := Real.log_le_log (by exact_mod_cast hpp.pos : (0 : ℝ) < p)
        (by exact_mod_cast hpB.le : (p : ℝ) ≤ B)
      have hnonneg : 0 ≤ Real.log p / (p : ℝ) := div_nonneg
        (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (Nat.cast_nonneg p)
      have h := mul_le_mul_of_nonneg_right hlog hnonneg
      convert h using 1 <;> ring
    _ = Real.log B * (∑ p ∈ B.primesBelow, Real.log p / (p : ℝ)) := (mul_sum _ _ _).symm
    _ ≤ Real.log B * (4 * Real.log B) :=
      mul_le_mul_of_nonneg_left (prime_log_div_sum_le B) (Real.log_natCast_nonneg B)
    _ = _ := by ring

/-- A quadratic logarithmic-mass estimate, stronger than the first-moment
bound for controlling integers with exceptionally many small prime factors. -/
theorem squarefreeSmallPrimeLog_second_moment (B N : ℕ) :
    (∑ n ∈ range N, (squarefreeSmallPrimeLog B (n+1))^2) ≤
      20 * N * (Real.log B)^2 := by
  have hw (p : ℕ) (hp : p ∈ B.primesBelow) : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_le)
  have hm := prime_divisor_sum_sq_mean_le B.primesBelow
    (fun p hp => (Nat.mem_primesBelow.mp hp).2) (fun p => Real.log p) hw N
  have hmassnonneg : 0 ≤ ∑ p ∈ B.primesBelow, Real.log p / (p : ℝ) :=
    sum_nonneg fun p hp => div_nonneg (hw p hp) (Nat.cast_nonneg p)
  have hsq := pow_le_pow_left₀ hmassnonneg (prime_log_div_sum_le B) 2
  have hlog2 := prime_log_sq_div_sum_le B
  have hb : (∑ p ∈ B.primesBelow, Real.log p/(p : ℝ))^2 +
      (∑ p ∈ B.primesBelow, (Real.log p)^2/(p : ℝ)) ≤ 20*(Real.log B)^2 := by
    nlinarith
  exact hm.trans (by
    have h := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) N)
    convert h using 1 <;> ring)

#print axioms squarefreeSmallPrimeLog_second_moment
end FiniteSieve
end Erdos371
