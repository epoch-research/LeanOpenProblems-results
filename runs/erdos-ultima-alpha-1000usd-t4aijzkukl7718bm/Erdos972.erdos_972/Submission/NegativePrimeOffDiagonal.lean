import Submission.PrimeRemainderProfileIdentity

/-! An exact negative value of the genuine prime-factor off-diagonal at an
irrational slope. This refutes unconditional nonnegativity of that raw sum,
not the prime-pair conjecture or a lower bound restricted to large good scales. -/
namespace Erdos972NegativePrimeOffDiagonal

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972PrimePowerError Erdos972MellinDivisorCoefficient
open Erdos972PrimeFactorRemainder Erdos972FourFactorDiagonalSplit
open Erdos972PrimeRemainderProfileIdentity Erdos972TypeIPolynomial
open Erdos972DivisorCovariance
set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def slope : ℝ := 6 + Real.sqrt 2 / 100

lemma slope_irrational : Irrational slope := by
  exact (irrational_sqrt_two.div_natCast (by decide : (100 : ℕ) ≠ 0)).natCast_add 6

lemma slope_gt_one : 1 < slope := by
  unfold slope
  have := Real.sqrt_nonneg (2 : ℝ)
  linarith

lemma slope_floor {n : ℕ} (hn : n ≤ 35) : floorMul slope n = 6*n := by
  unfold floorMul slope
  apply (Nat.floor_eq_iff (by positivity)).mpr
  push_cast
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn35 : (n : ℝ) ≤ 35 := Nat.cast_le.mpr hn
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hs' := Real.sqrt_two_lt_three_halves
  constructor
  · nlinarith [mul_nonneg hs hn0]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3/2-Real.sqrt 2) hn0]

lemma divisorCoeff_three {n : ℕ} (hn : 1 < n) :
    divisorCoeff 3 n = -1 + (if 2 ∣ n then 1 else 0) + (if 3 ∣ n then 1 else 0) := by
  classical
  rw [divisorCoeff_eq, ArithmeticFunction.one_apply, if_neg (by omega),
    ArithmeticFunction.coe_mul_zeta_apply]
  simp only [cutoff_apply]
  rw [truncated_divisor_sum 3 n _ (by omega)]
  unfold divisorPolynomial
  have hI : Ioc 0 3 = ({1,2,3} : Finset ℕ) := by decide
  rw [hI]
  norm_num [moebius_apply_prime (by decide : Nat.Prime 2),
    moebius_apply_prime (by decide : Nat.Prime 3)]
  split_ifs <;> norm_num

lemma tail_prime_five : tail primeMangoldt 3 5 = Real.log 5 := by
  rw [tail_eq_of_lt _ (by decide)]
  change (if Nat.Prime 5 then Λ 5 else 0) = _
  rw [if_pos (by decide), vonMangoldt_apply_prime (by decide)]
  norm_num

lemma tail_prime_seven : tail primeMangoldt 3 7 = Real.log 7 := by
  rw [tail_eq_of_lt _ (by decide)]
  change (if Nat.Prime 7 then Λ 7 else 0) = _
  rw [if_pos (by decide), vonMangoldt_apply_prime (by decide)]
  norm_num

lemma supported_tuples {m p k q : ℕ}
    (hmp : m*p ≤ 35) (hm : 3 < m) (hp3 : 3 < p) (_hk : 3 < k) (hq3 : 3 < q)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hrel : k*q = 6*(m*p)) :
    (m = 7 ∧ p = 5 ∧ k = 30 ∧ q = 7) ∨
    (m = 5 ∧ p = 7 ∧ k = 42 ∧ q = 5) := by
  have hq6 : ¬ q ∣ 6 := by
    intro hd
    have hqle : q ≤ 6 := Nat.le_of_dvd (by decide) hd
    interval_cases q <;> norm_num at *
  have hqm : q ∣ m := by
    have hd : q ∣ 6*(m*p) := hrel ▸ dvd_mul_left q k
    have hd' : q ∣ m*p := (hq.dvd_mul.mp hd).resolve_left hq6
    exact (hq.dvd_mul.mp hd').resolve_right (fun h => hpq ((hp.dvd_iff_eq hq.ne_one).mp h))
  have hqmle : q ≤ m := Nat.le_of_dvd (by omega) hqm
  have hpqle : p*q ≤ 35 := (Nat.mul_le_mul_left p hqmle).trans (by simpa [mul_comm] using hmp)
  have hp5 : 5 ≤ p := by
    by_contra hh
    have : p = 4 := by omega
    subst p
    norm_num at hp
  have hq5 : 5 ≤ q := by
    by_contra hh
    have : q = 4 := by omega
    subst q
    norm_num at hq
  have hp7 : p ≤ 7 := by nlinarith
  have hq7 : q ≤ 7 := by nlinarith
  have hp57 : p = 5 ∨ p = 7 := by
    interval_cases p <;> norm_num at *
  have hq57 : q = 5 ∨ q = 7 := by
    interval_cases q <;> norm_num at *
  rcases hp57 with rfl | rfl <;> rcases hq57 with rfl | rfl
  · exact (hpq rfl).elim
  · have hm7 : m = 7 := by omega
    subst m
    left
    omega
  · have hm5 : m = 5 := by omega
    subst m
    right
    omega
  · exact (hpq rfl).elim

noncomputable def term (α : ℝ) (m p k q : ℕ) : ℝ :=
  divisorCoeff 3 m * tail primeMangoldt 3 p * divisorCoeff 3 k * tail primeMangoldt 3 q *
    (if k*q = floorMul α (m*p) ∧ p ≠ q then 1 else 0)

lemma term_eq (α : ℝ) (hf : ∀ n ≤ 35, floorMul α n = 6*n)
    {m p k q : ℕ} (hmp : m*p ≤ 35) :
    term α m p k q =
      (if m = 7 then if p = 5 then if k = 30 then if q = 7 then
        -Real.log 5*Real.log 7 else 0 else 0 else 0 else 0) +
      (if m = 5 then if p = 7 then if k = 42 then if q = 5 then
        -Real.log 5*Real.log 7 else 0 else 0 else 0 else 0) := by
  classical
  have ha5 : divisorCoeff 3 5 = -1 := divisorCoeff_prime (by decide) (by decide) (by decide)
  have ha7 : divisorCoeff 3 7 = -1 := divisorCoeff_prime (by decide) (by decide) (by decide)
  have ha30 : divisorCoeff 3 30 = 1 := by norm_num [divisorCoeff_three (by decide : 1 < 30)]
  have ha42 : divisorCoeff 3 42 = 1 := by norm_num [divisorCoeff_three (by decide : 1 < 42)]
  have hc5 : term α 7 5 30 7 = -Real.log 5*Real.log 7 := by
    simp [term, hf 35 (by decide), ha7, ha30, tail_prime_five, tail_prime_seven]
  have hc7 : term α 5 7 42 5 = -Real.log 5*Real.log 7 := by
    simp [term, hf 35 (by decide), ha5, ha42, tail_prime_five, tail_prime_seven, mul_comm]
  by_cases hA : m = 7 ∧ p = 5 ∧ k = 30 ∧ q = 7
  · rcases hA with ⟨rfl, rfl, rfl, rfl⟩
    simpa using hc5
  by_cases hB : m = 5 ∧ p = 7 ∧ k = 42 ∧ q = 5
  · rcases hB with ⟨rfl, rfl, rfl, rfl⟩
    simpa using hc7
  have hz : term α m p k q = 0 := by
    by_contra h
    obtain ⟨hm, hp3, hk, hq3, hp, hq, hpq, hrel⟩ := prime_offDiagonal_support α 3 3 m p k q h
    rw [hf (m*p) hmp] at hrel
    exact (supported_tuples hmp hm hp3 hk hq3 hp hq hpq hrel).elim hA hB
  rw [hz]
  split_ifs <;> simp_all

lemma offDiagonal_eq_of_floor (α : ℝ) (hf : ∀ n ≤ 35, floorMul α n = 6*n) :
    primeFactorOffDiagonal α 35 3 3 = -2*Real.log 5*Real.log 7 := by
  classical
  unfold primeFactorOffDiagonal factorOffDiagonal
  simp_rw [mul_sum, ← mul_assoc]
  change (∑ m ∈ Ioc 0 35, ∑ p ∈ Ioc 0 (35/m), ∑ k ∈ Ioc 0 (floorMul α 35),
    ∑ q ∈ Ioc 0 (floorMul α 35/k), term α m p k q) = _
  rw [hf 35 (by decide)]
  trans (∑ m ∈ Ioc 0 35, ∑ p ∈ Ioc 0 (35/m), ∑ k ∈ Ioc 0 210,
    ∑ q ∈ Ioc 0 (210/k),
      ((if m = 7 then if p = 5 then if k = 30 then if q = 7 then
        -Real.log 5*Real.log 7 else 0 else 0 else 0 else 0) +
      (if m = 5 then if p = 7 then if k = 42 then if q = 5 then
        -Real.log 5*Real.log 7 else 0 else 0 else 0 else 0)))
  · apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro q hq
    apply term_eq α hf
    exact (Nat.mul_le_mul_left m (mem_Ioc.mp hp).2).trans (Nat.mul_div_le 35 m)
  · simp only [sum_add_distrib, sum_ite_irrel, sum_const_zero, sum_ite_eq']
    norm_num
    ring

/-- This finite-scale sign check does not disprove infinitude of prime pairs. -/
theorem irrational_negative_offDiagonal :
    1 < slope ∧ Irrational slope ∧ primeFactorOffDiagonal slope 35 3 3 < 0 := by
  refine ⟨slope_gt_one, slope_irrational, ?_⟩
  rw [offDiagonal_eq_of_floor slope (fun _ hn => slope_floor hn)]
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have h7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  nlinarith [mul_pos h5 h7]

#print axioms offDiagonal_eq_of_floor
#print axioms irrational_negative_offDiagonal

end Erdos972NegativePrimeOffDiagonal
