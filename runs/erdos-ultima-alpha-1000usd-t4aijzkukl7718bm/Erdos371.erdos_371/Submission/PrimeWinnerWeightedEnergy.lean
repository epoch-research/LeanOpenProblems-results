import Submission.PrimeLoserWeightedBound

/-! A cofactor-weighted bound for the actual prime-winner energy.
The main term saves a logarithm of the cofactor range. -/
namespace Erdos371
open Finset FiniteSieve

lemma primeWinnerSum_sq_le_weighted_loser_count (p N : ℕ) (hp : 0 < p) :
    (primeWinnerSum p N)^2 ≤ (2*(N : ℝ)/p+1)*
      ((((range N).filter fun n => primeLoser n = p).card : ℝ)+
        if Nat.maxPrimeFac N = p then 1 else 0) := by
  have hM : ‖primeWinnerSum p N‖ ≤ 2*(N : ℝ)/p+1 := by
    have hd := Nat.cast_div_le (α := ℝ) (m := N) (n := p)
    have hh := primeWinnerSum_norm_le_multiples p N
    simp only [mul_div_assoc]
    linarith
  have hL := primeWinnerSum_norm_le_loser_count p N hp
  have hh := mul_le_mul hM hL (norm_nonneg (primeWinnerSum p N))
    (show 0 ≤ 2*(N : ℝ)/p+1 by positivity)
  simpa only [← pow_two,Real.norm_eq_abs,sq_abs] using hh

/-- The endpoint correction is bounded only once, not once per prime. -/
theorem primeWinnerEnergyAbove_le_weightedLoserCount (B X N : ℕ)
    (hNX : N ≤ X*(B+1)) :
    primeWinnerEnergyAbove B N ≤ weightedLoserCount B N+(2*X+1 : ℝ) := by
  let S := (primeWinnerLabels N).filter (B < ·)
  let m (p : ℕ) : ℝ := 2*(N : ℝ)/p+1
  have hm0 (p : ℕ) : 0 ≤ m p := by dsimp [m]; positivity
  have hsum : primeWinnerEnergyAbove B N ≤
      (∑ p ∈ S, m p*((((range N).filter fun n => primeLoser n=p).card : ℝ)))+
        ∑ p ∈ S, m p*(if Nat.maxPrimeFac N=p then 1 else 0) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hpos : 0 < p := by have := (mem_filter.mp hp).2; omega
    convert primeWinnerSum_sq_le_weighted_loser_count p N hpos using 1
    dsimp [m]
    ring
  have hrow (p : ℕ) : m p*((((range N).filter fun n => primeLoser n=p).card : ℝ)) =
      ∑ n ∈ range N, if primeLoser n=p then m p else 0 := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    ring
  have hlos : (∑ p ∈ S, m p*((((range N).filter fun n => primeLoser n=p).card : ℝ))) ≤
      weightedLoserCount B N := by
    simp_rw [hrow]
    rw [sum_comm,weightedLoserCount,bothAboveSet,sum_filter]
    apply sum_le_sum
    intro n hn
    rw [sum_ite_eq]
    by_cases hs : primeLoser n ∈ S
    · have hB : B < primeLoser n := (mem_filter.mp hs).2
      have hpair : B < Nat.maxPrimeFac n ∧ B < Nat.maxPrimeFac (n+1) := by
        simpa only [primeLoser,lt_min_iff] using hB
      rw [if_pos hs,if_pos hpair]
      rfl
    · rw [if_neg hs]
      split_ifs
      · exact hm0 (primeLoser n)
      · rfl
  have hend : (∑ p ∈ S, m p*(if Nat.maxPrimeFac N=p then 1 else 0)) ≤ (2*X+1 : ℝ) := by
    simp only [mul_ite,mul_one,mul_zero,sum_ite_eq]
    split_ifs with hp
    · have hB : B < Nat.maxPrimeFac N := (mem_filter.mp hp).2
      have hp0 : (0 : ℝ) < Nat.maxPrimeFac N := by exact_mod_cast (show 0 < Nat.maxPrimeFac N by omega)
      have hprod : (N : ℝ) ≤ X*Nat.maxPrimeFac N := by
        exact_mod_cast hNX.trans (Nat.mul_le_mul_left X (by omega))
      have hd : (N : ℝ)/Nat.maxPrimeFac N ≤ X := (div_le_iff₀ hp0).mpr hprod
      dsimp only [m]
      rw [mul_div_assoc]
      linarith
    · positivity
  linarith

/-- For N<=(B+1)^2 and N<=X*(B+1), the main term is of order
N*X*log(X)/log(z)^2. This is a finite uniform estimate, not a bulk
near-linear energy bound. -/
theorem primeWinnerEnergyAbove_weighted_bound (B X z N : ℕ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hzB : z ≤ B)
    (hNX : N ≤ X*(B+1)) (hNB : N ≤ (B+1)^2) :
    primeWinnerEnergyAbove B N ≤
      224*Real.exp 19*(N : ℝ)^2*(1+Real.log X)/
        ((B+1 : ℝ)*(Real.log (z+1 : ℝ))^2)+
      28*(N : ℝ)^3*(z+1 : ℝ)^64/(B+1 : ℝ)^3+(2*X+1 : ℝ) := by
  exact (primeWinnerEnergyAbove_le_weightedLoserCount B X N hNX).trans
    (add_le_add_left (weightedLoserCount_bound B X z N hB hz hzB hNX hNB) _)

#print axioms primeWinnerEnergyAbove_le_weightedLoserCount
#print axioms primeWinnerEnergyAbove_weighted_bound
end Erdos371
