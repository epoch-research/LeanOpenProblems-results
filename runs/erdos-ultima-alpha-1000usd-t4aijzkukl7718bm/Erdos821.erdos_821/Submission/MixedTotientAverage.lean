import Submission.MixedPrimePairBound

/-!
# A small absolute constant for the reciprocal-totient harmonic average
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

lemma sum_reciprocal_successive_factors (A : ℕ) :
    (∑ n ∈ Icc 2 (A+1), 1/((n : ℝ)*((n : ℝ)-1))) = 1-1/(A+1 : ℝ) := by
  induction A with
  | zero => simp
  | succ A hA =>
    rw [show A+1+1 = (A+1)+1 by omega, sum_Icc_succ_top (by omega), hA]
    push_cast
    have ha : (A : ℝ)+1 ≠ 0 := by positivity
    have hb : (A : ℝ)+1+1 ≠ 0 := by positivity
    field_simp
    ring

/-- A uniform bound sufficient to avoid any large unspecified sieve constant. -/
theorem sum_reciprocal_totient_le_three_harmonic (A : ℕ) :
    (∑ n ∈ Icc 1 A, 1/(n.totient : ℝ)) ≤ 3*(harmonic A : ℝ) := by
  let w : ℕ → ℝ := fun p => 1/((p : ℝ)-1)
  let Q := (A+1).primesBelow
  have hw (p : ℕ) (hp : p.Prime) : 0 ≤ w p := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    dsimp [w]
    exact div_nonneg (by norm_num) (by linarith)
  have hsum : (∑ p ∈ Q, w p/(p : ℝ)) ≤ 1 := by
    have hsub : Q ⊆ Icc 2 (A+1) := by
      intro p hp
      obtain ⟨hpA,hpprime⟩ := Nat.mem_primesBelow.mp hp
      exact mem_Icc.mpr ⟨hpprime.two_le,by omega⟩
    calc
      _ = ∑ p ∈ Q, 1/((p : ℝ)*((p : ℝ)-1)) := by
        apply sum_congr rfl
        intro p hp
        dsimp [w]
        rw [div_div, mul_comm]
      _ ≤ ∑ p ∈ Icc 2 (A+1), 1/((p : ℝ)*((p : ℝ)-1)) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp hp).1
        exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
      _ = 1-1/(A+1 : ℝ) := sum_reciprocal_successive_factors A
      _ ≤ 1 := sub_le_self _ (by positivity)
  have hprod : (∏ p ∈ Q, (1+w p/(p : ℝ))) ≤ 3 := by
    calc
      _ ≤ ∏ p ∈ Q, Real.exp (w p/(p : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact add_nonneg zero_le_one (div_nonneg (hw p (Nat.mem_primesBelow.mp hp).2) (Nat.cast_nonneg _))
        · intro p hp
          simpa only [add_comm] using Real.add_one_le_exp (w p/(p : ℝ))
      _ = Real.exp (∑ p ∈ Q, w p/(p : ℝ)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum
      _ ≤ 3 := Real.exp_one_lt_three.le
  have havg := harmonic_average_prime_product_le A w (fun p hp => hw p (Nat.mem_primesBelow.mp hp).2)
  have heq (n : ℕ) (hn : n ∈ Icc 1 A) :
      1/(n.totient : ℝ) = (∏ p ∈ n.primeFactors, (1+w p))/(n : ℝ) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from (mem_Icc.mp hn).1).ne'
    have hprod' : ∏ p ∈ n.primeFactors, (1+w p) = (n : ℝ)/n.totient := by
      rw [totient_ratio_eq_prime_product n (mem_Icc.mp hn).1]
      apply prod_congr rfl
      intro p hp
      have hpR : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      dsimp [w]
      have hp1 : (p : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
      field_simp [hp1]
      ring
    rw [hprod']
    field_simp
  have hH : 0 ≤ (harmonic A : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  calc
    _ = ∑ n ∈ Icc 1 A, (∏ p ∈ n.primeFactors, (1+w p))/(n : ℝ) := sum_congr rfl heq
    _ ≤ (harmonic A : ℝ)*(∏ p ∈ Q, (1+w p/(p : ℝ))) := havg
    _ ≤ (harmonic A : ℝ)*3 := mul_le_mul_of_nonneg_left hprod hH
    _ = _ := mul_comm _ _

end Erdos821.Sieve
