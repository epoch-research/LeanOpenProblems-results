import Submission.MixedTotientAverage

/-!
# A reciprocal-totient harmonic bound with absolute constant two

A finite local Euler product is evaluated through 29; its remaining
factors are controlled by a telescoping sum over all integers.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

lemma sum_reciprocal_successive_tail (a b : ℕ) (ha : 1 ≤ a) :
    (∑ n ∈ Icc (a+1) b, 1/((n : ℝ)*((n : ℝ)-1))) ≤ 1/(a : ℝ) := by
  by_cases hab : a+1 ≤ b
  · have hsum : (∑ n ∈ Icc (a+1) b, 1/((n : ℝ)*((n : ℝ)-1))) =
        1/(a : ℝ)-1/(b : ℝ) := by
      have h := sum_Ico_sub (fun n : ℕ => 1/(n : ℝ)) (show a ≤ b by omega)
      have heq : (∑ n ∈ Icc (a+1) b, 1/((n : ℝ)*((n : ℝ)-1))) =
          ∑ n ∈ Ico a b, (1/(n : ℝ)-1/(n+1 : ℝ)) := by
        rw [show Icc (a+1) b = Ico (a+1) (b+1) by ext n; simp]
        rw [← Finset.sum_Ico_add' (fun n : ℕ => 1/((n : ℝ)*((n : ℝ)-1))) a b 1]
        apply sum_congr rfl
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (ha.trans (mem_Ico.mp hn).1)
        push_cast
        have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
        field_simp [hn0.ne', hn1]
        ring
      rw [heq]
      calc
        _ = -(∑ n ∈ Ico a b, (1/((n+1 : ℕ) : ℝ)-1/(n : ℝ))) := by
          rw [← Finset.sum_neg_distrib]
          apply sum_congr rfl
          intro n hn
          push_cast
          ring
        _ = _ := by rw [h]; ring
    rw [hsum]
    exact sub_le_self _ (by positivity)
  · rw [Icc_eq_empty_of_lt (by omega)]
    simp

lemma reciprocal_totient_euler_product_le_two (A : ℕ) :
    (∏ p ∈ (A+1).primesBelow, (1+1/((p : ℝ)*((p : ℝ)-1)))) ≤ 2 := by
  let P := (A+1).primesBelow
  let f : ℕ → ℝ := fun p => 1+1/((p : ℝ)*((p : ℝ)-1))
  have hf (p : ℕ) (hp : p.Prime) : 1 ≤ f p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hh : 0 ≤ 1/((p : ℝ)*((p : ℝ)-1)) :=
      div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
    dsimp [f]
    linarith
  have hsmall : (∏ p ∈ P with p ≤ 29, f p) ≤ (∏ p ∈ (30 : ℕ).primesBelow, f p) := by
    have hsub : P.filter (fun p => p ≤ 29) ⊆ (30 : ℕ).primesBelow := by
      intro p hp
      obtain ⟨hpP,hp29⟩ := mem_filter.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by omega,(Nat.mem_primesBelow.mp hpP).2⟩
    have hrest : 1 ≤ ∏ p ∈ (30 : ℕ).primesBelow \ P.filter (fun p => p ≤ 29), f p := by
      calc
        _ = ∏ _p ∈ (30 : ℕ).primesBelow \ P.filter (fun p => p ≤ 29), (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num)
          (fun p hp => hf p (Nat.mem_primesBelow.mp (mem_sdiff.mp hp).1).2)
    calc
      _ = 1*(∏ p ∈ P with p ≤ 29, f p) := by ring
      _ ≤ (∏ p ∈ (30 : ℕ).primesBelow \ P.filter (fun p => p ≤ 29), f p) *
          (∏ p ∈ P with p ≤ 29, f p) :=
        mul_le_mul_of_nonneg_right hrest (Finset.prod_nonneg (fun p hp =>
          (by norm_num : (0 : ℝ) ≤ 1).trans (hf p (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2)))
      _ = _ := Finset.prod_sdiff hsub
  have htailSum : (∑ p ∈ P with ¬p ≤ 29, 1/((p : ℝ)*((p : ℝ)-1))) ≤ 1/29 := by
    have hsub : P.filter (fun p => ¬p ≤ 29) ⊆ Icc 30 (A+1) := by
      intro p hp
      obtain ⟨hpP,hp29⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨by omega,by have := (Nat.mem_primesBelow.mp hpP).1; omega⟩
    apply le_trans (sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_))
      (sum_reciprocal_successive_tail 29 (A+1) (by norm_num))
    have hpR : (30 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp hp).1
    exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have htail : (∏ p ∈ P with ¬p ≤ 29, f p) ≤ (29/28 : ℝ) := by
    calc
      _ ≤ ∏ p ∈ P with ¬p ≤ 29, Real.exp (1/((p : ℝ)*((p : ℝ)-1))) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact (by norm_num : (0 : ℝ) ≤ 1).trans (hf p (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2)
        · intro p hp
          simpa only [f,add_comm] using Real.add_one_le_exp (1/((p : ℝ)*((p : ℝ)-1)))
      _ = Real.exp (∑ p ∈ P with ¬p ≤ 29, 1/((p : ℝ)*((p : ℝ)-1))) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (1/29) := Real.exp_le_exp.mpr htailSum
      _ ≤ 29/28 := by
        convert Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/29) (by norm_num : (1/29 : ℝ) < 1) using 1
        norm_num
  have hsmallExact : (∏ p ∈ (30 : ℕ).primesBelow, f p) * (29/28 : ℝ) ≤ 2 := by
    have hset : (30 : ℕ).primesBelow = {2,3,5,7,11,13,17,19,23,29} := by decide
    rw [hset]
    norm_num [f]
  calc
    _ = (∏ p ∈ P with p ≤ 29, f p)*(∏ p ∈ P with ¬p ≤ 29, f p) :=
      (Finset.prod_filter_mul_prod_filter_not P (fun p => p ≤ 29) f).symm
    _ ≤ (∏ p ∈ (30 : ℕ).primesBelow, f p)*(29/28 : ℝ) :=
      mul_le_mul hsmall htail (Finset.prod_nonneg (fun p hp =>
        (by norm_num : (0 : ℝ) ≤ 1).trans (hf p (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2)))
        (Finset.prod_nonneg (fun p hp => (by norm_num : (0 : ℝ) ≤ 1).trans (hf p (Nat.mem_primesBelow.mp hp).2)))
    _ ≤ _ := hsmallExact

theorem sum_reciprocal_totient_le_two_harmonic (A : ℕ) :
    (∑ n ∈ Icc 1 A, 1/(n.totient : ℝ)) ≤ 2*(harmonic A : ℝ) := by
  let w : ℕ → ℝ := fun p => 1/((p : ℝ)-1)
  let Q := (A+1).primesBelow
  have hw (p : ℕ) (hp : p.Prime) : 0 ≤ w p := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    dsimp [w]
    exact div_nonneg (by norm_num) (by linarith)
  have hprod : (∏ p ∈ Q, (1+w p/(p : ℝ))) ≤ 2 := by
    convert reciprocal_totient_euler_product_le_two A using 1
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [w]
    rw [div_div, mul_comm]
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
    _ ≤ (harmonic A : ℝ)*2 := mul_le_mul_of_nonneg_left hprod hH
    _ = _ := mul_comm _ _

end Erdos821.Sieve
