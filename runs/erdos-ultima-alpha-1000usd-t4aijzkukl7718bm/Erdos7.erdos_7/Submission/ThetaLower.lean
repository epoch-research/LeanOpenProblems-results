import Submission.ChebyshevTail
import Submission.SharpRawPrefix

/-! An exact finite theta lower bound and its uniform tail consequence. -/
namespace Erdos7ThetaLower
open scoped BigOperators
open Erdos7SharpRawPrefix
set_option maxHeartbeats 4000000

lemma log_lower (p : ℕ) (hp : p.Prime) :
    (69/100 : ℝ)*(Nat.log2 p : ℝ) ≤ Real.log p := by
  have hpow : (2 : ℝ)^(Nat.log2 p) ≤ p := by
    exact_mod_cast (show (2 : ℕ)^(Nat.log2 p) ≤ p by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 hp.ne_zero)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2^(Nat.log2 p)) hpow
  rw [Real.log_pow] at hlog
  have h2 : (69/100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  exact (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)).trans
    (by simpa only [mul_comm] using hlog)

lemma theta_lower : (95000 : ℝ) ≤ Chebyshev.theta 99999 := by
  classical
  have hP : fixedPrimes.toFinset ⊆ (Finset.Icc 0 99999).filter Nat.Prime := by
    intro p hp
    obtain ⟨hprime,hlo,hhi⟩ := (mem_prefix p).mp (List.mem_toFinset.mp hp)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hprime⟩
  have hnodup : fixedPrimes.Nodup := prefix_pairwise.nodup
  have he : ((bits : ℕ) : ℝ) = ∑ p ∈ fixedPrimes.toFinset, (Nat.log2 p : ℝ) := by
    rw [bits, ← List.sum_toFinset _ hnodup, Nat.cast_sum]
  have hlo : (69/100 : ℝ)*bits ≤ Chebyshev.theta 99999 := by
    rw [he, Finset.mul_sum, Chebyshev.theta_eq_sum_Icc]
    norm_num only [Nat.floor_ofNat]
    apply (Finset.sum_le_sum (s := fixedPrimes.toFinset) (fun p hp =>
      log_lower p ((mem_prefix p).mp (List.mem_toFinset.mp hp)).1)).trans
    apply Finset.sum_le_sum_of_subset_of_nonneg hP
    intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  rw [bits_certificate] at hlo
  norm_num at hlo
  linarith

lemma tail_cost_half (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 100000 ≤ p) :
    Erdos7No23Sieve.budgetCost S ≤ (1/2 : ℚ)/100000 := by
  have ht := Erdos7ChebyshevTail.tail_cost_potential S 100000 (by omega) hS
  norm_num only [Nat.cast_ofNat, Nat.reduceSub] at ht
  have hb := Erdos7ChebyshevTail.potential_antitone_theta
    (by norm_num : (0 : ℝ) < 100000) theta_lower
    (show Chebyshev.theta 99999 ≤ (7/5 : ℝ)*100000 from
      (Erdos7ChebyshevTail.theta_upper 99999 (by norm_num)).trans (by norm_num))
  have hn : Erdos7ChebyshevTail.potential (100000 : ℝ) 95000 ≤ (1/2 : ℝ)/100000 := by
    norm_num [Erdos7ChebyshevTail.potential]
  have h := ht.trans (hb.trans hn)
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

#print axioms theta_lower
#print axioms tail_cost_half
end Erdos7ThetaLower
