import FormalConjecturesUtil
import Submission.PrimeEnergy

/-! Exact conservation between larger-prime and smaller-prime signed groups.
Their energies differ by at most a linear boundary term. This is not a bound
on either energy separately, and does not prove the density conjecture. -/

namespace Erdos371LoserGroupConservation

open Finset Erdos371PrimeDiscrepancy Erdos371PrimeEnergy

def loser (n : ℕ) : ℕ := min (P n) (P (n+1))

def loserGroup (p N : ℕ) : ℤ :=
  ∑ n ∈ range N, if loser n = p then sign n else 0

def indicator (p n : ℕ) : ℤ := if P n = p then 1 else 0

lemma local_conservation (p n : ℕ) :
    (if winner n = p then sign n else 0) -
      (if loser n = p then sign n else 0) = indicator p (n+1) - indicator p n := by
  have hn := consecutive_ne n
  unfold winner loser sign indicator
  simp only [max_def, min_def]
  split_ifs <;> omega

/-- Conservation at a fixed height, with both interval endpoints retained. -/
lemma group_eq_loserGroup_add_boundary (p N : ℕ) :
    group p N = loserGroup p N + indicator p N - indicator p 0 := by
  have h : group p N - loserGroup p N = indicator p N - indicator p 0 := by
    simp only [group, loserGroup, ← sum_sub_distrib, local_conservation, sum_range_sub]
  omega

/-- For a prime, the initial endpoint contributes nothing. -/
theorem prime_group_conservation {p : ℕ} (hp : p.Prime) (N : ℕ) :
    group p N = loserGroup p N + if P N = p then 1 else 0 := by
  rw [group_eq_loserGroup_add_boundary]
  simp [indicator, P, hp.ne_zero.symm]

lemma loserGroup_abs_le (p N : ℕ) : |loserGroup p N| ≤ N := by
  calc
    _ ≤ ∑ n ∈ range N, |if loser n = p then sign n else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ range N, (1 : ℤ) := by
      apply sum_le_sum
      intro n hn
      unfold sign
      split_ifs <;> norm_num
    _ = _ := by simp

noncomputable def loserEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, (loserGroup p N : ℝ)^2

lemma endpoint_mem_iff (N : ℕ) : P N ∈ (N+1).primesBelow ↔ 1 < N := by
  constructor
  · intro h
    have hp := Nat.prime_of_mem_primesBelow h
    by_contra hn
    have he : N=0 ∨ N=1 := by omega
    rcases he with rfl | rfl <;> norm_num [P] at hp
  · intro hn
    exact Nat.mem_primesBelow.mpr
      ⟨Nat.lt_succ_of_le Nat.maxPrimeFac_le, Nat.prime_maxPrimeFac_of_one_lt N hn⟩

/-- The energy change is exactly one endpoint contribution. -/
theorem energy_eq_loserEnergy (N : ℕ) :
    energy N = loserEnergy N +
      if 1 < N then 2*(loserGroup (P N) N : ℝ)+1 else 0 := by
  have he (p : ℕ) (hp : p ∈ (N+1).primesBelow) :
      (group p N : ℝ)^2 = (loserGroup p N : ℝ)^2 +
        if P N = p then 2*(loserGroup p N : ℝ)+1 else 0 := by
    rw [prime_group_conservation (Nat.prime_of_mem_primesBelow hp)]
    by_cases h : P N = p <;> simp only [h, if_true, if_false, Int.cast_add, Int.cast_one,
      Int.cast_zero] <;> ring
  unfold energy
  rw [sum_congr rfl he, sum_add_distrib]
  simp only [sum_ite_eq, endpoint_mem_iff, loserEnergy]

/-- In particular, changing to smaller-prime groups cannot by itself establish
near-linear energy: the two energies already differ by at most `2*N+1`. -/
theorem energy_difference_bound (N : ℕ) :
    |energy N - loserEnergy N| ≤ 2*(N:ℝ)+1 := by
  rw [energy_eq_loserEnergy, add_sub_cancel_left]
  split_ifs with hN
  · have hg : |(loserGroup (P N) N : ℝ)| ≤ N := by
      exact_mod_cast loserGroup_abs_le (P N) N
    calc
      _ ≤ |2*(loserGroup (P N) N : ℝ)|+|1| := abs_add_le _ _
      _ = 2*|(loserGroup (P N) N : ℝ)|+1 := by norm_num [abs_mul]
      _ ≤ _ := by linarith
  · simpa only [abs_zero] using (show (0 : ℝ) ≤ 2*(N:ℝ)+1 by positivity)

end Erdos371LoserGroupConservation

#print axioms Erdos371LoserGroupConservation.prime_group_conservation
#print axioms Erdos371LoserGroupConservation.energy_eq_loserEnergy
#print axioms Erdos371LoserGroupConservation.energy_difference_bound
