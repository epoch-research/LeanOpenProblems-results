import Submission.BuchstabGridTransfer
import Submission.BuchstabInitialNodes
import Submission.BuchstabGridBudgets

/-! Actual Buchstab main-term positivity from the finite rounded grid.
All small-prime tails and finite-sector errors are retained. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg Erdos970.BuchstabGrid
set_option maxHeartbeats 0

lemma primeKeep_exp (k : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    primeKeep nthPrime k (exp (s*log (nthPrime k : ℝ))) := by
  have hp : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  change (nthPrime k : ℝ)^2 ≤ exp (s*log (nthPrime k : ℝ))
  rw [← exp_log (pow_pos hp 2),log_pow]
  apply exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_right hs (log_natCast_nonneg _)

lemma referenceLower_ge_of_normalized_excess (n k : ℕ) (L l : ℝ)
    (hkeep : primeKeep nthPrime k (exp L))
    (h : eulerMass (nthPrime k).primesBelow*(∑ p ∈ (nthPrime k).primesBelow,
      primeUpperExcess n L p) ≤ 1-l) :
    prefixDensity primeMarginal k*l ≤ referenceLower n k (exp L) := by
  apply lowerStep_ge_of_excess _ _ _ _ _ _ hkeep
  rw [reference_excess_sum,nthPrime_prefix_density]
  have hE := eulerMass_pos (nthPrime k).primesBelow (fun p hp => (Nat.mem_primesBelow.mp hp).2)
  have hh : (∑ p ∈ (nthPrime k).primesBelow, primeUpperExcess n L p) ≤
      (1-l)/eulerMass (nthPrime k).primesBelow :=
    (le_div_iff₀ hE).mpr (by simpa only [mul_comm] using h)
  convert hh using 1
  ring

lemma referenceUpper_one_le_of_normalized_deficit (k : ℕ) (L u : ℝ)
    (h : eulerMass (nthPrime k).primesBelow*(∑ p ∈ (nthPrime k).primesBelow,
      primeLowerDeficit L p) ≤ u-1) :
    referenceUpper 1 k (exp L) ≤ prefixDensity primeMarginal k*u := by
  apply upperMain_le_of_deficit _ _ _ 0
  change (∑ i : Fin k, primeMarginal i.val*(prefixDensity primeMarginal i.val-
    referenceLower 0 i.val (exp L*primeMarginal i.val))) ≤ _
  rw [reference_deficit_sum,nthPrime_prefix_density]
  have hE := eulerMass_pos (nthPrime k).primesBelow (fun p hp => (Nat.mem_primesBelow.mp hp).2)
  have hh : (∑ p ∈ (nthPrime k).primesBelow, primeLowerDeficit L p) ≤
      (u-1)/eulerMass (nthPrime k).primesBelow :=
    (le_div_iff₀ hE).mpr (by simpa only [mul_comm] using h)
  convert hh using 1
  ring

lemma exists_upper_excess_tail (n : ℕ) : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    ∀ s : ℝ, 1 ≤ s → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ smallPrimePart k (s*log (nthPrime k : ℝ)), primeUpperExcess n (s*log (nthPrime k : ℝ)) p) ≤
        initialGridTail/s := by
  obtain ⟨N,hN⟩ := exists_reference_initial_tail
  refine ⟨N,fun k hk s hs => ?_⟩
  apply le_trans _ (hN k hk s hs)
  apply mul_le_mul_of_nonneg_left _ (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
  apply sum_le_sum
  intro p hp
  have hpp := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
  exact (primeUpperExcess_le_zero n _ p).trans_eq (primeUpperExcess_zero _ p hpp)

lemma exists_grid_upper_excess_bound (n a N : ℕ) (ha : 50 ≤ a) (ha' : a ≤ 650) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, N ≤ nthPrime k → ∀ j ∈ Ico (a-50) 600,
      referenceUpper n k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))) ≤ prefixDensity primeMarginal k*B j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ k : ℕ, M ≤ nthPrime k → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ (nthPrime k).primesBelow, primeUpperExcess n (((a : ℝ)/50)*log (nthPrime k : ℝ)) p) <
      (initialGridTail+(∑ j ∈ Ico (a-50) 600, (B j-1)/50))/((a : ℝ)/50)+ε := by
  have haR : (50 : ℝ) ≤ a := by exact_mod_cast ha
  have hs : (1 : ℝ) ≤ (a : ℝ)/50 := by linarith
  obtain ⟨N₀,hN₀⟩ := exists_upper_excess_tail n
  exact exists_grid_total_bound a ha ha' (primeUpperExcess n) (primeUpperExcess_nonneg n)
    initialGridTail (fun j => B j-1) ⟨N₀,fun k hk => hN₀ k hk _ hs⟩
    (eventually_upper_grid_bins n (a-50) 600 N le_rfl B hgrid _ (by linarith)) ε hε

lemma exists_grid_lower_deficit_bound (a N : ℕ) (ha : 50 ≤ a) (ha' : a ≤ 650) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, N ≤ nthPrime k → ∀ j ∈ Ico (a-50) 600,
      prefixDensity primeMarginal k*B j ≤ referenceLower 0 k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ k : ℕ, M ≤ nthPrime k → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ (nthPrime k).primesBelow, primeLowerDeficit (((a : ℝ)/50)*log (nthPrime k : ℝ)) p) <
      (lowerGridTail+(∑ j ∈ Ico (a-50) 600, (1-B j)/50))/((a : ℝ)/50)+ε := by
  have haR : (50 : ℝ) ≤ a := by exact_mod_cast ha
  have hs : (1 : ℝ) ≤ (a : ℝ)/50 := by linarith
  obtain ⟨N₀,hN₀⟩ := exists_reference_lower_deficit_tail
  exact exists_grid_total_bound a ha ha' primeLowerDeficit primeLowerDeficit_nonneg
    lowerGridTail (fun j => 1-B j) ⟨N₀,fun k hk => hN₀ k hk _ hs⟩
    (eventually_lower_grid_bins (a-50) 600 N le_rfl B hgrid _ (by linarith)) ε hε

lemma exists_referenceLower_zero_node (a : ℕ) (ha : a < 601) : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    prefixDensity primeMarginal k*((lowerNodes a : ℝ)/1000000) ≤
      referenceLower 0 k (exp (((a : ℝ)/50)*log (nthPrime k : ℝ))) := by
  rcases lower_grid_node_budget a ha with hz | ⟨ha108,hbudget⟩
  · refine ⟨0,fun k hk => ?_⟩
    simpa only [hz,Nat.cast_zero,zero_div,mul_zero] using referenceLower_nonneg 0 k _
  have haR : (108 : ℝ) ≤ a := by exact_mod_cast ha108
  have hs : (0 : ℝ) < (a : ℝ)/50 := by linarith
  obtain ⟨N,hN⟩ := exists_referenceUpper_zero_grid
  obtain ⟨M,hM⟩ := exists_grid_upper_excess_bound 0 a N (by omega) (by omega)
    (fun j => (baseNodes j : ℝ)/1000000) (by
      intro k hk j hj
      obtain ⟨hja,hj600⟩ := mem_Ico.mp hj
      exact hN k hk j (by omega) (by omega)) (1/200000) (by norm_num)
  refine ⟨M,fun k hk => ?_⟩
  apply referenceLower_ge_of_normalized_excess 0 k _ _ (primeKeep_exp k _ (by linarith))
  have hh := hM k hk
  have hi := initial_integral_budget (a-50) (by omega)
  have hd : (initialGridTail+(∑ j ∈ Ico (a-50) 600, ((baseNodes j : ℝ)/1000000-1)/50))/
      ((a : ℝ)/50) ≤ 1-(lowerNodes a : ℝ)/1000000-1/100000 :=
    (div_le_iff₀ hs).mpr (by nlinarith only [hi,hbudget])
  nlinarith only [hh,hd]

/-- A single prime threshold controls every actual first-lower grid node. -/
theorem exists_referenceLower_zero_grid : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    ∀ j : ℕ, j < 601 → prefixDensity primeMarginal k*((lowerNodes j : ℝ)/1000000) ≤
      referenceLower 0 k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))) := by
  classical
  choose N hN using (fun j : Fin 601 => exists_referenceLower_zero_node j.val j.isLt)
  refine ⟨univ.sup N,fun k hk j hj => hN ⟨j,hj⟩ k ?_⟩
  exact (le_sup (f := N) (mem_univ ⟨j,hj⟩)).trans hk

lemma exists_referenceUpper_one_node (a : ℕ) (ha0 : 55 ≤ a) (ha : a < 601) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
      referenceUpper 1 k (exp (((a : ℝ)/50)*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*((upperNodes a : ℝ)/1000000) := by
  rcases upper_grid_node_budget a ha (by omega) with hz | hbudget
  · obtain ⟨N,hN⟩ := exists_referenceUpper_zero_grid
    refine ⟨N,fun k hk => ?_⟩
    rw [hz]
    exact (referenceUpper_succ_le 0 k _).trans (hN k hk a ha0 ha)
  have haR : (55 : ℝ) ≤ a := by exact_mod_cast ha0
  have hs : (0 : ℝ) < (a : ℝ)/50 := by linarith
  obtain ⟨N,hN⟩ := exists_referenceLower_zero_grid
  obtain ⟨M,hM⟩ := exists_grid_lower_deficit_bound a N (by omega) (by omega)
    (fun j => (lowerNodes j : ℝ)/1000000) (by
      intro k hk j hj
      exact hN k hk j (by have := (mem_Ico.mp hj).2; omega)) (1/200000) (by norm_num)
  refine ⟨M,fun k hk => ?_⟩
  apply referenceUpper_one_le_of_normalized_deficit
  have hh := hM k hk
  have hi := deficit_integral_budget (a-50) (by omega)
  have hd : (lowerGridTail+(∑ j ∈ Ico (a-50) 600, (1-(lowerNodes j : ℝ)/1000000)/50))/
      ((a : ℝ)/50) ≤ (upperNodes a : ℝ)/1000000-1-1/100000 :=
    (div_le_iff₀ hs).mpr (by nlinarith only [hi,hbudget])
  nlinarith only [hh,hd]

/-- Every stored refined upper node bounds the actual upper main term. -/
theorem exists_referenceUpper_one_grid : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    ∀ j : ℕ, 55 ≤ j → j < 601 →
      referenceUpper 1 k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*((upperNodes j : ℝ)/1000000) := by
  classical
  have hnode : ∀ j : Fin 601, ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k → 55 ≤ j.val →
      referenceUpper 1 k (exp (((j.val : ℝ)/50)*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*((upperNodes j.val : ℝ)/1000000) := by
    intro j
    by_cases hj : 55 ≤ j.val
    · obtain ⟨N,hN⟩ := exists_referenceUpper_one_node j.val hj j.isLt
      exact ⟨N,fun k hk _ => hN k hk⟩
    · exact ⟨0,fun _ _ hh => (hj hh).elim⟩
  choose N hN using hnode
  refine ⟨univ.sup N,fun k hk j hj0 hj => hN ⟨j,hj⟩ k ?_ hj0⟩
  exact (le_sup (f := N) (mem_univ ⟨j,hj⟩)).trans hk

/-- Actual root lower main positivity at divisor exponent21/10.
This is not yet interval-survivor positivity: the complete error budget must
still be dominated by the interval mass. -/
theorem exists_referenceLower_one_positive : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    prefixDensity primeMarginal k/200 ≤
      referenceLower 1 k (exp ((21/10 : ℝ)*log (nthPrime k : ℝ))) := by
  obtain ⟨N,hN⟩ := exists_referenceUpper_one_grid
  obtain ⟨M,hM⟩ := exists_grid_upper_excess_bound 1 105 N (by omega) (by omega)
    (fun j => (upperNodes j : ℝ)/1000000) (by
      intro k hk j hj
      obtain ⟨hja,hj600⟩ := mem_Ico.mp hj
      exact hN k hk j (by omega) (by omega)) (1/1000) (by norm_num)
  refine ⟨M,fun k hk => ?_⟩
  have hh := hM k hk
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,show (105 : ℝ)/50 = 21/10 by norm_num] at hh
  have hbudget := refined_grid_budget_strong
  have hnorm : eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ (nthPrime k).primesBelow, primeUpperExcess 1 ((21/10 : ℝ)*log (nthPrime k : ℝ)) p) ≤
      1-(1/200 : ℝ) := by linarith only [hh,hbudget]
  have hresult := referenceLower_ge_of_normalized_excess 1 k _ (1/200)
    (primeKeep_exp k _ (by norm_num)) hnorm
  simpa only [mul_one_div] using hresult

#print axioms exists_referenceLower_zero_grid
#print axioms exists_referenceUpper_one_grid
#print axioms exists_referenceLower_one_positive
end Erdos970.RecursiveSieve.Buchstab
