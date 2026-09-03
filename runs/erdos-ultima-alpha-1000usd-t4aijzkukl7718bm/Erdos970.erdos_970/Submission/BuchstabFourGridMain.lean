import Submission.BuchstabIteratedGrid
import Submission.BuchstabFourGridBudgets

/-! Actual prime-grid positivity at divisor exponent51/25. All profiles are
transferred uniformly, rather than identifying model tables with sieve mains. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg BuchstabGrid BuchstabFourGrid
set_option maxHeartbeats 0

lemma four_grid_seed_valid : UpperGridValid 1 (fun j => (upperTable 0 j : ℝ)/1000000) := by
  obtain ⟨N,hN⟩ := exists_referenceUpper_one_grid
  obtain ⟨N',hN'⟩ := exists_referenceLower_zero_grid
  have hnode (a : Fin 601) : ∃ M : ℕ, ∀ k : ℕ, M ≤ nthPrime k → 50 ≤ a.val →
      referenceUpper 1 k (exp (((a.val : ℝ)/50)*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*((upperTable 0 a.val : ℝ)/1000000) := by
    by_cases ha : 50 ≤ a.val
    · rcases seed_checks a ha with ⟨ha55,hEq⟩ | ⟨ha55,hbudget⟩
      · refine ⟨N,fun k hk _ => ?_⟩
        rw [hEq]
        exact hN k hk a.val ha55 a.isLt
      · have haR : (50 : ℝ) ≤ a.val := by exact_mod_cast ha
        have hs : (0 : ℝ) < (a.val : ℝ)/50 := by linarith
        obtain ⟨M,hM⟩ := exists_grid_lower_deficit_bound a.val N' (by omega) (by omega)
          (fun j => (lowerNodes j : ℝ)/1000000) (by
            intro k hk j hj
            exact hN' k hk j (by have := (mem_Ico.mp hj).2; omega)) (1/200000) (by norm_num)
        refine ⟨M,fun k hk _ => ?_⟩
        apply referenceUpper_one_le_of_normalized_deficit
        have hh := hM k hk
        have hi := deficit_integral_budget (a.val-50) (by omega)
        change 50*lowerDeficitIntegral (a.val-50)+(1000000+10)*a.val ≤ upperTable 0 a.val*a.val at hbudget
        have hcR : (50 : ℝ)*lowerDeficitIntegral (a.val-50)+(1000000+10)*a.val ≤
            (upperTable 0 a.val : ℝ)*a.val := by exact_mod_cast hbudget
        have hd : (lowerGridTail+(∑ j ∈ Ico (a.val-50) 600, (1-(lowerNodes j : ℝ)/1000000)/50))/
            ((a.val : ℝ)/50) ≤ (upperTable 0 a.val : ℝ)/1000000-1-1/100000 :=
          (div_le_iff₀ hs).mpr (by nlinarith only [hi,hcR])
        linarith only [hh,hd]
    · exact ⟨0,fun k hk hh => (ha hh).elim⟩
  classical
  choose M hM using hnode
  refine ⟨univ.sup M,fun k hk j hj0 hj => hM ⟨j,hj⟩ k ?_ hj0⟩
  exact (le_sup (f := M) (mem_univ ⟨j,hj⟩)).trans hk

lemma four_grid_round_valid (r : ℕ) (hr : r < 4) :
    UpperGridValid (r+1) (fun j => (upperTable r j : ℝ)/1000000) := by
  induction r with
  | zero => exact four_grid_seed_valid
  | succ r ih =>
    have hr3 : r < 3 := by omega
    have hu := ih (by omega)
    have hl := lower_grid_from_upper (r+1) _ _ hu
      (fun a ha => lower_node_budget r a hr3 ha)
    exact upper_grid_from_lower (r+1) _ _ _ hu hl
      (fun a ha0 ha => upper_node_budget r a hr3 ha0 ha)

/-- Four actual upper refinements give a positive normalized lower main at
exponent51/25. Interval positivity still requires its complete incurred error. -/
theorem exists_referenceLower_four_positive : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    prefixDensity primeMarginal k/250 ≤
      referenceLower 4 k (exp ((51/25 : ℝ)*log (nthPrime k : ℝ))) := by
  obtain ⟨N,hN⟩ := four_grid_round_valid 3 (by omega)
  obtain ⟨M,hM⟩ := exists_grid_upper_excess_bound 4 102 N (by omega) (by omega)
    (fun j => (upperTable 3 j : ℝ)/1000000) (by
      intro k hk j hj
      obtain ⟨hja,hj600⟩ := mem_Ico.mp hj
      exact hN k hk j (by omega) (by omega)) (1/1000) (by norm_num)
  refine ⟨M,fun k hk => ?_⟩
  have hh := hM k hk
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,show (102 : ℝ)/50 = 51/25 by norm_num] at hh
  have hbudget := root_budget
  have hnorm : eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ (nthPrime k).primesBelow, primeUpperExcess 4 ((51/25 : ℝ)*log (nthPrime k : ℝ)) p) ≤
      1-(1/250 : ℝ) := by linarith only [hh,hbudget]
  have hresult := referenceLower_ge_of_normalized_excess 4 k _ (1/250)
    (primeKeep_exp k _ (by norm_num)) hnorm
  simpa only [mul_one_div] using hresult

#print axioms four_grid_seed_valid
#print axioms four_grid_round_valid
#print axioms exists_referenceLower_four_positive
end Erdos970.RecursiveSieve.Buchstab
