import Submission.BuchstabFourGridChecks
import Submission.BuchstabGridBudgets

/-! Real consequences of the exact four-refinement table checks. -/
namespace Erdos970.BuchstabFourGrid
open Finset Real Erdos970.FiniteSelberg Erdos970.BuchstabGrid
set_option maxHeartbeats 0

lemma upper_integral_budget (r a : ℕ) (hr : r < 4) (ha : a ≤ 600) :
    initialGridTail+(∑ j ∈ Ico a 600, ((upperTable r j : ℝ)/1000000-1)/50) ≤
      (upperIntegral r a : ℝ)/1000000 := by
  have hs := sum_Ico_le_telescope a 600 ha
    (fun j => ((upperTable r j : ℝ)/1000000-1)/50)
    (fun j => (upperIntegral r j : ℝ)/1000000) (by
      intro j hj
      have hh := (all_checks ⟨r,hr⟩ ⟨j,by have := (mem_Ico.mp hj).2; omega⟩).1 (mem_Ico.mp hj).2
      change 50*upperIntegral r (j+1)+upperTable r j ≤ 50*upperIntegral r j+1000000 at hh
      have hhR : (50 : ℝ)*upperIntegral r (j+1)+upperTable r j ≤ 50*upperIntegral r j+1000000 := by exact_mod_cast hh
      linarith)
  have ht : initialGridTail ≤ (upperIntegral r 600 : ℝ)/1000000 := by
    rw [terminal_checks.1 ⟨r,hr⟩]
    norm_num [initialGridTail]
  dsimp only at hs
  linarith

lemma lower_integral_budget (r a : ℕ) (hr : r < 3) (ha : a ≤ 600) :
    lowerGridTail+(∑ j ∈ Ico a 600, (1-(lowerTable r j : ℝ)/1000000)/50) ≤
      (lowerIntegral r a : ℝ)/1000000 := by
  have hs := sum_Ico_le_telescope a 600 ha
    (fun j => (1-(lowerTable r j : ℝ)/1000000)/50)
    (fun j => (lowerIntegral r j : ℝ)/1000000) (by
      intro j hj
      have hh := ((all_checks ⟨r,by omega⟩ ⟨j,by have := (mem_Ico.mp hj).2; omega⟩).2 hr).2.1 (mem_Ico.mp hj).2
      change 50*lowerIntegral r (j+1)+1000000 ≤ 50*lowerIntegral r j+lowerTable r j at hh
      have hhR : (50 : ℝ)*lowerIntegral r (j+1)+1000000 ≤ 50*lowerIntegral r j+lowerTable r j := by exact_mod_cast hh
      linarith)
  have ht : lowerGridTail ≤ (lowerIntegral r 600 : ℝ)/1000000 := by
    rw [terminal_checks.2.1 ⟨r,hr⟩]
    norm_num [lowerGridTail]
  dsimp only at hs
  linarith

lemma lower_node_budget (r a : ℕ) (hr : r < 3) (ha : a < 601) :
    (lowerTable r a : ℝ)/1000000 = 0 ∨ (100 ≤ a ∧
      initialGridTail+(∑ j ∈ Ico (a-50) 600, ((upperTable r j : ℝ)/1000000-1)/50) ≤
        ((a : ℝ)/50)*(1-(lowerTable r a : ℝ)/1000000-1/100000)) := by
  rcases ((all_checks ⟨r,by omega⟩ ⟨a,ha⟩).2 hr).1 with hz | ⟨ha100,hbudget⟩
  · exact Or.inl (by simp only [hz,Nat.cast_zero,zero_div])
  · refine Or.inr ⟨ha100,?_⟩
    have hi := upper_integral_budget r (a-50) (by omega) (by omega)
    change 50*upperIntegral r (a-50)+(lowerTable r a+10)*a ≤ 1000000*a at hbudget
    have hcR : (50 : ℝ)*upperIntegral r (a-50)+((lowerTable r a : ℝ)+10)*a ≤ 1000000*a := by exact_mod_cast hbudget
    nlinarith only [hi,hcR]

lemma upper_node_budget (r a : ℕ) (hr : r < 3) (ha0 : 50 ≤ a) (ha : a < 601) :
    (upperTable (r+1) a : ℝ)/1000000 = (upperTable r a : ℝ)/1000000 ∨
      lowerGridTail+(∑ j ∈ Ico (a-50) 600, (1-(lowerTable r j : ℝ)/1000000)/50) ≤
        ((a : ℝ)/50)*((upperTable (r+1) a : ℝ)/1000000-1-1/100000) := by
  rcases ((all_checks ⟨r,by omega⟩ ⟨a,ha⟩).2 hr).2.2 ha0 with hz | hbudget
  · exact Or.inl (by rw [hz])
  · apply Or.inr
    have hi := lower_integral_budget r (a-50) hr (by omega)
    change 50*lowerIntegral r (a-50)+(1000000+10)*a ≤ upperTable (r+1) a*a at hbudget
    have hcR : (50 : ℝ)*lowerIntegral r (a-50)+(1000000+10)*a ≤ (upperTable (r+1) a : ℝ)*a := by exact_mod_cast hbudget
    nlinarith only [hi,hcR]

lemma root_budget :
    initialGridTail+(∑ j ∈ Ico 52 600, ((upperTable 3 j : ℝ)/1000000-1)/50) < (10149/5000 : ℝ) := by
  have hi := upper_integral_budget 3 52 (by omega) (by omega)
  have ht : (upperIntegral 3 52 : ℝ) < 2029800 := by exact_mod_cast terminal_checks.2.2
  linarith only [hi,ht]

#print axioms root_budget
end Erdos970.BuchstabFourGrid
