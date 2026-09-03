import Submission.BuchstabGridCertificate
import Submission.BuchstabTailAlgebra

/-! Real budget consequences of the kernel-checked local recurrences.
The terminal allowances match the actual source and deficit tail constants. -/
namespace Erdos970.BuchstabGrid
open Finset Erdos970.FiniteSelberg
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma initial_integral_budget (a : ℕ) (ha : a ≤ 600) :
    initialGridTail+(∑ j ∈ Ico a 600, ((baseNodes j : ℝ)/1000000-1)/50) ≤
      (initialIntegral a : ℝ)/1000000 := by
  have hs := sum_Ico_le_telescope a 600 ha
    (fun j => ((baseNodes j : ℝ)/1000000-1)/50)
    (fun j => (initialIntegral j : ℝ)/1000000) (by
      intro j hj
      have hh := initial_integral_step ⟨j,(mem_Ico.mp hj).2⟩
      change 50*initialIntegral (j+1)+baseNodes j ≤ 50*initialIntegral j+1000000 at hh
      have hhR : (50 : ℝ)*initialIntegral (j+1)+baseNodes j ≤ 50*initialIntegral j+1000000 := by exact_mod_cast hh
      linarith)
  have ht : initialGridTail ≤ (initialIntegral 600 : ℝ)/1000000 := by
    norm_num [initialGridTail,initialIntegral]
  dsimp only at hs
  linarith

lemma deficit_integral_budget (a : ℕ) (ha : a ≤ 600) :
    lowerGridTail+(∑ j ∈ Ico a 600, (1-(lowerNodes j : ℝ)/1000000)/50) ≤
      (lowerDeficitIntegral a : ℝ)/1000000 := by
  have hs := sum_Ico_le_telescope a 600 ha
    (fun j => (1-(lowerNodes j : ℝ)/1000000)/50)
    (fun j => (lowerDeficitIntegral j : ℝ)/1000000) (by
      intro j hj
      have hh := deficit_integral_step ⟨j,(mem_Ico.mp hj).2⟩
      change 50*lowerDeficitIntegral (j+1)+1000000 ≤ 50*lowerDeficitIntegral j+lowerNodes j at hh
      have hhR : (50 : ℝ)*lowerDeficitIntegral (j+1)+1000000 ≤
          50*lowerDeficitIntegral j+lowerNodes j := by exact_mod_cast hh
      linarith)
  have ht : lowerGridTail ≤ (lowerDeficitIntegral 600 : ℝ)/1000000 := by
    norm_num [lowerGridTail,lowerDeficitIntegral]
  dsimp only at hs
  linarith

lemma refined_integral_budget (a : ℕ) (ha : a ≤ 600) :
    initialGridTail+(∑ j ∈ Ico a 600, ((upperNodes j : ℝ)/1000000-1)/50) ≤
      (refinedIntegral a : ℝ)/1000000 := by
  have hs := sum_Ico_le_telescope a 600 ha
    (fun j => ((upperNodes j : ℝ)/1000000-1)/50)
    (fun j => (refinedIntegral j : ℝ)/1000000) (by
      intro j hj
      have hh := refined_integral_step ⟨j,(mem_Ico.mp hj).2⟩
      change 50*refinedIntegral (j+1)+upperNodes j ≤ 50*refinedIntegral j+1000000 at hh
      have hhR : (50 : ℝ)*refinedIntegral (j+1)+upperNodes j ≤ 50*refinedIntegral j+1000000 := by exact_mod_cast hh
      linarith)
  have ht : initialGridTail ≤ (refinedIntegral 600 : ℝ)/1000000 := by
    norm_num [initialGridTail,refinedIntegral]
  dsimp only at hs
  linarith

lemma lower_grid_node_budget (a : ℕ) (ha : a < 601) : lowerNodes a = 0 ∨
    (108 ≤ a ∧ (initialIntegral (a-50) : ℝ)/1000000 ≤
      ((a : ℝ)/50)*(1-(lowerNodes a : ℝ)/1000000-1/100000)) := by
  rcases lower_node_step ⟨a,ha⟩ with hz | ⟨ha',hc⟩
  · exact Or.inl hz
  · refine Or.inr ⟨ha',?_⟩
    change 50*initialIntegral (a-50)+(lowerNodes a+10)*a ≤ 1000000*a at hc
    have hcR : (50 : ℝ)*initialIntegral (a-50)+((lowerNodes a : ℝ)+10)*a ≤ 1000000*a := by exact_mod_cast hc
    nlinarith only [hcR]

lemma upper_grid_node_budget (a : ℕ) (ha : a < 601) (ha50 : 50 ≤ a) :
    upperNodes a = baseNodes a ∨ (lowerDeficitIntegral (a-50) : ℝ)/1000000 ≤
      ((a : ℝ)/50)*((upperNodes a : ℝ)/1000000-1-1/100000) := by
  rcases upper_node_step ⟨a,ha⟩ ha50 with hz | hc
  · exact Or.inl hz
  · apply Or.inr
    change 50*lowerDeficitIntegral (a-50)+(1000000+10)*a ≤ upperNodes a*a at hc
    have hcR : (50 : ℝ)*lowerDeficitIntegral (a-50)+(1000000+10)*a ≤ (upperNodes a : ℝ)*a := by exact_mod_cast hc
    nlinarith only [hcR]

/-- The stronger rounded margin leaves an additional 1/1000 for finite-sector
errors, while still retaining a root lower value of1/200. -/
theorem refined_grid_budget_strong :
    initialGridTail+(∑ j ∈ Ico 55 600, ((upperNodes j : ℝ)/1000000-1)/50) < (1043/500 : ℝ) := by
  have hs := refined_integral_budget 55 (by omega)
  have ht : (refinedIntegral 55 : ℝ)/1000000 < (1043/500 : ℝ) := by
    norm_num [refinedIntegral]
  exact hs.trans_lt ht

#print axioms initial_integral_budget
#print axioms deficit_integral_budget
#print axioms lower_grid_node_budget
#print axioms upper_grid_node_budget
#print axioms refined_grid_budget_strong
end Erdos970.BuchstabGrid
