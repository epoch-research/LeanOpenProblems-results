import Submission.BuchstabGridBaseBounds
import Submission.BuchstabGridLocalChecks

/-! Kernel-checked local inequalities for rounded integer profile tables.
This is a finite arithmetic certificate, not an assertion that the tables
already bound an arithmetic sieve. The latter needs prime-sector transfer. -/
namespace Erdos970.BuchstabGrid
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma node_bounds : ∀ j : Fin 601,
    scale ≤ (baseNodes (j.val)) ∧ (lowerNodes (j.val)) ≤ scale ∧
      scale ≤ (upperNodes (j.val)) ∧ (upperNodes (j.val)) ≤ (baseNodes (j.val)) :=
  fun j => (all_local_checks j).1

lemma initial_integral_step : ∀ j : Fin 600,
    mesh*(initialIntegral (j.val+1))+(baseNodes (j.val)) ≤
      mesh*(initialIntegral (j.val))+scale :=
  fun j => (all_local_checks ⟨j.val,by omega⟩).2.1 j.isLt

/-- Every positive lower node has an explicit ten-unit rounding slack. -/
lemma lower_node_step : ∀ j : Fin 601, (lowerNodes (j.val)) = 0 ∨
    (108 ≤ j.val ∧ mesh*(initialIntegral (j.val-mesh))+
      ((lowerNodes (j.val))+10)*j.val ≤ scale*j.val) :=
  fun j => (all_local_checks j).2.2.1

lemma deficit_integral_step : ∀ j : Fin 600,
    mesh*(lowerDeficitIntegral (j.val+1))+scale ≤
      mesh*(lowerDeficitIntegral (j.val))+(lowerNodes (j.val)) :=
  fun j => (all_local_checks ⟨j.val,by omega⟩).2.2.2.1 j.isLt

/-- Each upper node is certified either by its old source or by the new lower
step. The second alternative retains a ten-unit upper rounding slack. -/
lemma upper_node_step : ∀ j : Fin 601, mesh ≤ j.val →
    (upperNodes (j.val)) = (baseNodes (j.val)) ∨
      mesh*(lowerDeficitIntegral (j.val-mesh))+(scale+10)*j.val ≤ (upperNodes (j.val))*j.val :=
  fun j => (all_local_checks j).2.2.2.2.1

lemma refined_integral_step : ∀ j : Fin 600,
    mesh*(refinedIntegral (j.val+1))+(upperNodes (j.val)) ≤
      mesh*(refinedIntegral (j.val))+scale :=
  fun j => (all_local_checks ⟨j.val,by omega⟩).2.2.2.2.2 j.isLt

lemma terminal_bounds :
    (scale : ℚ)*(3/50)*8^8/(7*12^7) ≤ (initialIntegral (600)) ∧
    (scale : ℚ)*(3/2)*(8*(3/50)/63)*9^8/(7*12^7) ≤ (lowerDeficitIntegral (600)) ∧
    (refinedIntegral (600)) = (initialIntegral (600)) ∧
    (refinedIntegral (55)) < 2089500 := by decide +kernel

lemma sum_Ico_le_telescope (a b : ℕ) (hab : a ≤ b) (w F : ℕ → ℝ)
    (h : ∀ j ∈ Ico a b, w j ≤ F j-F (j+1)) :
    (∑ j ∈ Ico a b, w j) ≤ F a-F b := by
  have hh := sum_le_sum h
  have he := sum_Ico_sub (fun j => -F j) hab
  simp only [neg_sub_neg] at he
  rw [he] at hh
  linarith only [hh]

/-- The rounded refined table has strict positive margin at s=21/10,
large enough to retain the normalized lower value 1/200. -/
theorem refined_grid_budget :
    ((initialIntegral (600)) : ℝ)/1000000+
      (∑ j ∈ Ico 55 600, (((upperNodes (j)) : ℝ)/1000000-1)/50) < (4179/2000 : ℝ) := by
  have hs := sum_Ico_le_telescope 55 600 (by omega)
    (fun j => (((upperNodes (j)) : ℝ)/1000000-1)/50)
    (fun j => ((refinedIntegral (j)) : ℝ)/1000000) (by
      intro j hj
      have hjlt : j < 600 := (mem_Ico.mp hj).2
      have hh := refined_integral_step ⟨j,hjlt⟩
      change 50*(refinedIntegral (j+1))+(upperNodes (j)) ≤ 50*(refinedIntegral (j))+1000000 at hh
      have hhR : (50 : ℝ)*(refinedIntegral (j+1))+(upperNodes (j)) ≤
          50*(refinedIntegral (j))+1000000 := by exact_mod_cast hh
      linarith)
  have ht : ((refinedIntegral (600)) : ℝ) = (initialIntegral (600)) := by
    exact_mod_cast terminal_bounds.2.2.1
  have hb : ((refinedIntegral (55)) : ℝ) < 2089500 := by
    exact_mod_cast terminal_bounds.2.2.2
  dsimp only at hs
  rw [ht] at hs
  linarith

#print axioms base_formula_bound
#print axioms lower_node_step
#print axioms upper_node_step
#print axioms refined_grid_budget
end Erdos970.BuchstabGrid
