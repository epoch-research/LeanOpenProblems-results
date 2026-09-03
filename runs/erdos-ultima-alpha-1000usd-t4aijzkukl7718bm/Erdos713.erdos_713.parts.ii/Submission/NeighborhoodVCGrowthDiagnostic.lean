import FormalConjecturesUtil
import Submission.NeighborhoodVC
import Submission.RegularGrowthGap

/-! Bounded neighborhood VC dimension and regularity do not by themselves
force rational edge-growth indices. The graphs here are not extremal. -/
open SimpleGraph Filter Asymptotics
open scoped Classical Topology
namespace Erdos713NeighborhoodVCGrowthDiagnostic
open Erdos713NeighborhoodVC
set_option maxHeartbeats 1000000

/-- Every real index in (1,3/2) occurs with VC dimension at most two,
regularity, and exact power asymptotics. The extremal ratio tends to zero. -/
theorem exists_regular_low_vc_family {α : ℝ} (hα : 1 < α) (hαhi : α < 3/2) :
    ∃ N d : ℕ → ℕ, Tendsto N atTop atTop ∧ Tendsto d atTop atTop ∧
      ∃ G : ∀ i, SimpleGraph (Fin (N i)),
        (∀ i, (cycleGraph 4).Free (G i) ∧ (family (G i)).vcDim ≤ 2 ∧
          ∀ v, (G i).degree v = d i) ∧
        (fun i => (Nat.card (G i).edgeSet : ℝ)) ~[atTop]
          (fun i => (1/2 : ℝ)*(N i : ℝ)^α) ∧
        (fun i => (d i : ℝ)) ~[atTop] (fun i => (N i : ℝ)^(α-1)) ∧
        Tendsto (fun i => (Nat.card (G i).edgeSet : ℝ) /
          (extremalNumber (N i) (cycleGraph 4) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨N,d,hN,hd,G,hG,hE,hdeg⟩ :=
    Erdos713RegularPowerGrowth.exists_regular_power_family hα hαhi
  refine ⟨N,d,hN,hd,G,?_,hE,hdeg,?_⟩
  · intro i
    refine ⟨(hG i).1,?_,(hG i).2⟩
    convert vcDim_le_two_of_c4_free (G i) (hG i).1 using 1
    congr 1
  · exact Erdos713RegularGrowthGap.ratio_extremal_tendsto_zero hN hαhi (by norm_num) hE

/-- This is the negation of an auxiliary proposed criterion, not of the
original statement involving extremalNumber. -/
theorem no_rationality_from_regular_low_vc_growth :
    ¬ ∀ (α : ℝ) (N d : ℕ → ℕ) (G : ∀ i, SimpleGraph (Fin (N i))),
      1 < α → α < 3/2 → Tendsto N atTop atTop → Tendsto d atTop atTop →
      (∀ i, (cycleGraph 4).Free (G i) ∧ (family (G i)).vcDim ≤ 2 ∧
        ∀ v, (G i).degree v = d i) →
      (fun i => (Nat.card (G i).edgeSet : ℝ)) ~[atTop]
        (fun i => (1/2 : ℝ)*(N i : ℝ)^α) → α ∈ Set.range ((↑) : ℚ → ℝ) := by
  intro h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hlow : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hhigh : Real.sqrt 2 < (3 : ℝ)/2 := by nlinarith
  obtain ⟨N,d,hN,hd,G,hG,hE,_hdeg,_hgap⟩ := exists_regular_low_vc_family hlow hhigh
  exact irrational_sqrt_two (h _ N d G hlow hhigh hN hd hG hE)

#print axioms exists_regular_low_vc_family
#print axioms no_rationality_from_regular_low_vc_growth
end Erdos713NeighborhoodVCGrowthDiagnostic
