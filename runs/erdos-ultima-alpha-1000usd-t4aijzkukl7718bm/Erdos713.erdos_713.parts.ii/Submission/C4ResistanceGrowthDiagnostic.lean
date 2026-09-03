import FormalConjecturesUtil
import Submission.C4CloneResistance
import Submission.RegularGrowthGap

/-! Actual regular C4-free hosts with irrational power growth and edge-scale
clone resistance, but a vanishing proportion of the C4 extremal number.
This is not a disproof of the original conjecture. -/
open SimpleGraph Filter Asymptotics Finset
open scoped Classical Topology
namespace Erdos713C4ResistanceGrowthDiagnostic
open Erdos713DegreePenalty Erdos713Cloning

/-- Clone resistance does not replace the extremal-asymptotic hypothesis.
The same regular family has irrational power growth, strong clone
resistance, and a vanishing extremal ratio. -/
theorem exists_irrational_resistant_family :
    ∃ α : ℝ, 1 < α ∧ α < 3/2 ∧ Irrational α ∧
      ∃ N d : ℕ → ℕ, Tendsto N atTop atTop ∧ Tendsto d atTop atTop ∧
        ∃ G : ∀ i, SimpleGraph (Fin (N i)),
          (∀ i, (cycleGraph 4).Free (G i) ∧ ∀ v, (G i).degree v = d i) ∧
          (fun i => (Nat.card (G i).edgeSet : ℝ)) ~[atTop]
            (fun i => (1/2 : ℝ)*(N i : ℝ)^α) ∧
          (fun i => (d i : ℝ)) ~[atTop] (fun i => (N i : ℝ)^(α-1)) ∧
          Tendsto (fun i => (Nat.card (G i).edgeSet : ℝ)/
            (extremalNumber (N i) (cycleGraph 4) : ℝ)) atTop (𝓝 0) ∧
          ∀ᶠ i : ℕ in atTop, ∀ J : Fin (N i) → SimpleGraph (Option (Fin (N i))),
            (∀ v, J v ≤ clone (G i) v) → (∀ v, (cycleGraph 4).Free (J v)) →
            edgesR (G i) ≤ ∑ v, (edgesR (clone (G i) v)-edgesR (J v)) := by
  obtain ⟨α,hα,hαhi,hirr,N,d,hN,hd,G,hG,hE,hdeg,hgap⟩ :=
    Erdos713RegularGrowthGap.exists_irrational_regular_family_with_gap
  refine ⟨α,hα,hαhi,hirr,N,d,hN,hd,G,hG,hE,hdeg,hgap,?_⟩
  filter_upwards [hd.eventually_ge_atTop 2] with i hi
  intro J hJ hf
  apply Erdos713C4CloneResistance.edge_scale_cost (G i) ?_ J hJ hf
  intro v
  unfold degreeR
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,(hG i).2]
  exact_mod_cast hi

#print axioms exists_irrational_resistant_family
end Erdos713C4ResistanceGrowthDiagnostic
