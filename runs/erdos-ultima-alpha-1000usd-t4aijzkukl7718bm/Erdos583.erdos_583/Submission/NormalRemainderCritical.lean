import Submission.NormalTerminalBudget
import Submission.CycleEdgeAbsorption
import Submission.TailEdgeAbsorption
import Submission.RootEndpointTailCapacity

/-! Necessary path-budget and endpoint obstructions in the ordinary remainder
of the same optimized minimal-failure certificate. These do not assert that
such a certificate is impossible. -/
namespace Erdos583NormalRemainderCriticalDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.GroupActivation Erdos583Work.MarkedCycleGroups
open Erdos583UnifiedMinimalDefectDevelopment
open Erdos583CycleEdgeAbsorptionDevelopment Erdos583TailEdgeAbsorptionDevelopment
open Erdos583RootEndpointTailCapacityDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

abbrev normalIndices := Finset.univ.erase D.rep.index
abbrev remainder := selectedGraph D.family (normalIndices F D)
abbrev normalBudget := (normalIndices F D).card

lemma normalBudget_eq : normalBudget F D=budget F.order-1 := by
  simp only [normalBudget,normalIndices,Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,Fintype.card_fin]

lemma normal_partition_exact :
    ∃ E : Finset (remainder F D).Subgraph, GoodDecomposition (remainder F D) E ∧
      E.card=normalBudget F D ∧ ∀ H ∈ E, H.edgeSet.Nonempty := by
  exact normal_group_exact F.failure D.family D.score D.rep.index D.rep.member_not_path
    (normalIndices F D) (by simp [normalIndices])

lemma normal_partition_lower_bound (E : Finset (remainder F D).Subgraph)
    (hE : GoodDecomposition (remainder F D) E) : normalBudget F D ≤ E.card := by
  exact normal_group_cannot_save F.failure D.family D.score D.rep.index D.rep.member_not_path
    (normalIndices F D) (by simp [normalIndices]) E hE

lemma root_cycle_edge_critical {x : Fin F.order} (hx : D.rep.cycle.toSubgraph.Adj D.root x) :
    ¬∃ E : Finset (remainder F D ⊔ edge D.root x).Subgraph,
      GoodDecomposition (remainder F D ⊔ edge D.root x) E ∧ E.card ≤ normalBudget F D := by
  rintro ⟨E,hE,hEc⟩
  exact F.failure (absorb_root_cycle_edge D.family D.score D.root D.rep
    (normalIndices F D) (by simp [normalIndices]) hx E hE hEc)

lemma last_tail_edge_critical :
    ¬∃ E : Finset (remainder F D ⊔ edge D.rep.finish D.rep.tail.penultimate).Subgraph,
      GoodDecomposition (remainder F D ⊔ edge D.rep.finish D.rep.tail.penultimate) E ∧
      E.card ≤ normalBudget F D := by
  rintro ⟨E,hE,hEc⟩
  obtain ⟨U,M,hUs,hMC,hl⟩ := absorb_last_tail_edge D.family D.score D.root D.rep
    (tail_not_nil F D) (normalIndices F D) (by simp [normalIndices]) E hE hEc
  have hh := D.tail_minimum U M hUs hMC
  omega

lemma root_cycle_edge_missing {x : Fin F.order} (hx : D.rep.cycle.toSubgraph.Adj D.root x) :
    ¬(remainder F D).Adj D.root x := by
  intro h
  obtain ⟨E,hE,hEc,_⟩ := normal_partition_exact F D
  have he : remainder F D ⊔ edge D.root x=remainder F D :=
    sup_eq_left.mpr ((edge_le_iff _).mpr (Or.inr h))
  apply root_cycle_edge_critical F D hx
  rw [he]
  exact ⟨E,hE,hEc.le⟩

lemma last_tail_edge_missing : ¬(remainder F D).Adj D.rep.finish D.rep.tail.penultimate := by
  intro h
  obtain ⟨E,hE,hEc,_⟩ := normal_partition_exact F D
  have he : remainder F D ⊔ edge D.rep.finish D.rep.tail.penultimate=remainder F D :=
    sup_eq_left.mpr ((edge_le_iff _).mpr (Or.inr h))
  apply last_tail_edge_critical F D
  rw [he]
  exact ⟨E,hE,hEc.le⟩

lemma odd_normalBudget (ho : Odd F.order) : F.order=2*normalBudget F D+1 := by
  rw [normalBudget_eq]
  have hp := D.rep.index.isLt
  obtain ⟨q,hq⟩ := ho
  simp only [budget,BridgeGlue.ceil_half,Fintype.card_fin] at *
  omega

lemma odd_remainder_connected (ho : Odd F.order) : (remainder F D).Connected :=
  Erdos583NormalTerminalBudgetDevelopment.odd_normal_remainder_connected F D ho

lemma short_tail_root_not_marked (hl : D.rep.tail.length ≤ 1) :
    ¬MarkedPartition (remainder F D) (normalBudget F D) D.root := by
  rintro ⟨E,b,P,hE,hEc,hP,_,hPE⟩
  obtain ⟨U,hUs,hrest,hpaths,_,hparts⟩ := replace_path_group_tracked D.family
    (normalIndices F D)
    (fun j hj ↦ (D.family.one_defect_other_paths D.score D.rep.index D.rep.member_not_path).2
      j (Finset.mem_erase.mp hj).1) E hE hEc
  have hkeep := hrest D.rep.index (by simp [normalIndices])
  let M : RootedCycleRep U D.root :=
    { D.rep with
      start_eq := hkeep.1.trans D.rep.start_eq
      finish_eq := hkeep.2.1.trans D.rep.finish_eq
      subgraph := hkeep.2.2.trans D.rep.subgraph }
  have hmax : ∀ W : TrailFamily F.graph (budget F.order), W.score ≤ U.score := by
    intro W
    rw [hUs]
    exact D.maximum W
  have hmin : ∀ W : TrailFamily F.graph (budget F.order), ∀ r, ∀ N : RootedCycleRep W r,
      W.score=U.score → M.cycle.length ≤ N.cycle.length := by
    intro W r N hWs
    exact D.cycle_minimum W r N (hWs.trans hUs)
  have hno := minimum_short_tail_other_endpoints_avoid_root U (by rw [hUs]; exact D.score) hmax D.root M hmin hl
  obtain ⟨j,hj,hUj⟩ := hparts P.toSubgraph hPE
  let Q := P.mapLe (selectedGraph_le D.family (normalIndices F D))
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le D.family (normalIndices F D))) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hends := MarkedBudgets.endpoint_of_path_rep Q hQ (U.walk j) (U.isTrail j)
    (hUj.trans hQe.symm)
  have hji := (Finset.mem_erase.mp hj).1
  rcases hends with ha|hb
  · exact (hno j hji).1 ha.symm
  · exact (hno j hji).2 hb.symm

end Erdos583NormalRemainderCriticalDevelopment
