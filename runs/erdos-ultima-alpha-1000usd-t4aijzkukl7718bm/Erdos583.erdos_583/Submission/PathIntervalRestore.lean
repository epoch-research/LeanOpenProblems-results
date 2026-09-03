import Submission.Work
import Submission.PathIntervals

/-! Reattaching the two outside portions of a path after an interval exchange. -/
namespace Erdos583PathIntervalRestoreDevelopment
open SimpleGraph Erdos583Work Erdos583PathIntervalsDevelopment
open Erdos583Work.QuotaSurgery Erdos583Work.TriangleAbsorption
set_option maxHeartbeats 1800000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}

omit [Fintype V] in
lemma full_interval_edges (P : G.Walk a b) :
    (interval P 0 P.length (Nat.zero_le _)).toSubgraph.edgeSet=P.toSubgraph.edgeSet := by
  ext e
  rw [interval_edges P _ le_rfl,Walk.mem_edges_toSubgraph,edges_positions]
  simp

lemma restore_two (P : G.Walk a b) (hp : P.IsPath) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.length) {z : V}
    (X : G.Walk (P.getVert i) z) (Y : G.Walk (P.getVert j) z)
    (hX : X.IsPath) (hY : Y.IsPath) (hdXY : Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet)
    (K : Set (Sym2 V)) (hdK : Disjoint K P.toSubgraph.edgeSet)
    (heXY : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=K ∪ (interval P i j hij).toSubgraph.edgeSet)
    (hsX : ∀ x ∈ X.support, x ∈ (interval P i j hij).support)
    (hsY : ∀ x ∈ Y.support, x ∈ (interval P i j hij).support) :
    TwoPathCover (G := G) (K ∪ P.toSubgraph.edgeSet) := by
  classical
  let L := interval P 0 i (Nat.zero_le _)
  let R := (interval P j P.length hj).reverse
  let A := L.append X
  let B := R.append Y
  have hA : A.IsPath := by
    apply path_append_of_support_intersection (interval_isPath P hp _) hX
    intro x hx hxX
    exact (interval_support_inter P hp (Nat.zero_le _) hij le_rfl hj hx (hsX x hxX)).2
  have hB : B.IsPath := by
    apply path_append_of_support_intersection (interval_isPath P hp hj).reverse hY
    intro x hx hxY
    have hx' : x ∈ (interval P j P.length hj).support := by simpa only [R,Walk.support_reverse,List.mem_reverse] using hx
    exact (interval_support_inter P hp hij hj le_rfl le_rfl (hsY x hxY) hx').2
  have hall : L.toSubgraph.edgeSet ∪ (interval P i j hij).toSubgraph.edgeSet ∪ R.toSubgraph.edgeSet=P.toSubgraph.edgeSet := by
    simp only [L,R,Walk.toSubgraph_reverse]
    rw [interval_edges_append P (Nat.zero_le _) hij hj,
      interval_edges_append P (Nat.zero_le _) hj le_rfl,full_interval_edges]
  have hc : A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet=K ∪ P.toSubgraph.edgeSet := by
    simp only [A,B,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    ext e
    have hh := congrArg (fun S : Set (Sym2 V) ↦ e ∈ S) hall
    have hxy := congrArg (fun S : Set (Sym2 V) ↦ e ∈ S) heXY
    simp only [Set.mem_union] at hh hxy ⊢
    tauto
  have hkm : Disjoint K (interval P i j hij).toSubgraph.edgeSet :=
    hdK.mono_right (interval_edges_subset P hij hj)
  have hlenXY := congrArg Set.ncard heXY
  rw [Set.ncard_union_eq hdXY,Set.ncard_union_eq hkm,trail_edgeSet_ncard X hX.isTrail,
    trail_edgeSet_ncard Y hY.isTrail,trail_edgeSet_ncard _ (interval_isPath P hp hij).isTrail,
    interval_length P hij hj] at hlenXY
  have hlen : A.length+B.length=(K ∪ P.toSubgraph.edgeSet).ncard := by
    rw [Set.ncard_union_eq hdK,trail_edgeSet_ncard P hp.isTrail]
    simp only [A,B,L,R,Walk.length_append,Walk.length_reverse,
      interval_length P (Nat.zero_le _) (hij.trans hj),interval_length P hj le_rfl,Nat.sub_zero]
    omega
  exact ⟨P.getVert 0,z,P.getVert P.length,z,A,B,hA,hB,
    TriangleAbsorption.disjoint_of_cover_length A B hA.isTrail hB.isTrail _ hc hlen,hc⟩

end Erdos583PathIntervalRestoreDevelopment
