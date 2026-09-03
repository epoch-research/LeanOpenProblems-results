import Submission.RunEdgeCount
import Submission.TailPrefixRunFreshness

/-! Edge saving when a private final suffix is removed in addition to
compressing complete prefix runs. -/
namespace Erdos583PrefixCompressionEdgeCountDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583CycleRunIntervalsDevelopment Erdos583PrivatePathExpansionDevelopment
open Erdos583RunCompressionDataDevelopment Erdos583RunEdgeCountDevelopment
open Erdos583TailPrefixRunFreshnessDevelopment
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma selected_complement_edge_count {k : ℕ} (T : TrailFamily G k) (A : Finset (Fin k)) :
    (selectedGraph T A).edgeSet.ncard+(selectedGraph T (Finset.univ \ A)).edgeSet.ncard=G.edgeSet.ncard := by
  have hd : Disjoint (selectedGraph T A).edgeSet (selectedGraph T (Finset.univ \ A)).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,hi,hei⟩ := (selected_edge_iff T A e).mp he
    obtain ⟨j,hj,hej⟩ := (selected_edge_iff T (Finset.univ \ A) e).mp hf
    exact Set.disjoint_left.mp (T.disjoint (show i ≠ j from fun h ↦ (Finset.mem_sdiff.mp hj).2 (h ▸ hi))) hei hej
  have he : (selectedGraph T A).edgeSet ∪ (selectedGraph T (Finset.univ \ A)).edgeSet=G.edgeSet := by
    ext e
    constructor
    · rintro (he|he)
      · obtain ⟨i,_,hi⟩ := (selected_edge_iff T A e).mp he
        exact (T.walk i).toSubgraph.edgeSet_subset hi
      · obtain ⟨i,_,hi⟩ := (selected_edge_iff T (Finset.univ \ A) e).mp he
        exact (T.walk i).toSubgraph.edgeSet_subset hi
    · intro he
      obtain ⟨i,hi⟩ := (T.cover e).mp he
      by_cases hiA : i ∈ A
      · exact Or.inl ((selected_edge_iff T A e).mpr ⟨i,hiA,hi⟩)
      · exact Or.inr ((selected_edge_iff T (Finset.univ \ A) e).mpr ⟨i,by simp [hiA],hi⟩)
  rw [←Set.ncard_union_eq hd,he]

lemma prefix_compression_edge_saving {a w b : V}
    (W : G.Walk a w) (Q : G.Walk w b) (hp : (W.append Q).IsPath)
    (S : Set V) (hQ : ∀ z ∈ Q.support, z ≠ w → z ∈ S)
    (H : SimpleGraph V) (hH : H.support ⊆ Sᶜ) :
    (H ⊔ chords (runs W S) (runStart W) (runFinish W)).edgeSet.ncard+
      (runs W S).card+Q.length ≤
      ((H ⊔ arcs (runs W S) (runPath W)) ⊔ Q.toSubgraph.spanningCoe).edgeSet.ncard := by
  have hd : Disjoint (H ⊔ arcs (runs W S) (runPath W)).edgeSet Q.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | h x y =>
      change H.Adj x y ∨ (arcs (runs W S) (runPath W)).Adj x y at he
      rcases he with he|he
      · have hx : x=w := by
          by_contra hn
          exact hH ⟨y,he⟩ (hQ x (Walk.mem_support_of_adj_toSubgraph hf) hn)
        have hy : y=w := by
          by_contra hn
          exact hH ⟨x,he.symm⟩ (hQ y (Walk.mem_support_of_adj_toSubgraph
            (show Q.toSubgraph.Adj x y from hf).symm) hn)
        exact he.ne (hx.trans hy.symm)
      · obtain ⟨p,_,he⟩ := (arcs_adj _ _ _ _).mp he
        exact Set.disjoint_left.mp (RootedTailSystem.append_trail_disjoint hp.isTrail)
          (runPath_edges_subset W p (show s(x,y) ∈ (runPath W p).toSubgraph.edgeSet from he)) hf
  have hsave := RunConditions.compression_edge_saving W S (path_run_conditions W hp.of_append_left S) H hH
  have hcount : ((H ⊔ arcs (runs W S) (runPath W)) ⊔ Q.toSubgraph.spanningCoe).edgeSet.ncard=
      (H ⊔ arcs (runs W S) (runPath W)).edgeSet.ncard+Q.length := by
    rw [edgeSet_sup]
    change ((H ⊔ arcs (runs W S) (runPath W)).edgeSet ∪ Q.toSubgraph.edgeSet).ncard=_
    rw [Set.ncard_union_eq hd,path_edgeSet_ncard hp.of_append_right]
  rw [hcount]
  omega

end Erdos583PrefixCompressionEdgeCountDevelopment
