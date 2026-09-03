import Submission.AdjacentEndpointUnpairing

/-! In an all-odd normal path system, an endpoint can avoid carrying a
specified edge when it is distinct from, and nonadjacent to, one end of that
edge. This does not assert that the edge carrier avoids the vertex internally,
or give simultaneous avoidance at several endpoints. -/
namespace Erdos583EndpointEdgeAvoidanceDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.NormalTrailSystem Erdos583Work.TrailNormalization
open Erdos583AdjacentEndpointUnpairingDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma endpoint_owner_avoids_edge_of_nonadjacent {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : NormalTrailSystem G k)
    (hp : ∀ i, (T.walk i).IsPath) {x y a : V}
    (h : G.Adj x y) (hxa : x ≠ a) (hna : ¬G.Adj x a) :
    ∃ U : NormalTrailSystem G k, (∀ i, (U.walk i).IsPath) ∧
      U.score=T.score ∧ s(x,y) ∉ (U.walk (owner U a)).toSubgraph.edgeSet := by
  classical
  obtain ⟨S,hSs,t,Q,hQ,hmem⟩ := force_first_edge T (all_paths_maximum T hp) h
  have hSp : ∀ i, (S.walk i).IsPath := S.score_eq_edges_add_iff.mp
    (hSs.trans (T.score_eq_edges_add_iff.mpr hp))
  have hpath := max_score_member_isPath S (all_paths_maximum S hSp) _ hQ hmem
  obtain ⟨i,hends,hi⟩ := hmem
  have he : s(x,y) ∈ (S.walk i).toSubgraph.edgeSet := by rw [hi]; simp
  by_cases hai : owner S a=i
  · have hae := (endpoint_iff_owner S a i).mpr hai
    have hat : a=t := by
      rcases hends with hh|hh
      · rw [hh.1,hh.2] at hae
        exact hae.resolve_left hxa.symm
      · rw [hh.1,hh.2] at hae
        exact hae.resolve_right hxa.symm
    subst t
    have hnQ : ¬Q.Nil := by
      intro hh
      exact hna (hh.eq ▸ h)
    obtain ⟨U,hUs,hUi⟩ := InducedBuffer.shorten_path_member_nonadj S i h Q hnQ hpath hna hi
    have hUp : ∀ j, (U.walk j).IsPath := U.score_eq_edges_add_iff.mp
      (hUs.trans (S.score_eq_edges_add_iff.mpr hSp))
    have hown : owner U a=i := (endpoint_iff_owner U a i).mp
      (SingletonRotation.endpoints_of_path_subgraph U i Q hpath.of_cons hnQ hUi).2
    refine ⟨U,hUp,hUs.trans hSs,?_⟩
    rw [hown,hUi]
    intro hh
    have hnodup := hpath.isTrail.edges_nodup
    rw [Walk.edges_cons,List.nodup_cons] at hnodup
    exact hnodup.1 (Q.mem_edges_toSubgraph.mp hh)
  · refine ⟨S,hSp,hSs,?_⟩
    intro hh
    exact Set.disjoint_left.mp (S.disjoint hai) hh he

end Erdos583EndpointEdgeAvoidanceDevelopment
