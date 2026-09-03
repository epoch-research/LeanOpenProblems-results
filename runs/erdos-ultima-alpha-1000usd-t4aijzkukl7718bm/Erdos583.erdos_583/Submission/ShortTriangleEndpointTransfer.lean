import Submission.OrdinaryPairReplacement

/-! Endpoint transfer propagates root containment across an external edge. -/
namespace Erdos583ShortTriangleEndpointTransferDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583OrdinaryPairReplacementDevelopment Erdos583ShortTriangleIncidenceDevelopment
open Erdos583MixedTriangleTerminalExclusionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma short_triangle_terminal_transfer {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    (i j : Fin k) (hij : i ≠ j) (hiL : i ≠ L.index) (hjL : j ≠ L.index)
    {v b d e : V} (hvb : G.Adj v b) (P : G.Walk b d) (Q : G.Walk b e)
    (hP : (Walk.cons hvb P).IsPath) (hQ : Q.IsPath)
    (hPi : (T.walk i).toSubgraph=(Walk.cons hvb P).toSubgraph)
    (hQj : (T.walk j).toSubgraph=Q.toSubgraph)
    (hvC : v ∈ L.cycle.support) (hvr : v ≠ r) (hrQ : r ∉ Q.support) : False := by
  classical
  have hvQ : v ∉ Q.support := by
    intro hvQ
    apply hrQ
    have hvj : v ∈ (T.walk j).support := by
      rwa [←Walk.mem_verts_toSubgraph,hQj,Walk.mem_verts_toSubgraph]
    have hh := short_triangle_member_contains_root T hs hm r L hc ht j hvC hvj
    rwa [←Walk.mem_verts_toSubgraph,hQj,Walk.mem_verts_toSubgraph] at hh
  have hQ' : (Walk.cons hvb Q).IsPath := (Walk.cons_isPath_iff hvb Q).mpr ⟨hQ,hvQ⟩
  have hdold : Disjoint (Walk.cons hvb P).toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [←hPi,←hQj]; exact T.disjoint hij
  have heP : s(v,b) ∉ P.toSubgraph.edgeSet := by
    intro hh
    exact (Walk.cons_isPath_iff hvb P).mp hP |>.2
      (P.fst_mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp hh))
  have hd : Disjoint P.toSubgraph.edgeSet (Walk.cons hvb Q).toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    rw [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons] at hz'
    rcases hz' with rfl | hz'
    · exact heP hz
    · exact Set.disjoint_left.mp hdold
        (by rw [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons]; exact Or.inr (P.mem_edges_toSubgraph.mp hz))
        (Q.mem_edges_toSubgraph.mpr hz')
  have he : P.toSubgraph.edgeSet ∪ (Walk.cons hvb Q).toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [hPi,hQj]
    ext z
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons]
    tauto
  obtain ⟨U,M,hUs,hMC,hMT,_,hUj⟩ := replace_two_paths_preserving_root T hs r L i j hij hiL hjL
    P (Walk.cons hvb Q) hP.of_cons hQ' hd he
  have hsU : U.score+1=G.edgeSet.ncard+k := by omega
  have hmU : ∀ A : TrailFamily G k, A.score ≤ U.score := by intro A; rw [hUs]; exact hm A
  have hvM : v ∈ M.cycle.support := by rwa [hMC]
  have hvU : v ∈ (U.walk j).support := by
    rw [←Walk.mem_verts_toSubgraph,hUj,Walk.mem_verts_toSubgraph]
    simp
  have hrU := short_triangle_member_contains_root U hsU hmU r M (by rwa [hMC])
    (by rwa [hMT]) j hvM hvU
  rw [←Walk.mem_verts_toSubgraph,hUj,Walk.mem_verts_toSubgraph,Walk.support_cons,List.mem_cons] at hrU
  exact hrU.elim (fun h ↦ hvr h.symm) hrQ

end Erdos583ShortTriangleEndpointTransferDevelopment
