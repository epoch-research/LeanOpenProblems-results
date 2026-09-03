import Submission.CubicTriangleDeletion

/-! The external edge at a cubic cycle vertex begins its ordinary endpoint carrier. -/
namespace Erdos583CubicExternalCarrierDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleSingleCarrierDevelopment Erdos583ShortTriangleIncidenceDevelopment
open Erdos583MixedTriangleTerminalExclusionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma cycle_cubic_external_carrier {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2) {v w b : V}
    (hvC : v ∈ L.cycle.support) (hvr : v ≠ r)
    (hvrC : s(v,r) ∈ L.cycle.toSubgraph.edgeSet) (hvwC : s(v,w) ∈ L.cycle.toSubgraph.edgeSet)
    (hNv : ∀ z, G.Adj v z → z=r ∨ z=w ∨ z=b) (hdv : Nat.card (G.neighborSet v)=3) :
    ∃ i : Fin k, i ≠ L.index ∧ ∃ d, ∃ P : G.Walk v d,
      P.IsPath ∧ (T.walk i).toSubgraph=P.toSubgraph ∧ s(v,b) ∈ P.edges := by
  obtain ⟨i,hiL,hiv⟩ := cubic_cycle_vertex_endpoint T r L hvC hvr hdv
  obtain ⟨d,P,hP,hPi⟩ := orient_path_at_endpoint (T.walk i)
    ((T.one_defect_other_paths hs L.index L.member_not_path).2 i hiL) hiv
  have hvi : v ∈ (T.walk i).support := by
    rw [←Walk.mem_verts_toSubgraph,hPi,Walk.mem_verts_toSubgraph]; exact P.start_mem_support
  have hrP := short_triangle_member_contains_root T hs hm r L hc ht i hvC hvi
  rw [←Walk.mem_verts_toSubgraph,hPi,Walk.mem_verts_toSubgraph] at hrP
  have hnot {e : Sym2 V} (he : e ∈ L.cycle.toSubgraph.edgeSet) : e ∉ P.edges := by
    intro hh
    apply Set.disjoint_left.mp (T.disjoint hiL.symm)
    · rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]; exact Or.inl he
    · rw [hPi]; exact P.mem_edges_toSubgraph.mpr hh
  refine ⟨i,hiL,d,P,hP,hPi,?_⟩
  cases P with
  | nil => exact (hvr.symm (by simpa using hrP)).elim
  | @cons _ z _ hvz Q =>
    have hzb : z=b := by
      rcases hNv z hvz with hz | hz | hh
      · subst z
        exact (hnot hvrC (by simp)).elim
      · subst z
        exact (hnot hvwC (by simp)).elim
      · exact hh
    subst z
    simp

lemma short_triangle_cubic_external_carrier {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) {x y b : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b) (hdy : Nat.card (G.neighborSet y)=3) :
    ∃ i : Fin k, i ≠ L.index ∧ ∃ d, ∃ P : G.Walk y d,
      P.IsPath ∧ (T.walk i).toSubgraph=P.toSubgraph ∧ s(y,b) ∈ P.edges := by
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  obtain ⟨i,hiL,hiy⟩ := cubic_cycle_vertex_endpoint T r L hyC hry.ne.symm hdy
  obtain ⟨d,P,hP,hPi⟩ := orient_path_at_endpoint (T.walk i)
    ((T.one_defect_other_paths hs L.index L.member_not_path).2 i hiL) hiy
  have hyi : y ∈ (T.walk i).support := by
    rw [←Walk.mem_verts_toSubgraph,hPi,Walk.mem_verts_toSubgraph]; exact P.start_mem_support
  have hrP := short_triangle_member_contains_root T hs hm r L hc ht i hyC hyi
  rw [←Walk.mem_verts_toSubgraph,hPi,Walk.mem_verts_toSubgraph] at hrP
  have hnot {e : Sym2 V} (he : e ∈ L.cycle.toSubgraph.edgeSet) : e ∉ P.edges := by
    intro hh
    apply Set.disjoint_left.mp (T.disjoint hiL.symm)
    · rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]; exact Or.inl he
    · rw [hPi]; exact P.mem_edges_toSubgraph.mpr hh
  refine ⟨i,hiL,d,P,hP,hPi,?_⟩
  cases P with
  | nil => exact (hry.ne (by simpa using hrP)).elim
  | @cons _ z _ hyz Q =>
    have hzb : z=b := by
      rcases hNy z hyz with hz | hz | hh
      · subst z
        exact (hnot (show s(y,r) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp) (by simp)).elim
      · subst z
        exact (hnot (show s(y,x) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp [Sym2.eq_swap]) (by simp)).elim
      · exact hh
    subst z
    simp

end Erdos583CubicExternalCarrierDevelopment
