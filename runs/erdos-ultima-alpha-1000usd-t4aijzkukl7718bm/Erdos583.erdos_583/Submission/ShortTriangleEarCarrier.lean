import Submission.PathEarExchange

/-! An external shortcut cannot be carried by a second ordinary path beside a short triangle. -/
namespace Erdos583ShortTriangleEarCarrierDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.TailEar
open Erdos583PathEarExchangeDevelopment Erdos583ShortTriangleIncidenceDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma short_triangle_no_ordinary_ear_chord {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    (j l : Fin k) (hji : j ≠ L.index) (hli : l ≠ L.index)
    (hunique : ∀ m : Fin k, m ≠ L.index →
      (∃ v ∈ L.cycle.support, v ∈ (T.walk m).support) → m=j)
    {a x b : V} (hxC : x ∈ L.cycle.support) (hxr : x ≠ r)
    (A : G.Walk (T.start j) a) (B : G.Walk b (T.finish j))
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : G.Adj a b)
    (hform : T.walk j=A.append (Walk.cons hax (Walk.cons hxb B)))
    (he : s(a,b) ∈ (T.walk l).edges) : False := by
  classical
  have hP : (T.walk j).IsPath := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hji
  have hQ : (T.walk l).IsPath := (T.one_defect_other_paths hs L.index L.member_not_path).2 l hli
  have hp : (A.append (Walk.cons hax (Walk.cons hxb B))).IsPath := hform ▸ hP
  have hjl : j ≠ l := by
    rintro rfl
    exact tail_ear_chord_not_mem A B hax hxb hab hp (hform ▸ he)
  have hxQ : x ∉ (T.walk l).support := fun hh ↦ hjl (hunique l hli ⟨x,hxC,hh⟩).symm
  have hrQ : r ∉ (T.walk l).support := fun hh ↦
    hjl (hunique l hli ⟨r,L.cycle.start_mem_support,hh⟩).symm
  let P' := A.append (Walk.cons hab B)
  have hP' : P'.IsPath := shortcut_isPath A B hax hxb hab hp
  obtain ⟨Q',hQ',hsep,hcover,hQ'e⟩ := path_ear_exchange A B hax hxb hab hp (T.walk l) hQ he hxQ
    (by rw [←hform]; exact T.disjoint hjl)
  rw [←hform] at hcover
  obtain ⟨U,hUj,hUl,hrest,hstarts,hfinish,hscore,_⟩ := replace_two_starts_general T j l hjl
    (T.start j) (T.start l) P' Q' hP'.isTrail hQ'.isTrail hsep hcover
  have hlen := congrArg Set.ncard hcover
  rw [Set.ncard_union_eq hsep,Set.ncard_union_eq (T.disjoint hjl),
    trail_edgeSet_ncard P' hP'.isTrail,trail_edgeSet_ncard Q' hQ'.isTrail,
    trail_edgeSet_ncard _ (T.isTrail j),trail_edgeSet_ncard _ (T.isTrail l)] at hlen
  rw [(walk_vertex_ncard_eq_iff _).mpr hP,(walk_vertex_ncard_eq_iff _).mpr hQ,
    (walk_vertex_ncard_eq_iff _).mpr hP',(walk_vertex_ncard_eq_iff _).mpr hQ'] at hscore
  have hUs : U.score=T.score := by omega
  have hUa : U.start L.index=r := by
    rw [hstarts]
    simp only [if_neg hji.symm,if_neg hli.symm,L.start_eq]
  have hUb : U.finish L.index=L.finish := (congrFun hfinish L.index).trans L.finish_eq
  let M : RootedCycleRep U r :=
    ⟨L.index,L.finish,hUa,hUb,L.cycle,L.tail,L.isCycle,L.isPath,L.inter,
      (hrest L.index hji.symm hli.symm).trans L.subgraph⟩
  have hxQ' : x ∈ Q'.support := by
    have hh : s(a,x) ∈ Q'.toSubgraph.edgeSet := hQ'e.symm ▸ Or.inr (Or.inl rfl)
    exact Walk.mem_support_of_adj_toSubgraph hh.symm
  have hxl : x ∈ (U.walk l).support := by
    rw [←Walk.mem_verts_toSubgraph,hUl,Walk.mem_verts_toSubgraph]
    exact hxQ'
  have hrl := short_triangle_member_contains_root U (by omega)
    (fun W ↦ (hm W).trans_eq hUs.symm) r M hc ht l hxC hxl
  rw [←Walk.mem_verts_toSubgraph,hUl,Walk.mem_verts_toSubgraph] at hrl
  rcases ear_expansion_support_subset (T.walk l) Q' he hQ'e r hrl with hh | hh
  · exact hxr hh.symm
  · exact hrQ hh

end Erdos583ShortTriangleEarCarrierDevelopment
