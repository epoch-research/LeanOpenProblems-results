import Submission.CubicTriangleReduction

/-! The unique ordinary carrier at a degree-five short triangular defect. -/
namespace Erdos583ShortTriangleSingleCarrierDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma short_triangle_degree_five_unique_carrier {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hq : T.quota r=1)
    (hd : Nat.card (G.neighborSet r)=5) :
    ∃ j : Fin k, j ≠ L.index ∧ r ∈ (T.walk j).support ∧
      ∀ l : Fin k, l ≠ L.index →
        (∃ v ∈ L.cycle.support, v ∈ (T.walk l).support) → l=j := by
  classical
  let S := Finset.univ.filter fun j ↦ ∃ v ∈ L.cycle.support, v ∈ (T.walk j).support
  have hi : L.index ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,r,L.cycle.start_mem_support,?_⟩
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  have hh := short_triangle_carrier_degree_identity T hs hm r L hc ht hq
  have hcard : S.card=2 := by change _=2*S.card+1 at hh; omega
  have herase : (S.erase L.index).card=1 := by rw [Finset.card_erase_of_mem hi,hcard]
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp herase
  have hjmem : j ∈ S.erase L.index := by rw [hj]; simp
  have hji := (Finset.mem_erase.mp hjmem).1
  obtain ⟨v,hvC,hvj⟩ := (Finset.mem_filter.mp (Finset.mem_erase.mp hjmem).2).2
  refine ⟨j,hji,short_triangle_member_contains_root T hs hm r L hc ht j hvC hvj,?_⟩
  intro l hli hl
  have hlS : l ∈ S.erase L.index := Finset.mem_erase.mpr ⟨hli,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩⟩
  simpa only [hj,Finset.mem_singleton] using hlS

lemma cycle_nonroot_endpoint_not_defective {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r)
    {v : V} (hvC : v ∈ L.cycle.support) (hvr : v ≠ r)
    {j : Fin k} (hj : v=T.start j ∨ v=T.finish j) : j ≠ L.index := by
  rintro rfl
  rcases hj with hj | hj
  · exact hvr (hj.trans L.start_eq)
  · have he : v=L.finish := hj.trans L.finish_eq
    exact hvr (L.inter v hvC (he.symm ▸ L.tail.end_mem_support))

lemma cubic_cycle_vertex_endpoint {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r)
    {v : V} (hvC : v ∈ L.cycle.support) (hvr : v ≠ r)
    (hd : Nat.card (G.neighborSet v)=3) :
    ∃ j : Fin k, j ≠ L.index ∧ (v=T.start j ∨ v=T.finish j) := by
  have ho : Odd (Nat.card (G.neighborSet v)) := by rw [hd]; decide
  obtain ⟨j,hj⟩ := DeletionEndpoint.endpoint_of_positive_quota T ((QuotaParity.quota_odd_iff T v).mpr ho).pos
  exact ⟨j,cycle_nonroot_endpoint_not_defective T r L hvC hvr hj,hj⟩

lemma orient_path_between_endpoints {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (j : Fin k) (hp : (T.walk j).IsPath)
    {x y : V} (hxy : x ≠ y)
    (hx : x=T.start j ∨ x=T.finish j) (hy : y=T.start j ∨ y=T.finish j) :
    ∃ P : G.Walk x y, P.IsPath ∧ (T.walk j).toSubgraph=P.toSubgraph := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hxy (hx.trans hy.symm)).elim
  · exact ⟨(T.walk j).copy hx.symm hy.symm,by simpa using hp,
      by simp only [NormalTrailSystem.walk_copy_subgraph]⟩
  · exact ⟨(T.walk j).reverse.copy hx.symm hy.symm,by simpa using hp.reverse,
      by simp only [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]⟩
  · exact (hxy (hx.trans hy.symm)).elim

lemma degree_five_two_cubic_carrier {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hq : T.quota r=1)
    (hd : Nat.card (G.neighborSet r)=5)
    {x y : V} (hxC : x ∈ L.cycle.support) (hyC : y ∈ L.cycle.support)
    (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3) :
    ∃ j : Fin k, j ≠ L.index ∧ ∃ P : G.Walk x y,
      P.IsPath ∧ (T.walk j).toSubgraph=P.toSubgraph ∧ r ∈ P.support ∧
      Disjoint L.cycle.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
  obtain ⟨j,hji,hrj,hunique⟩ := short_triangle_degree_five_unique_carrier T hs hm r L hc ht hq hd
  have hend {v} (hvC : v ∈ L.cycle.support) (hvr : v ≠ r) (hdv : Nat.card (G.neighborSet v)=3) :
      v=T.start j ∨ v=T.finish j := by
    obtain ⟨l,hli,hl⟩ := cubic_cycle_vertex_endpoint T r L hvC hvr hdv
    have hvl : v ∈ (T.walk l).support := by
      rcases hl with hl | hl
      · exact hl ▸ (T.walk l).start_mem_support
      · exact hl ▸ (T.walk l).end_mem_support
    have hlj := hunique l hli ⟨v,hvC,hvl⟩
    exact hlj ▸ hl
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hji
  obtain ⟨P,hP,hPe⟩ := orient_path_between_endpoints T j hp hxy (hend hxC hxr hdx) (hend hyC hyr hdy)
  refine ⟨j,hji,P,hP,hPe,?_,?_⟩
  · rwa [←Walk.mem_verts_toSubgraph,hPe,Walk.mem_verts_toSubgraph] at hrj
  · rw [←hPe]
    apply (T.disjoint (Ne.symm hji)).mono_left
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_left

end Erdos583ShortTriangleSingleCarrierDevelopment
