import Submission.SubdividedFiveFinite

/-! Map the finite subdivided-five cycle partitions into an arbitrary simple graph. -/
namespace Erdos583SubdividedFiveCyclesDevelopment
open SimpleGraph Erdos583SubdividedFiveFiniteDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma base_cycle_choice {u v : Fin 6} (huv : base.Adj u v) :
    ∃ C D : base.Walk 0 0, C.IsCycle ∧ C.length=5 ∧ D.IsCycle ∧
      (∀ z : Fin 6, z ∈ D.support) ∧ s(u,v) ∈ D.toSubgraph.edgeSet ∧
      Disjoint C.toSubgraph.edgeSet D.toSubgraph.edgeSet ∧
      C.toSubgraph.edgeSet ∪ D.toSubgraph.edgeSet=base.edgeSet := by
  rcases every_edge_in_long u v huv with hh | hh | hh
  · exact ⟨short0,long0,short0_cycle,short0_length,long0_cycle,long0_spanning,hh,pair0_disjoint,pair0_cover⟩
  · exact ⟨short1,long1,short1_cycle,short1_length,long1_cycle,long1_spanning,hh,pair1_disjoint,pair1_cover⟩
  · exact ⟨short2,long2,short2_cycle,short2_length,long2_cycle,long2_spanning,hh,pair2_disjoint,pair2_cover⟩

lemma map_walk_edgeSet {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W} (f : H →g G)
    {a b : V} (P : H.Walk a b) :
    (P.map f).toSubgraph.edgeSet=Sym2.map f '' P.toSubgraph.edgeSet := by
  ext e
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_map,List.mem_map,Set.mem_image]

lemma mapped_cycle_choice {V : Type*} {G : SimpleGraph V} (f : base →g G)
    (hf : Function.Injective f) {u v : Fin 6} (huv : base.Adj u v) :
    ∃ C D : G.Walk (f 0) (f 0), C.IsCycle ∧ C.length=5 ∧ D.IsCycle ∧
      (∀ z : V, z ∈ D.support ↔ z ∈ Set.range f) ∧
      s(f u,f v) ∈ D.toSubgraph.edgeSet ∧
      Disjoint C.toSubgraph.edgeSet D.toSubgraph.edgeSet ∧
      C.toSubgraph.edgeSet ∪ D.toSubgraph.edgeSet=Sym2.map f '' base.edgeSet := by
  obtain ⟨C,D,hC,hCl,hD,hDs,he,hd,hcov⟩ := base_cycle_choice huv
  refine ⟨C.map f,D.map f,hC.map hf,by simpa using hCl,hD.map hf,?_,?_,?_,?_⟩
  · intro z
    simp only [Walk.support_map,List.mem_map,Set.mem_range]
    constructor
    · rintro ⟨u,_,hu⟩; exact ⟨u,hu⟩
    · rintro ⟨u,hu⟩; exact ⟨u,hDs u,hu⟩
  · rw [map_walk_edgeSet]
    exact ⟨s(u,v),he,rfl⟩
  · rw [map_walk_edgeSet,map_walk_edgeSet]
    exact Set.disjoint_image_of_injective (Sym2.map.injective hf) hd
  · rw [map_walk_edgeSet,map_walk_edgeSet,←Set.image_union,hcov]

end Erdos583SubdividedFiveCyclesDevelopment
