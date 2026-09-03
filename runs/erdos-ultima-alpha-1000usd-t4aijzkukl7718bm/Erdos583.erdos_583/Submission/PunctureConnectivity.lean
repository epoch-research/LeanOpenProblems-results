import Submission.ShortTriangleDegreeSeven

/-! Connectivity under suppression and deletion of a bypassed edge. -/
namespace Erdos583PunctureConnectivityDevelopment
open SimpleGraph Erdos583Work Erdos583SupportSmoothingDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma puncture_degree_two_connected_of_shortcut {V : Type*} {G : SimpleGraph V}
    (hG : SupportConnected G) {x a b : V} (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hab : G.Adj a b) (hNx : ∀ z, G.Adj x z → z=a ∨ z=b) :
    SupportConnected (puncture G ({x} : Set V)) := by
  have hh := smooth_support_connected hG hxa hxb hab.ne hNx
  have he : smooth G x a b=puncture G ({x} : Set V) :=
    sup_eq_left.mpr ((edge_le_iff _).mpr (Or.inr ⟨hab,hxa.ne.symm,hxb.ne.symm⟩))
  exact he ▸ hh

lemma puncture_pair_eq_of_triangle_deletion {V : Type*} (G : SimpleGraph V) (r x y : V) :
    puncture (puncture (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))) {x}) {y}=
      puncture G ({x,y} : Set V) := by
  ext u v
  simp only [puncture_adj,deleteEdges_adj,Set.mem_singleton_iff,Set.mem_insert_iff]
  constructor
  · tauto
  · rintro ⟨huv,hu,hv⟩
    refine ⟨⟨⟨huv,?_⟩,fun hh ↦ hu (Or.inl hh),fun hh ↦ hv (Or.inl hh)⟩,
      fun hh ↦ hu (Or.inr hh),fun hh ↦ hv (Or.inr hh)⟩
    rintro (he|he|he) <;>
      rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp_all

lemma supported_delete_edge_connected {V : Type*} {G : SimpleGraph V}
    (hG : SupportConnected G) {a b : V}
    (hab : (G.deleteEdges {s(a,b)}).Reachable a b) :
    SupportConnected (G.deleteEdges {s(a,b)}) := by
  have hedge (u v : V) (huv : G.Adj u v) : (G.deleteEdges {s(a,b)}).Reachable u v := by
    by_cases he : s(u,v)=s(a,b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hab
      · exact hab.symm
    · exact (show (G.deleteEdges {s(a,b)}).Adj u v from deleteEdges_adj.mpr ⟨huv,he⟩).reachable
  intro u hu v hv
  exact reachable_map_to_reachable id hedge (hG u (support_mono (deleteEdges_le _) hu)
    v (support_mono (deleteEdges_le _) hv))

lemma delete_edge_reachable_of_old {V : Type*} {G : SimpleGraph V} {a b u v : V}
    (hab : (G.deleteEdges {s(a,b)}).Reachable a b) (huv : G.Reachable u v) :
    (G.deleteEdges {s(a,b)}).Reachable u v := by
  apply reachable_map_to_reachable id _ huv
  intro s t hst
  by_cases he : s(s,t)=s(a,b)
  · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hab
    · exact hab.symm
  · exact (show (G.deleteEdges {s(a,b)}).Adj s t from deleteEdges_adj.mpr ⟨hst,he⟩).reachable

end Erdos583PunctureConnectivityDevelopment
