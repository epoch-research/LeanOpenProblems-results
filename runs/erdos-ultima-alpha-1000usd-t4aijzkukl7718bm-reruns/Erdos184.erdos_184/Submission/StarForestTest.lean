import Submission.ForestMixedCompletion
open SimpleGraph
open scoped Classical
namespace Erdos184.ForestMixedCompletion
variable {V : Type*} [Fintype V]
lemma acyclic_of_all_edges_at (B : SimpleGraph V) (v : V)
    (h : ∀ a b, B.Adj a b → a = v ∨ b = v) : B.IsAcyclic := by
  intro a p hp
  have h2 : (p.toSubgraph.neighborSet a).ncard = 2 :=
    hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support
  have hex : (p.toSubgraph.neighborSet a).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  obtain ⟨b,hb⟩ := hex
  have hne : a ≠ b := (p.toSubgraph.adj_sub hb).ne
  obtain ⟨w,hw,hwv⟩ : ∃ w ∈ p.support, w ≠ v := by
    by_cases hav : a = v
    · refine ⟨b, ?_, ?_⟩
      · exact p.mem_verts_toSubgraph.mp (p.toSubgraph.neighborSet_subset_verts a hb)
      · intro hbv; exact hne (hav.trans hbv.symm)
    · exact ⟨a,p.start_mem_support,hav⟩
  have hsub : p.toSubgraph.neighborSet w ⊆ {v} := by
    intro u hu
    exact (h w u (p.toSubgraph.adj_sub hu)).resolve_left hwv
  have hh := Set.ncard_le_ncard hsub
  have hh2 := hp.ncard_neighborSet_toSubgraph_eq_two hw
  simp only [Set.ncard_singleton] at hh
  omega

lemma incidence_complement_acyclic (G : SimpleGraph V) (v : V) :
    (G \ G.deleteIncidenceSet v).IsAcyclic := by
  apply acyclic_of_all_edges_at _ v
  intro a b hab
  by_contra hn
  push_neg at hn
  exact hab.2 (deleteIncidenceSet_adj.mpr ⟨hab.1,hn.1,hn.2⟩)
end Erdos184.ForestMixedCompletion
