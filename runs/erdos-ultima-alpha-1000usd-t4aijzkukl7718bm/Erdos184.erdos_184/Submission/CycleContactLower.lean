import Submission.MaximumCoreFamilies
import Submission.GraphVertexSeparation

/-! A cycle attached to the rest of a family at at most one vertex contributes
one additively to the optimum. In a family of at least three cycles with
optimum at most two, every displayed cycle therefore has at least two contacts.
This is a local necessary condition, not a general decomposition bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleContactLower
open Critical EvenCore Rigidity MaximumCycles MaximumCoreFamilies GraphVertexSeparation
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Union of the displayed vertex sets (not merely the edge supports). -/
def vertexUnion (D : Finset G.Subgraph) : Set V := ⋃ H ∈ D, H.verts

lemma support_subset_vertexUnion (D : Finset G.Subgraph) :
    (subfamilyGraph D).support ⊆ vertexUnion D := by
  rintro x ⟨y,hxy⟩
  have he : s(x,y) ∈ (subfamilyGraph D).edgeSet := hxy
  rw [subfamilyGraph_edges] at he
  obtain ⟨H,hH⟩ := Set.mem_iUnion.mp he
  obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp hH
  exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hHD,H.edge_vert heH⟩⟩

lemma number_ge_two_of_two_pieces (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hc : 2 ≤ D.card) : 2 ≤ number (subfamilyGraph D) := by
  by_contra hn
  have he : ∀ x, Even ((subfamilyGraph D).degree x) := cycle_subfamily_even D hD hd
  have hr := rigid_of_number_le_one he (by omega)
  obtain ⟨E,hE,hdE,hcE⟩ := subfamily_decomposition D hD hd
  have hnum := hr E hE hdE
  omega

lemma leaf_piece_number (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (H : G.Subgraph) (hH : H ∈ D)
    (hcontact : (H.verts ∩ vertexUnion (D.erase H)).ncard ≤ 1) :
    number (subfamilyGraph D) = 1 + number (subfamilyGraph (D.erase H)) := by
  obtain ⟨x⟩ := (hD H hH).1.nonempty
  letI : Nonempty V := ⟨x.val⟩
  obtain ⟨v,hv⟩ := (Set.ncard_le_one_iff_subset_singleton (Set.toFinite _)).mp hcontact
  have ht : TouchAt H.spanningCoe (subfamilyGraph (D.erase H)) v := by
    intro z hzH hzR
    have hz : z ∈ H.verts ∩ vertexUnion (D.erase H) := by
      obtain ⟨w,hzw⟩ := hzH
      exact ⟨H.edge_vert hzw,support_subset_vertexUnion _ hzR⟩
    exact Set.mem_singleton_iff.mp (hv hz)
  have hAe : ∀ z, Even (H.spanningCoe.degree z) := regular_two_spanning_even H (hD H hH).2
  have hRe : ∀ z, Even ((subfamilyGraph (D.erase H)).degree z) :=
    cycle_subfamily_even (D.erase H) (fun K hK => hD K (Finset.mem_of_mem_erase hK))
      (fun K hK L hL hne => hd (Finset.mem_of_mem_erase hK) (Finset.mem_of_mem_erase hL) hne)
  have hsum := number_sup ht hAe hRe
  have hg : subfamilyGraph D = H.spanningCoe ⊔ subfamilyGraph (D.erase H) := by
    conv_lhs => rw [← Finset.insert_erase hH]
    simp only [subfamilyGraph,Finset.sup_insert]
  rw [hg,hsum,GraphCircuitCode.cycle_number_one H (hD H hH)]

lemma two_contacts_of_number_le_two (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hc : 3 ≤ D.card) (hn : number (subfamilyGraph D) ≤ 2)
    (H : G.Subgraph) (hH : H ∈ D) :
    2 ≤ (H.verts ∩ vertexUnion (D.erase H)).ncard := by
  by_contra h
  have hh := leaf_piece_number D hD hd H hH (by omega)
  have hcE : 2 ≤ (D.erase H).card := by
    have hcard := Finset.card_erase_add_one hH
    omega
  have hge := number_ge_two_of_two_pieces (D.erase H)
    (fun K hK => hD K (Finset.mem_of_mem_erase hK))
    (fun K hK L hL hne => hd (Finset.mem_of_mem_erase hK) (Finset.mem_of_mem_erase hL) hne) hcE
  omega

#print axioms leaf_piece_number
#print axioms two_contacts_of_number_le_two
end Erdos184Work.CycleContactLower
