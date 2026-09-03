import Submission.AdaptiveFourRouting

/-!
Restricting cycle packings to a subfamily and transferring a packing whose
edges lie in a different ambient graph. These operations preserve exact edge
coverage and do not assert any new decomposition bound.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TerminalRouting
variable {V : Type*} [Fintype V] {G K : SimpleGraph V}
set_option maxHeartbeats 800000

noncomputable def Packing.restrict (P : Packing K) (S : Finset K.Subgraph) (hS : S ⊆ P.pieces) :
    Packing K where
  pieces := S
  cycles H hH := P.cycles H (hS hH)
  disjoint _ hH _ hL hne := P.disjoint (hS hH) (hS hL) hne

noncomputable def Packing.remove (P : Packing K) (S : Finset K.Subgraph) : Packing K :=
  P.restrict (P.pieces \ S) Finset.sdiff_subset

lemma Packing.remove_card (P : Packing K) (S : Finset K.Subgraph) (hS : S ⊆ P.pieces) :
    (P.remove S).pieces.card + S.card = P.pieces.card := by
  exact Finset.card_sdiff_add_card_eq_card hS

lemma Packing.remove_disjoint (P : Packing K) (S : Finset K.Subgraph) (hS : S ⊆ P.pieces) :
    Disjoint (P.remove S).edges (P.restrict S hS).edges := by
  apply Set.disjoint_left.mpr
  intro e he hf
  obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
  obtain ⟨L,hL,heL⟩ := Set.mem_iUnion₂.mp hf
  have hh : H ∈ P.pieces ∧ H ∉ S := Finset.mem_sdiff.mp hH
  have hl : L ∈ S := hL
  exact Set.disjoint_left.mp (P.disjoint hh.1 (hS hl) (fun h => hh.2 (h ▸ hl))) heH heL

lemma Packing.remove_cover (P : Packing K) (S : Finset K.Subgraph) (hS : S ⊆ P.pieces) :
    (P.remove S).edges ∪ (P.restrict S hS).edges = P.edges := by
  ext e
  simp only [Packing.edges,Packing.remove,Packing.restrict,Set.mem_union,Set.mem_iUnion,
    Finset.mem_sdiff]
  constructor
  · rintro (⟨H,⟨hH,_⟩,he⟩ | ⟨H,hH,he⟩)
    · exact ⟨H,hH,he⟩
    · exact ⟨H,hS hH,he⟩
  · rintro ⟨H,hH,he⟩
    by_cases hs : H ∈ S
    · exact Or.inr ⟨H,hs,he⟩
    · exact Or.inl ⟨H,⟨hH,hs⟩,he⟩

lemma Packing.remove_edges (P : Packing K) (S : Finset K.Subgraph) (hS : S ⊆ P.pieces) :
    (P.remove S).edges = P.edges \ (P.restrict S hS).edges := by
  have hcov := P.remove_cover S hS
  have hdis := Set.disjoint_left.mp (P.remove_disjoint S hS)
  ext e
  have hh := Set.ext_iff.mp hcov e
  simp only [Set.mem_union,Set.mem_diff] at hh ⊢
  constructor
  · intro h
    exact ⟨hh.mp (Or.inl h),hdis h⟩
  · rintro ⟨h,hn⟩
    exact (hh.mpr h).resolve_right hn

/-- Transfer on a subfamily. No graph homomorphism on the entire ambient
vertex set is required, since unused ambient edges may be absent in G. -/
lemma Packing.transfer (P : Packing K) (hPG : P.edges ⊆ G.edgeSet) :
    ∃ Q : Packing G, Q.edges = P.edges ∧ Q.pieces.card ≤ P.pieces.card := by
  let J (H : {H // H ∈ P.pieces}) : G.Subgraph := {
    verts := H.val.verts
    Adj := H.val.Adj
    adj_sub := fun {u v} h => show s(u,v) ∈ G.edgeSet from
      hPG (P.piece_edges_subset H.property (show s(u,v) ∈ H.val.edgeSet from h))
    edge_vert := H.val.edge_vert
    symm := H.val.symm }
  let E := Finset.univ.image J
  have hc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hH
    refine ⟨(P.cycles L.val L.property).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (P.cycles L.val L.property).2 x
  have hd : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH L hL hne
    obtain ⟨X,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨Y,_,rfl⟩ := Finset.mem_image.mp hL
    apply P.disjoint X.property Y.property
    intro h
    exact hne (congrArg J (Subtype.ext h))
  refine ⟨⟨E,hc,hd⟩,?_,?_⟩
  · ext e
    simp only [Packing.edges,Set.mem_iUnion]
    constructor
    · rintro ⟨H,hH,heH⟩
      obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hH
      exact ⟨L.val,L.property,heH⟩
    · rintro ⟨H,hH,heH⟩
      let L : {H // H ∈ P.pieces} := ⟨H,hH⟩
      exact ⟨J L,Finset.mem_image.mpr ⟨L,Finset.mem_univ _,rfl⟩,heH⟩
  · exact Finset.card_image_le.trans_eq (by rw [Finset.card_univ,Fintype.card_coe])

end Erdos184.TerminalRouting
