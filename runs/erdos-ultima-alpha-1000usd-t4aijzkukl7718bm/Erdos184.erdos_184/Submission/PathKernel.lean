import Submission.PathSubstitutionProjection

/-! The finite labelled kernel of a path substitution. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.PathSubstitution.Family
open PathSeries MaximumCycles
set_option maxHeartbeats 2000000
variable {V W J : Type*} [Fintype V] [Fintype J] {G : SimpleGraph V} (F : Family J W G)

lemma path_subgraph_injective : Function.Injective (fun j => (F.path j).toSubgraph) := by
  intro i j he
  dsimp only at he
  by_contra hij
  have hn : ¬ (F.path i).Nil := Walk.not_nil_of_ne (fun h => F.ne i (F.injective h))
  have hm : s(F.vertex (F.src i),(F.path i).snd) ∈ (F.path i).toSubgraph.edgeSet :=
    (F.path i).toSubgraph_adj_snd hn
  have hm' : s(F.vertex (F.src i),(F.path i).snd) ∈ (F.path j).toSubgraph.edgeSet := by rw [← he]; exact hm
  exact List.disjoint_left.mp (F.edge_disjoint i j hij)
    ((F.path i).mem_edges_toSubgraph.mp hm) ((F.path j).mem_edges_toSubgraph.mp hm')

noncomputable def pieces (s : Finset J) : Finset G.Subgraph := s.image (fun j => (F.path j).toSubgraph)
noncomputable def expandGraph (s : Finset J) : SimpleGraph V := subfamilyGraph (F.pieces s)
noncomputable def expandEdges (s : Finset J) : Finset (Sym2 V) := s.biUnion (fun j => (F.path j).edges.toFinset)

lemma pieces_disjoint (s : Finset J) :
    Set.PairwiseDisjoint (F.pieces s : Set G.Subgraph) (fun H => H.edgeSet) := by
  intro H hH K hK hne
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hH
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hK
  apply Set.disjoint_left.mpr
  intro e he hf
  exact List.disjoint_left.mp (F.edge_disjoint i j (fun he => hne (congrArg (fun j => (F.path j).toSubgraph) he)))
    ((F.path i).mem_edges_toSubgraph.mp he) ((F.path j).mem_edges_toSubgraph.mp hf)

lemma mem_expandGraph (s : Finset J) (e : Sym2 V) :
    e ∈ (F.expandGraph s).edgeSet ↔ ∃ j ∈ s, e ∈ (F.path j).edges := by
  rw [expandGraph,subfamilyGraph_edges]
  simp only [Set.mem_iUnion,exists_prop,pieces,Finset.mem_image]
  constructor
  · rintro ⟨H,⟨j,hj,rfl⟩,he⟩
    exact ⟨j,hj,(F.path j).mem_edges_toSubgraph.mp he⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨(F.path j).toSubgraph,⟨j,hj,rfl⟩,(F.path j).mem_edges_toSubgraph.mpr he⟩

lemma expandGraph_edgeFinset (s : Finset J) : (F.expandGraph s).edgeFinset = F.expandEdges s := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset,expandEdges,Finset.mem_biUnion,List.mem_toFinset]
  exact F.mem_expandGraph s e

lemma expandGraph_le (s : Finset J) : F.expandGraph s ≤ G := subfamilyGraph_le _

lemma expandGraph_degree (s : Finset J) (x : V) :
    (F.expandGraph s).degree x = ∑ j ∈ s, (F.path j).toSubgraph.spanningCoe.degree x := by
  rw [expandGraph,subfamilyGraph_degree _ (F.pieces_disjoint s)]
  exact Finset.sum_image (fun _ _ _ _ h => F.path_subgraph_injective h)

lemma path_degree_vertex (j : J) (w : W) :
    (F.path j).toSubgraph.spanningCoe.degree (F.vertex w) =
      if F.src j = w ∨ F.dst j = w then 1 else 0 := by
  have hn : ¬ (F.path j).Nil := Walk.not_nil_of_ne (fun h => F.ne j (F.injective h))
  by_cases hw : F.src j = w ∨ F.dst j = w
  · rw [if_pos hw]
    rcases hw with rfl | rfl
    · exact path_start_degree (F.path j) (F.isPath j) hn
    · rw [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      change ((F.path j).toSubgraph.neighborSet (F.vertex (F.dst j))).ncard = 1
      rw [(F.isPath j).neighborSet_toSubgraph_endpoint hn]
      simp
  · rw [if_neg hw,SimpleGraph.degree_eq_zero_iff_notMem_support]
    rintro ⟨y,hxy⟩
    have hmem := (F.path j).mem_verts_toSubgraph.mp ((F.path j).toSubgraph.edge_vert hxy)
    exact hw (((F.vertex_mem j w).mp hmem).imp Eq.symm Eq.symm)

lemma expandGraph_degree_vertex (s : Finset J) (w : W) :
    (F.expandGraph s).degree (F.vertex w) =
      (s.filter (fun j => F.src j = w ∨ F.dst j = w)).card := by
  rw [F.expandGraph_degree]
  simp_rw [F.path_degree_vertex]
  simp

def validLabels (s : Finset J) : Prop :=
  ∀ w, Even ((s.filter (fun j => F.src j = w ∨ F.dst j = w)).card)

lemma expandGraph_even_iff (s : Finset J) :
    (∀ x, Even ((F.expandGraph s).degree x)) ↔ F.validLabels s := by
  constructor
  · intro he w
    rw [← F.expandGraph_degree_vertex]
    exact he (F.vertex w)
  · intro hs x
    by_cases hx : ∃ w, F.vertex w = x
    · obtain ⟨w,rfl⟩ := hx
      rw [F.expandGraph_degree_vertex]
      exact hs w
    · rw [F.expandGraph_degree]
      apply Finset.even_sum
      intro j hj
      exact path_internal_even (F.path j) (F.isPath j) x
        (fun h => hx ⟨F.src j,h.symm⟩) (fun h => hx ⟨F.dst j,h.symm⟩)

lemma selectedLabels_expandGraph (s : Finset J) : F.selectedLabels (F.expandGraph s) = s := by
  ext j
  rw [F.mem_selectedLabels]
  constructor
  · intro h
    have hn : ¬ (F.path j).Nil := Walk.not_nil_of_ne (fun h => F.ne j (F.injective h))
    have he : s(F.vertex (F.src j),(F.path j).snd) ∈ (F.path j).edges :=
      (F.path j).mem_edges_toSubgraph.mp ((F.path j).toSubgraph_adj_snd hn)
    obtain ⟨i,hi,hei⟩ := (F.mem_expandGraph s _).mp (h _ he)
    by_cases hij : j = i
    · exact hij ▸ hi
    · exact (List.disjoint_left.mp (F.edge_disjoint j i hij) he hei).elim
  · intro hj e he
    exact (F.mem_expandGraph s e).mpr ⟨j,hj,he⟩

lemma expandGraph_selectedLabels
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (R : SimpleGraph V) (hRG : R ≤ G) (he : ∀ x, Even (R.degree x)) :
    F.expandGraph (F.selectedLabels R) = R := by
  apply SimpleGraph.edgeSet_injective
  ext e
  rw [F.mem_expandGraph,F.even_subgraph_edges_iff hcover R hRG he]

lemma expandGraph_injective : Function.Injective F.expandGraph := by
  intro s t h
  have he := congrArg F.selectedLabels h
  simpa only [F.selectedLabels_expandGraph] using he

#print axioms expandGraph_selectedLabels
#print axioms expandGraph_even_iff
end Erdos184Work.PathSubstitution.Family
