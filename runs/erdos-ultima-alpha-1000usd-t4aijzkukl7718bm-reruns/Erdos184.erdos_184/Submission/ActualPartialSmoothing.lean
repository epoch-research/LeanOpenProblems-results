import Submission.PartialSmoothing

/-! The partial-smoothing obstruction stated directly for an actual graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.PartialSmoothing
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

/-- Remove precisely the two spokes that are to be smoothed. -/
def removeSpokes (G : SimpleGraph V) (v a b : V) : SimpleGraph V :=
  G.deleteEdges {s(v,a),s(v,b)}

omit [Fintype V] in
lemma removeSpokes_left (G : SimpleGraph V) (v a b : V) :
    ¬(removeSpokes G v a b).Adj v a := by
  simp [removeSpokes]

omit [Fintype V] in
lemma removeSpokes_right (G : SimpleGraph V) (v a b : V) :
    ¬(removeSpokes G v a b).Adj v b := by
  simp [removeSpokes]

omit [Fintype V] in
lemma removeSpokes_pair (G : SimpleGraph V) {v a b : V} (hab : ¬G.Adj a b) :
    ¬(removeSpokes G v a b).Adj a b := by
  simp [removeSpokes,hab]

omit [Fintype V] in
lemma unsmooth_removeSpokes (G : SimpleGraph V) {v a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) :
    unsmooth (removeSpokes G v a b) v a b = G := by
  apply SimpleGraph.edgeSet_injective
  rw [unsmooth_edges _ ha.ne hb.ne]
  simp only [removeSpokes,edgeSet_deleteEdges]
  ext e
  have h₁ : e = s(v,a) → e ∈ G.edgeSet := by rintro rfl; exact ha
  have h₂ : e = s(v,b) → e ∈ G.edgeSet := by rintro rfl; exact hb
  simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff]
  tauto

/-- The genuine partial smoothing is even, has one fewer edge, and has a
bounded decomposition in which every marked piece must meet the apex. -/
lemma actual_lex_minimal_obstruction (C : ℕ) (G : SimpleGraph V)
    (hG : GlobalVertexMinimal.IsLexMinimal C G) {v a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) (hn : ¬G.Adj a b) :
    let S := smooth (removeSpokes G v a b) a b
    (∀ x, Even (S.degree x)) ∧ S.edgeSet.ncard + 1 = G.edgeSet.ncard ∧
    ∃ D : Finset S.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition S D ∧ D.card ≤ C * Fintype.card V ∧
      ∀ H ∈ D, H.Adj a b → v ∈ H.verts := by
  dsimp only
  let A := removeSpokes G v a b
  have heq : unsmooth A v a b = G := unsmooth_removeSpokes G ha hb
  have hA : GlobalVertexMinimal.IsLexMinimal C (unsmooth A v a b) := by rwa [heq]
  have hna := removeSpokes_left G v a b
  have hnb := removeSpokes_right G v a b
  have hnab := removeSpokes_pair (v := v) G hn
  refine ⟨?_,?_,lex_minimal_smoothing_obstruction C A ha.ne hb.ne hab hna hnb hnab hA⟩
  · exact smooth_even A ha.ne hb.ne hab hna hnb hnab hA.1.1
  · have hh := edge_card_relation A ha.ne hb.ne hab hna hnb hnab
    rwa [heq] at hh

/-- A path outside the apex gives a cycle using the new edge and avoiding the
apex. No optimal-extension assertion is made for this cycle. -/
lemma avoiding_cycle_of_connected_without (G : SimpleGraph V) {v a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) (hn : ¬G.Adj a b)
    (hconn : (G.induce {x | x ≠ v}).Connected) :
    ∃ H : (smooth (removeSpokes G v a b) a b).Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ H.Adj a b ∧ v ∉ H.verts := by
  let S := smooth (removeSpokes G v a b) a b
  let f : (G.induce {x | x ≠ v}) →g S :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        apply Or.inl
        apply (deleteEdges_adj ..).mpr
        refine ⟨hxy,?_⟩
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
        rintro (h | h) <;> rcases Sym2.eq_iff.mp h with h | h
        · exact x.property h.1
        · exact y.property h.2
        · exact x.property h.1
        · exact y.property h.2 }
  obtain ⟨p,hp⟩ := (hconn.preconnected ⟨b,hb.ne.symm⟩ ⟨a,ha.ne.symm⟩).exists_isPath
  let q := p.map f
  have hq : q.IsPath := Walk.map_isPath_of_injective Subtype.val_injective hp
  have hqv : v ∉ q.support := by
    simp only [q,Walk.support_map,List.mem_map,not_exists,not_and]
    intro x _ hx
    exact x.property hx
  have hadj : S.Adj a b := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab⟩)
  have he : s(a,b) ∉ q.edges := by
    intro he
    have hg := q.edges_subset_edgeSet he
    -- Every mapped path edge still comes from the original induced graph.
    have hg' : s(a,b) ∈ (p.map ((SimpleGraph.Embedding.induce {x | x ≠ v}).toHom)).edges := by
      simpa only [q,Walk.edges_map] using he
    exact hn ((p.map ((SimpleGraph.Embedding.induce {x | x ≠ v}).toHom)).edges_subset_edgeSet hg')
  let c := q.cons hadj
  have hc : c.IsCycle := (Walk.cons_isCycle_iff q hadj).mpr ⟨hq,he⟩
  refine ⟨c.toSubgraph,cycle_subgraph_regular S hc,?_,?_⟩
  · apply Walk.adj_toSubgraph_iff_mem_edges.mpr
    simp only [c,Walk.edges_cons,List.mem_cons,true_or]
  · simpa only [Walk.mem_verts_toSubgraph,c,Walk.support_cons,List.mem_cons,not_or]
      using And.intro ha.ne hqv

/-- When deletion of the apex is connected, partial smoothing of a lex-minimal
counterexample necessarily destroys the all-cycles-optimal property. -/
lemma actual_smoothing_not_all_optimal (C : ℕ) (G : SimpleGraph V)
    (hG : GlobalVertexMinimal.IsLexMinimal C G) {v a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) (hn : ¬G.Adj a b)
    (hconn : (G.induce {x | x ≠ v}).Connected) :
    ¬MinimalCounterexample.AllCyclesOptimal (smooth (removeSpokes G v a b) a b) := by
  intro hopt
  obtain ⟨_,_,D,hcD,hdD,hbD,_⟩ := actual_lex_minimal_obstruction C G hG ha hb hab hn
  obtain ⟨H,hcH,heH,hvH⟩ := avoiding_cycle_of_connected_without G ha hb hab hn hconn
  obtain ⟨E,hcE,hdE,hHE,hminE⟩ := hopt H hcH
  have hbE := (hminE D hcD hdD).trans hbD
  have hbad : ¬ExactVertexSmoothing.HasPieceBound (C * Fintype.card V)
      (unsmooth (removeSpokes G v a b) v a b) := by
    rw [unsmooth_removeSpokes G ha hb]
    exact hG.1.2.1
  exact hvH (marked_piece_must_meet_apex _ _ ha.ne hb.ne hab
    (removeSpokes_left G v a b) (removeSpokes_right G v a b)
    (removeSpokes_pair G hn) hbad E hcE hdE hbE H hHE heH)

end Erdos184.PartialSmoothing
