import Submission.OneVertexCycles
import Submission.Projection

/-! Gateway-edge constraints on cycle packings. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma cycle_piece_edge_card_le_support {V : Type*} [Fintype V]
    {G A : SimpleGraph V} (H : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2)
    (hHA : H.edgeSet ⊆ A.edgeSet) : H.edgeSet.ncard ≤ A.support.ncard := by
  rw [regular_two_edge_vertex_card H hr]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro v hv
  have hp : 0 < H.coe.degree ⟨v, hv⟩ := by
    have hh := hr ⟨v, hv⟩
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
    omega
  obtain ⟨w, hw⟩ := (H.coe.degree_pos_iff_exists_adj ⟨v, hv⟩).mp hp
  exact ⟨w.val, hHA (show s(v, w.val) ∈ H.edgeSet from hw)⟩

/-- If deleting one edge exposes a small side attached at a single vertex,
any cycle too long to fit on that side must use the deleted edge whenever
it uses an edge of that side. -/
lemma long_cycle_meeting_side_uses_gateway {V : Type*} [Fintype V]
    {G A B : SimpleGraph V} (e : Sym2 V)
    (hcover : A.edgeSet ∪ B.edgeSet = (G.deleteEdges {e}).edgeSet)
    (hdis : Disjoint A.edgeSet B.edgeSet)
    (hover : (A.support ∩ B.support).ncard ≤ 1)
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (hlong : A.support.ncard < H.edgeSet.ncard)
    (hmeet : ¬Disjoint H.edgeSet A.edgeSet) : e ∈ H.edgeSet := by
  by_contra he
  let J : (G.deleteEdges {e}).Subgraph := {
    verts := H.verts
    Adj := H.Adj
    adj_sub := fun {u v} h => SimpleGraph.deleteEdges_adj.mpr ⟨H.adj_sub h, by
      intro hh
      have hh' : s(u,v) = e := Set.mem_singleton_iff.mp hh
      exact he (hh' ▸ (show s(u,v) ∈ H.edgeSet from h))⟩
    edge_vert := H.edge_vert
    symm := H.symm }
  have hJ := cycle_contained_in_one_vertex_separation hcover hover J hc (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hr v)
  rcases hJ with hJA | hJB
  · have hh := cycle_piece_edge_card_le_support H hr hJA
    omega
  · obtain ⟨f, hfH, hfA⟩ := Set.not_disjoint_iff.mp hmeet
    exact Set.disjoint_left.mp hdis hfA (hJB hfH)

lemma regular_two_spanning_degree_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} (H : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) (v : V) :
    H.spanningCoe.degree v ≤ 2 := by
  rw [Subgraph.degree_spanningCoe]
  by_cases hv : v ∈ H.verts
  · have hh := hr ⟨v, hv⟩
    rw [Subgraph.coe_degree] at hh
    simpa only [Subgraph.degree, ← Nat.card_eq_fintype_card] using hh.le
  · rw [Subgraph.degree_of_notMem_verts hv]
    omega

lemma degree_sup_le_sum {V : Type*} [Fintype V] (A B : SimpleGraph V) (v : V) :
    (A ⊔ B).degree v ≤ A.degree v + B.degree v := by
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  exact Set.ncard_union_le (A.neighborSet v) (B.neighborSet v)

/-- A packing of cycles too long for the small side removes at most two
of that side's incident edges at any vertex: at most one packed cycle can
use its gateway. -/
lemma gateway_packing_degree_lower {V : Type*} [Fintype V]
    {G A B : SimpleGraph V} (hAG : A ≤ G) (e : Sym2 V)
    (hcover : A.edgeSet ∪ B.edgeSet = (G.deleteEdges {e}).edgeSet)
    (hdis : Disjoint A.edgeSet B.edgeSet)
    (hover : (A.support ∩ B.support).ncard ≤ 1)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hlong : ∀ H ∈ D, A.support.ncard < H.edgeSet.ncard) (v : V) :
    A.degree v ≤ (G \ unionPieces G D).degree v + 2 := by
  let R := G \ unionPieces G D
  by_cases hhit : ∃ H ∈ D, ¬Disjoint H.edgeSet A.edgeSet
  · obtain ⟨H, hH, hHA⟩ := hhit
    have heH := long_cycle_meeting_side_uses_gateway e hcover hdis hover H
      (hc H hH).1 (hc H hH).2 (hlong H hH) hHA
    have hle : A ≤ R ⊔ H.spanningCoe := by
      intro x y hxy
      by_cases heU : s(x,y) ∈ (unionPieces G D).edgeSet
      · rw [unionPieces_edgeSet] at heU
        simp only [Set.mem_iUnion] at heU
        obtain ⟨K, hK, heK⟩ := heU
        have hKA : ¬Disjoint K.edgeSet A.edgeSet :=
          Set.not_disjoint_iff.mpr ⟨s(x,y), heK, hxy⟩
        have heK' := long_cycle_meeting_side_uses_gateway e hcover hdis hover K
          (hc K hK).1 (hc K hK).2 (hlong K hK) hKA
        have hKH : K = H := by
          by_contra hne
          exact Set.disjoint_left.mp (hd hK hH hne) heK' heH
        subst K
        exact Or.inr heK
      · left
        change s(x,y) ∈ (G \ unionPieces G D).edgeSet
        rw [SimpleGraph.edgeSet_sdiff]
        exact ⟨hAG hxy, heU⟩
    have h₁ : A.degree v ≤ (R ⊔ H.spanningCoe).degree v := SimpleGraph.degree_le_of_le hle
    have h₂ := degree_sup_le_sum R H.spanningCoe v
    have h₃ := regular_two_spanning_degree_le H (hc H hH).2 v
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h₁ h₂ h₃ ⊢
    change Nat.card (A.neighborSet v) ≤ Nat.card (R.neighborSet v) + 2
    omega
  · have hle : A ≤ R := by
      intro x y hxy
      change s(x,y) ∈ (G \ unionPieces G D).edgeSet
      rw [SimpleGraph.edgeSet_sdiff]
      refine ⟨hAG hxy, ?_⟩
      intro hh
      rw [unionPieces_edgeSet] at hh
      simp only [Set.mem_iUnion] at hh
      obtain ⟨H, hH, heH⟩ := hh
      exact hhit ⟨H, hH, Set.not_disjoint_iff.mpr ⟨s(x,y), heH, hxy⟩⟩
    have hh : A.degree v ≤ R.degree v := SimpleGraph.degree_le_of_le hle
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
    exact hh.trans (Nat.le_add_right _ _)

end Erdos184
