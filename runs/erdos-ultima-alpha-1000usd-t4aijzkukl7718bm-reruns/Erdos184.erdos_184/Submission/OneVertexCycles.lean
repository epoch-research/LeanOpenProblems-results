import Submission.Blocks

/-! Cycle containment under one-vertex separations. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma even_subgraph_of_connected_regular_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hc : G.Connected) (hr : G.IsRegularOfDegree 2)
    (A : SimpleGraph V) (hAG : A ≤ G) (he : ∀ v, Even (A.degree v)) :
    A = ⊥ ∨ A = G := by
  by_cases hb : A = ⊥
  · exact Or.inl hb
  have hsat : ∀ u ∈ A.support, A.neighborSet u = G.neighborSet u := by
    intro u hu
    have hpos := (A.degree_pos_iff_mem_support u).mpr hu
    have hle : A.degree u ≤ G.degree u := SimpleGraph.degree_le_of_le hAG
    have heven := he u
    have hreg := hr u
    have hdeg : A.degree u = 2 := by
      obtain ⟨k, hk⟩ := heven
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hpos hle hreg hk ⊢
      omega
    apply Set.eq_of_subset_of_ncard_le (fun _ h => hAG h)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] at hdeg hreg
    change (G.neighborSet u).ncard ≤ (A.neighborSet u).ncard
    rw [hdeg, hreg]
  have hprop : ∀ {u v} (p : G.Walk u v), u ∈ A.support → v ∈ A.support := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
      intro hu
      have huvA : A.Adj u v := by
        change v ∈ A.neighborSet u
        rw [hsat u hu]
        exact huv
      exact ih ⟨u, huvA.symm⟩
  have hex : ∃ u v, A.Adj u v := by
    by_contra! hn
    exact hb (SimpleGraph.eq_bot_iff_forall_not_adj.mpr hn)
  obtain ⟨u, v, huv⟩ := hex
  have hall : ∀ w, w ∈ A.support := by
    intro w
    obtain ⟨p⟩ := hc u w
    exact hprop p ⟨v, huv⟩
  right
  ext x y
  exact Set.ext_iff.mp (hsat x (hall x)) y

/-- A cycle piece cannot cross an edge separation whose two sides have at
most one nonisolated vertex in common. -/
lemma cycle_contained_in_one_vertex_separation {V : Type*} [Fintype V]
    {G A B : SimpleGraph V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hover : (A.support ∩ B.support).ncard ≤ 1)
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    H.edgeSet ⊆ A.edgeSet ∨ H.edgeSet ⊆ B.edgeSet := by
  let X : SimpleGraph H.verts := H.coe ⊓ A.comap Subtype.val
  let Y : SimpleGraph H.verts := H.coe ⊓ B.comap Subtype.val
  have hXY : X.edgeSet ∪ Y.edgeSet = H.coe.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | h u v =>
      change (H.Adj u.val v.val ∧ A.Adj u.val v.val) ∨
        (H.Adj u.val v.val ∧ B.Adj u.val v.val) ↔ H.Adj u.val v.val
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        have hh : s(u.val, v.val) ∈ A.edgeSet ∪ B.edgeSet :=
          hcover.symm ▸ (show s(u.val, v.val) ∈ G.edgeSet from H.adj_sub h)
        rcases hh with ha | hb
        · exact Or.inl ⟨h, ha⟩
        · exact Or.inr ⟨h, hb⟩
  have hoverXY : (X.support ∩ Y.support).ncard ≤ 1 := by
    apply Set.ncard_le_one_iff_subsingleton.mpr
    have hsub := Set.ncard_le_one_iff_subsingleton.mp hover
    intro u hu v hv
    apply Subtype.ext
    apply hsub
    · obtain ⟨x, hx⟩ := hu.1
      obtain ⟨y, hy⟩ := hu.2
      exact ⟨⟨x.val, hx.2⟩, ⟨y.val, hy.2⟩⟩
    · obtain ⟨x, hx⟩ := hv.1
      obtain ⟨y, hy⟩ := hv.2
      exact ⟨⟨x.val, hx.2⟩, ⟨y.val, hy.2⟩⟩
  have he : ∀ v, Even (H.coe.degree v) := by intro v; rw [hr v]; decide
  have heX := even_left_of_one_vertex_separation (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using he)
    hXY hoverXY
  have hX := even_subgraph_of_connected_regular_two H.coe hc (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hr v) X inf_le_left (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heX)
  rcases hX with hbot | hfull
  · right
    intro e heH
    induction e using Sym2.ind with
    | h u v =>
      have hu := H.edge_vert heH
      have hv := H.edge_vert (H.symm heH)
      have hH : H.coe.Adj ⟨u, hu⟩ ⟨v, hv⟩ := heH
      have hAB : s(u,v) ∈ A.edgeSet ∪ B.edgeSet :=
        hcover.symm ▸ (show s(u,v) ∈ G.edgeSet from H.adj_sub heH)
      rcases hAB with hA | hB
      · have hXA : X.Adj ⟨u, hu⟩ ⟨v, hv⟩ := ⟨hH, hA⟩
        simp [hbot] at hXA
      · exact hB
  · left
    intro e heH
    induction e using Sym2.ind with
    | h u v =>
      have hu := H.edge_vert heH
      have hv := H.edge_vert (H.symm heH)
      have hH : H.coe.Adj ⟨u, hu⟩ ⟨v, hv⟩ := heH
      have hXA : X.Adj ⟨u, hu⟩ ⟨v, hv⟩ := hfull.symm ▸ hH
      exact hXA.2

lemma cycle_length_bound_one_vertex_union {V : Type*} [Fintype V]
    {G A B : SimpleGraph V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hover : (A.support ∩ B.support).ncard ≤ 1) (k : ℕ)
    (hA : ∀ u (p : A.Walk u u), p.IsCycle → p.length ≤ k)
    (hB : ∀ u (p : B.Walk u u), p.IsCycle → p.length ≤ k) :
    ∀ u (p : G.Walk u u), p.IsCycle → p.length ≤ k := by
  intro u p hp
  have hh := cycle_subgraph_regular G hp
  have hc := cycle_contained_in_one_vertex_separation hcover hover p.toSubgraph hh.1 (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v)
  rcases hc with hcA | hcB
  · have htrans : ∀ e ∈ p.edges, e ∈ A.edgeSet :=
      fun _ he => hcA (p.mem_edges_toSubgraph.mpr he)
    have hb := hA u (p.transfer A htrans) (hp.transfer htrans)
    simpa only [Walk.length_transfer] using hb
  · have htrans : ∀ e ∈ p.edges, e ∈ B.edgeSet :=
      fun _ he => hcB (p.mem_edges_toSubgraph.mpr he)
    have hb := hB u (p.transfer B htrans) (hp.transfer htrans)
    simpa only [Walk.length_transfer] using hb

end Erdos184
