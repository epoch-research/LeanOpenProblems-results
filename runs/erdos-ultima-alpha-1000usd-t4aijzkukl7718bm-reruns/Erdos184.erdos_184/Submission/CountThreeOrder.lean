import Submission.NoTwoCyclesEdges

/-! A finite order reduction for the degree-two-free count-three critical case.
This does not provide a uniform bound for arbitrary critical counts. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CountThreeOrder
open CountCritical HighGirthCritical EvenCycleCore
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma edge_delete_set_le (G : SimpleGraph V) (S : Set V) :
    G.edgeSet.ncard ≤ (avoid G S).edgeSet.ncard + ∑ v ∈ S.toFinset, G.degree v := by
  have hsub : G.edgeFinset ⊆ (avoid G S).edgeFinset ∪ S.toFinset.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have hxy : G.Adj x y := G.mem_edgeFinset.mp he
      by_cases hx : x ∈ S
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨x,Set.mem_toFinset.mpr hx,by simpa using hxy⟩
      by_cases hy : y ∈ S
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨y,Set.mem_toFinset.mpr hy,by
          rw [mem_incidenceFinset,mk'_mem_incidenceSet_right_iff]
          exact hxy⟩
      · apply Finset.mem_union_left
        exact (avoid G S).mem_edgeFinset.mpr ⟨hxy,hx,hy⟩
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsum : (S.toFinset.biUnion (fun v => G.incidenceFinset v)).card ≤ ∑ v ∈ S.toFinset, G.degree v := by
    simpa only [card_incidenceFinset_eq_degree] using
      (Finset.card_biUnion_le (s := S.toFinset) (t := fun v => G.incidenceFinset v))
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hle
  omega

lemma cycle_vertex_delete_bound {G : SimpleGraph V} (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hfour : ∀ v ∈ C.verts, G.degree v = 4) :
    G.edgeSet.ncard ≤ (avoid G C.verts).edgeSet.ncard + 3 * C.verts.ncard := by
  let R := G \ C.spanningCoe
  have heq : avoid R C.verts = avoid G C.verts := by
    ext x y
    constructor
    · rintro ⟨h,hx,hy⟩
      exact ⟨h.1,hx,hy⟩
    · rintro ⟨h,hx,hy⟩
      exact ⟨⟨h,fun hh => hx (C.edge_vert hh)⟩,hx,hy⟩
  have hdeg : ∀ v ∈ C.verts, R.degree v = 2 := by
    intro v hv
    have hd := degree_sdiff_of_le C.spanningCoe_le v
    have hC := CriticalNestedCycles.cycle_degree C hc v
    rw [if_pos hv] at hC
    have hG := hfour v hv
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hC hG ⊢
    change Nat.card (R.neighborSet v) = Nat.card (G.neighborSet v) -
      Nat.card (C.spanningCoe.neighborSet v) at hd
    omega
  have hsum : (∑ v ∈ C.verts.toFinset, R.degree v) = 2 * C.verts.ncard := by
    calc
      _ = ∑ _v ∈ C.verts.toFinset, 2 := Finset.sum_congr rfl (fun v hv => hdeg v (Set.mem_toFinset.mp hv))
      _ = _ := by simp only [Finset.sum_const,smul_eq_mul,Set.toFinset_card,← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq,Nat.mul_comm]
  have hb := edge_delete_set_le R C.verts
  rw [heq] at hb
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hsum hb
  rw [hsum] at hb
  have hcard : R.edgeSet.ncard + C.edgeSet.ncard = G.edgeSet.ncard := by
    dsimp only [R]
    rw [edgeSet_sdiff]
    exact Set.ncard_diff_add_ncard_of_subset C.edgeSet_subset
  rw [regular_two_edge_vertex_card C hc.2] at hcard
  omega

lemma four_regular_support_edges {G : SimpleGraph V}
    (hfour : ∀ v ∈ G.support, G.degree v = 4) :
    G.edgeSet.ncard = 2 * G.support.ncard := by
  have hh := G.sum_degrees_support_eq_twice_card_edges
  have hs : (∑ v ∈ G.support.toFinset, G.degree v) = 4 * G.support.ncard := by
    calc
      _ = ∑ _v ∈ G.support.toFinset, 4 := Finset.sum_congr rfl (fun v hv => hfour v (Set.mem_toFinset.mp hv))
      _ = _ := by simp only [Finset.sum_const,smul_eq_mul,Set.toFinset_card,← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq,Nat.mul_comm]
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hs hh
  rw [hs] at hh
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh
  omega

/-- A cycle in a four-regular supported graph, whose outside has no two
edge-disjoint cycles, bounds the total supported order by twice its length plus three. -/
lemma support_bound_from_cycle {G : SimpleGraph V}
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hout : NoTwoCycles (avoid G C.verts)) :
    G.support.ncard ≤ 2 * C.verts.ncard + 3 := by
  have hCsup := CriticalOutsideCycles.cycle_verts_in_support C hc.2
  have hbudget := cycle_vertex_delete_bound C hc (fun v hv => hfour v (hCsup hv))
  have hcount := four_regular_support_edges hfour
  have houtedges := NoTwoCyclesEdges.edge_bound (avoid G C.verts) hout
  have houtsup := Set.ncard_le_ncard (avoid_support_subset G C.verts)
  have hsplit := Set.ncard_diff_add_ncard_of_subset hCsup
  omega

/-- A hypothetical nonempty, degree-two-free critical graph at count at most
three has at most eleven supported vertices. No finite-case exclusion is asserted here. -/
lemma support_le_eleven {G : SimpleGraph V} {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 3) (hne : G ≠ ⊥)
    (hno : ∀ v, G.degree v ≠ 2) : G.support.ncard ≤ 11 := by
  have hfour := LowCountCritical.supported_degree_eq_four_of_count_le_three hG hk hne hno
  obtain ⟨a,p,hp,hg⟩ := exists_shortest_cycle G hne (by
    intro v hv
    rw [hfour v hv]
    omega)
  have hlen : p.length ≤ 4 := by
    by_contra! hn
    obtain ⟨v,hv⟩ := degree_two_of_count_le_three_high_girth hG hk hne (by
      intro v q hq
      have hh := G.girth_le_length hq
      rw [hg] at hh
      omega)
    exact hno v hv
  have hc := cycle_subgraph_regular G hp
  have hout : NoTwoCycles (avoid G p.toSubgraph.verts) :=
    CriticalOutsideCycles.outside_cycles_not_disjoint hG hk hno p.toSubgraph hc
  have hbound := support_bound_from_cycle hfour p.toSubgraph hc hout
  have hcard := trail_spanning_edge_card p hp.isTrail
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hcard
  change p.toSubgraph.edgeSet.ncard = p.length at hcard
  rw [regular_two_edge_vertex_card p.toSubgraph hc.2] at hcard
  omega

end Erdos184.CountThreeOrder
