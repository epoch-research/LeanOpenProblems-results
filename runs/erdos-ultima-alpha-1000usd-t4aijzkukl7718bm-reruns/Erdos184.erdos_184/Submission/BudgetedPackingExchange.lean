import Submission.BudgetedCyclePacking
import Submission.TwoTerminalGluing

/-!
Exchange inequalities for maximum-coverage cycle packings. Replacements may
reuse edges from removed pieces; they need only avoid the retained pieces.
The resulting detour restrictions do not yet give a linear residual bound.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.BudgetedCyclePacking
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Arbitrarily many pieces may be replaced, and their edges may be reused.
Only the retained family must be edge-disjoint from the replacement family. -/
lemma Optimal.exchange_family_le {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (S F : Finset G.Subgraph) (hSD : S ⊆ D)
    (hcF : ∀ K ∈ F, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hdF : Set.PairwiseDisjoint (F : Set G.Subgraph) (fun K => K.edgeSet))
    (hcross : ∀ H ∈ D \ S, ∀ K ∈ F, Disjoint H.edgeSet K.edgeSet)
    (hcard : F.card ≤ S.card) : weight F ≤ weight S := by
  have hdis : Disjoint (D \ S) F := by
    apply Finset.disjoint_left.mpr
    intro H hH hF
    obtain ⟨e, he⟩ := cycle_edgeSet_nonempty H (hcF H hF).1 (hcF H hF).2
    exact Set.disjoint_left.mp (hcross H hH H hF) he he
  have hE : Feasible G k ((D \ S) ∪ F) := by
    refine ⟨?_, ?_, ?_⟩
    · intro H hH
      rcases Finset.mem_union.mp hH with hH | hH
      · exact hm.1.1 H (Finset.mem_sdiff.mp hH).1
      · exact hcF H hH
    · intro H hH K hK hne
      rcases Finset.mem_union.mp hH with hH | hH <;>
        rcases Finset.mem_union.mp hK with hK | hK
      · exact hm.1.2.1 (Finset.mem_sdiff.mp hH).1 (Finset.mem_sdiff.mp hK).1 hne
      · exact hcross H hH K hK
      · exact (hcross K hK H hH).symm
      · exact hdF hH hK hne
    · rw [Finset.card_union_of_disjoint hdis, Finset.card_sdiff_of_subset hSD]
      have hle := Finset.card_le_card hSD
      have hk := hm.1.2.2
      omega
  have hh := hm.2 _ hE
  have hsplit : weight (D \ S) + weight S = weight D := by
    exact Finset.sum_sdiff hSD
  have hunion : weight ((D \ S) ∪ F) = weight (D \ S) + weight F := by
    exact Finset.sum_union hdis
  rw [hunion] at hh
  omega

/-- One-piece specialization, without the earlier requirement that the new
cycle be disjoint from the old piece it replaces. -/
lemma Optimal.exchange_one_le {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (H : G.Subgraph) (hH : H ∈ D)
    (K : G.Subgraph) (hcK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hcross : ∀ J ∈ D.erase H, Disjoint K.edgeSet J.edgeSet) :
    K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  have hh := hm.exchange_family_le {H} {K} (by simpa using hH)
    (by simpa using hcK) (by simp) (by
      intro J hJ L hL
      have hLK : L = K := Finset.mem_singleton.mp hL
      subst L
      apply (hcross J _).symm
      simpa only [Finset.sdiff_singleton_eq_erase] using hJ)
    (by simp)
  simpa only [weight, Finset.sum_singleton] using hh

/-- Every selected cycle is longest in its union with the residual. This is
stronger than comparing it only with cycles wholly in the residual. -/
lemma Optimal.available_cycle_le {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (H : G.Subgraph) (hH : H ∈ D)
    (K : G.Subgraph) (hcK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hsub : K.edgeSet ⊆ H.edgeSet ∪ (G \ unionPieces G D).edgeSet) :
    K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  apply hm.exchange_one_le H hH K hcK
  intro J hJ
  obtain ⟨hne, hJD⟩ := Finset.mem_erase.mp hJ
  apply Set.disjoint_left.mpr
  intro e heK heJ
  rcases hsub heK with heH | heR
  · exact Set.disjoint_left.mp (hm.1.2.1 hH hJD hne.symm) heH heJ
  · rw [SimpleGraph.edgeSet_sdiff] at heR
    apply heR.2
    rw [unionPieces_edgeSet]
    exact Set.mem_iUnion₂.mpr ⟨J, hJD, heJ⟩

/-- Replace one edge of a simple cycle by a two-edge path through a new
vertex. The resulting object is again a simple cycle, and is one edge longer. -/
lemma edge_detour_cycle (H : G.Subgraph)
    (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) {u v x : V}
    (huv : H.Adj u v) (hux : G.Adj u x) (hxv : G.Adj x v) (hx : x ∉ H.verts) :
    ∃ K : G.Subgraph,
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      K.edgeSet ⊆ H.edgeSet ∪ {s(u,x), s(x,v)} ∧
      K.edgeSet.ncard = H.edgeSet.ncard + 1 := by
  obtain ⟨p, hp, hpe, hpv⟩ := TwoTerminalGluing.cycle_complementary_path
    H hcH.1 hcH.2 huv
  have hxp : x ∉ p.support := fun hh => hx (hpv x hh)
  let q := p.cons hxv
  have hq : q.IsPath := hp.cons hxp
  have hp0 : 0 < p.length :=
    Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne (H.adj_sub huv).ne.symm)
  have hql : 2 ≤ q.length := by
    simp only [q, Walk.length_cons]
    omega
  let c := q.cons hux
  have hc : c.IsCycle := path_close_isCycle q hq hql hux
  have hcardp : p.toSubgraph.edgeSet.ncard = p.length := by
    have hh := trail_spanning_edge_card p hp.isTrail
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hh
  have hpset : p.toSubgraph.edgeSet = H.edgeSet \ {s(u,v)} := by
    ext e
    simpa only [Walk.mem_edges_toSubgraph, Set.mem_diff, Set.mem_singleton_iff] using hpe e
  have hplen : p.length + 1 = H.edgeSet.ncard := by
    rw [← hcardp, hpset]
    exact Set.ncard_diff_singleton_add_one (show s(u,v) ∈ H.edgeSet from huv)
  have hcardc : c.toSubgraph.edgeSet.ncard = c.length := by
    have hh := trail_spanning_edge_card c hc.isTrail
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hh
  refine ⟨c.toSubgraph, cycle_subgraph_regular G hc, ?_, ?_⟩
  · intro e he
    rw [Walk.mem_edges_toSubgraph] at he
    simp only [c, q, Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he | he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
    · exact Or.inl ((hpe e).mp he).1
  · rw [hcardc]
    simp only [c, q, Walk.length_cons]
    omega

/-- Residual common neighbors cannot give an external detour around an edge
of a selected cycle. Both residual edges must be genuinely available. -/
lemma Optimal.residual_common_neighbor_mem {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (H : G.Subgraph) (hH : H ∈ D) {u v x : V}
    (huv : H.Adj u v)
    (hux : (G \ unionPieces G D).Adj u x)
    (hxv : (G \ unionPieces G D).Adj x v) : x ∈ H.verts := by
  by_contra hx
  obtain ⟨K, hcK, hsub, hlen⟩ := edge_detour_cycle H (hm.1.1 H hH) huv hux.1 hxv.1 hx
  have hh := hm.available_cycle_le H hH K hcK (by
    intro e he
    rcases hsub he with he | he
    · exact Or.inl he
    · rcases he with he | he
      · exact Or.inr (he ▸ hux)
      · exact Or.inr (he ▸ hxv))
  omega

end Erdos184.BudgetedCyclePacking
