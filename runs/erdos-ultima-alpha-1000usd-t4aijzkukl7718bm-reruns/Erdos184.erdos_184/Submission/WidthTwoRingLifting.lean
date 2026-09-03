import Submission.WidthTwoRing
import Submission.PrivatePathLifting

/-!
The all-crossing width-two ring construction survives arbitrary private path
replacements. This is a restricted exchange, not a general cycle-count bound.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.WidthTwoRing

lemma kernel_walk_pair (r : ℕ) :
    ∃ c d : (graph r).Walk (.inl 0) (.inl 0),
      c.IsCycle ∧ d.IsCycle ∧ c.edges.Disjoint d.edges ∧
      ∀ e, e ∈ c.edges ∨ e ∈ d.edges ↔ e ∈ (graph r).edgeSet := by
  obtain ⟨c,hc,hce⟩ := CycleRing.cycle_piece_walk_at (redPiece r)
    (redPiece_cycle r).1 (redPiece_cycle r).2 (.inl 0) (by trivial)
  obtain ⟨d,hd,hde⟩ := CycleRing.cycle_piece_walk_at (bluePiece r)
    (bluePiece_cycle r).1 (bluePiece_cycle r).2 (.inl 0) (by trivial)
  refine ⟨c,d,hc,hd,?_,?_⟩
  · intro e hec hed
    have hc' := c.mem_edges_toSubgraph.mpr hec
    have hd' := d.mem_edges_toSubgraph.mpr hed
    rw [hce] at hc'
    rw [hde] at hd'
    exact Set.disjoint_left.mp (red_blue_disjoint r) hc' hd'
  · intro e
    rw [← c.mem_edges_toSubgraph, ← d.mem_edges_toSubgraph, hce, hde]
    exact Set.ext_iff.mp (red_blue_cover r) e

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Replace every edge of an all-crossing width-two ring by a simple path.
Different replacement paths may meet only at their prescribed endpoints,
and all edges of G must occur in the replacement system. The resulting
union has a partition into at most two simple cycles. -/
theorem all_crossing_private_paths (r : ℕ)
    (M : PrivatePathLifting.Model (graph r) G)
    (hG : ∀ e ∈ G.edgeSet, ∃ a b, ∃ h : (graph r).Adj a b,
      e ∈ (M.path h).edges) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ 2 := by
  obtain ⟨c,d,hc,hd,hdis,hcover⟩ := kernel_walk_pair r
  exact M.two_cycle_decomposition c d hc hd hdis hcover hG

/-- Exclusion in a genuinely minimum decomposition, allowing arbitrary
private path lengths and arbitrary unused ambient edges. -/
theorem minimum_all_crossing_subfamily (r : ℕ)
    (M : PrivatePathLifting.Model (graph r) G)
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D)
    (hmin : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hS : S ⊆ D)
    (hcover : ∀ e, e ∈ (⋃ H ∈ S, H.edgeSet) ↔
      ∃ a b, ∃ h : (graph r).Adj a b, e ∈ (M.path h).edges) : S.card ≤ 2 := by
  obtain ⟨c,d,hc,hd,hdis,hcd⟩ := kernel_walk_pair r
  exact M.minimum_subfamily_bound c d hc hd hdis hcd D hD hdec hmin S hS hcover

end Erdos184.WidthTwoRing
