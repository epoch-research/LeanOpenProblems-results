import Submission.BlockPotentialPlateau

/-!
Feedback-vertex kernels retaining a specified vertex degree. These are exact
critical kernels, but their count need not be only one below the original count.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FeedbackKernels
open CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma cycle_mem_of_feedback {G : SimpleGraph V} (v : V)
    (hf : (G.deleteIncidenceSet v).IsAcyclic) (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) : v ∈ C.verts := by
  by_contra hn
  obtain ⟨e,heC,he⟩ := cycle_has_edge_outside_forest (G.deleteIncidenceSet v) hf C hc.1 hc.2
  apply he
  induction e using Sym2.ind with
  | h x y =>
    exact deleteIncidenceSet_adj.mpr ⟨C.adj_sub heC,
      fun hx => hn (hx ▸ C.edge_vert heC),fun hy => hn (hy ▸ C.edge_vert heC.symm)⟩

lemma partition_count_of_feedback {G : SimpleGraph V} (v : V)
    (hf : (G.deleteIncidenceSet v).IsAcyclic) (D : Finset G.Subgraph)
    (hc : ∀ C ∈ D, C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : 2 * D.card = G.degree v := by
  have hh := cycle_decomposition_vertex_count G D hc hd v
  have heq : D.filter (fun C => v ∈ C.verts) = D := by
    apply Finset.filter_eq_self.mpr
    intro C hC
    exact cycle_mem_of_feedback v hf C (hc C hC)
  rwa [heq] at hh

lemma invariant_of_feedback {G : SimpleGraph V} (v : V)
    (hf : (G.deleteIncidenceSet v).IsAcyclic) : InvariantPartitions.HasInvariantCount G := by
  intro D E hcD hdD hcE hdE
  have hD := partition_count_of_feedback v hf D hcD hdD
  have hE := partition_count_of_feedback v hf E hcE hdE
  omega

lemma critical_of_feedback {G : SimpleGraph V} (he : ∀ x, Even (G.degree x))
    (v : V) (hf : (G.deleteIncidenceSet v).IsAcyclic) (r : ℕ)
    (hr : G.degree v = 2*r) : IsCountCritical r G := by
  have hc := of_invariant he (invariant_of_feedback v hf)
  obtain ⟨D,hcy,hd,hcard⟩ := minimum_exists G he
  have hh := partition_count_of_feedback v hf D hcy hd
  have hn : cycleNumber G = r := by omega
  rwa [hn] at hc

/-- Repeatedly deleting cycles avoiding v terminates with a forest away from v.
No degree at v is lost. The selected graph need not be connected or spanning. -/
lemma exists_feedback_subgraph (G : SimpleGraph V) (he : ∀ x, Even (G.degree x)) (v : V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (∀ x, Even (H.degree x)) ∧
      H.degree v = G.degree v ∧ (H.deleteIncidenceSet v).IsAcyclic := by
  let P (m : ℕ) := ∃ H : SimpleGraph V, H ≤ G ∧ (∀ x, Even (H.degree x)) ∧
    H.degree v = G.degree v ∧ H.edgeSet.ncard = m
  have hex : ∃ m, P m := ⟨G.edgeSet.ncard,G,le_rfl,he,rfl,rfl⟩
  obtain ⟨H,hHG,heH,hdeg,hsize⟩ := Nat.find_spec hex
  refine ⟨H,hHG,heH,hdeg,?_⟩
  by_contra hacyc
  obtain ⟨a,p,hp⟩ : ∃ a, ∃ p : (H.deleteIncidenceSet v).Walk a a, p.IsCycle := by
    simpa only [IsAcyclic,not_forall,not_not] using hacyc
  let C := promote (H.deleteIncidenceSet_le v) p.toSubgraph
  have hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2 := by
    have hh := cycle_subgraph_regular (H.deleteIncidenceSet v) hp
    refine ⟨hh.1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hh.2 x
  have hC0 : C.spanningCoe.degree v = 0 := by
    apply (C.spanningCoe.degree_eq_zero_iff_notMem_support v).mpr
    rintro ⟨w,hw⟩
    have hh : (H.deleteIncidenceSet v).Adj v w := p.toSubgraph.adj_sub hw
    exact (deleteIncidenceSet_adj.mp hh).2.1 rfl
  have hres : (H \ C.spanningCoe).degree v = G.degree v := by
    have hh := degree_sdiff_of_le C.spanningCoe_le v
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hC0 hdeg ⊢
    omega
  have hresEven := residual_even heH C hc
  have hP : P (H \ C.spanningCoe).edgeSet.ncard := by
    refine ⟨H \ C.spanningCoe,sdiff_le.trans hHG,?_,?_,rfl⟩
    · intro x
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hresEven x
    · simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hres
  have hm := Nat.find_min' hex hP
  have hlt := edges_lt (show H \ C.spanningCoe ≤ H from sdiff_le) (residual_proper C hc)
  omega

lemma exists_feedback_critical_kernel (G : SimpleGraph V) (he : ∀ x, Even (G.degree x))
    (v : V) (r : ℕ) (hr : G.degree v = 2*r) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.degree v = G.degree v ∧
      (H.deleteIncidenceSet v).IsAcyclic ∧ IsCountCritical r H := by
  obtain ⟨H,hHG,heH,hdeg,hf⟩ := exists_feedback_subgraph G he v
  refine ⟨H,hHG,hdeg,hf,critical_of_feedback heH v hf r ?_⟩
  exact hdeg.trans hr

end Erdos184.FeedbackKernels
