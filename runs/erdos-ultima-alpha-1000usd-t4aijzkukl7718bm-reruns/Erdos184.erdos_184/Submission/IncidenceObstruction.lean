import Submission.Cuts

/-! A finite obstruction to reducing cycles from a binary vertex-incidence
relation. This is not a counterexample to Erdős 184. -/

open SimpleGraph
namespace Erdos184.IncidenceObstruction

abbrev K : SimpleGraph (Fin 10) := ⊤

def bigWalk : K.Walk 0 0 :=
  .cons (show K.Adj 0 3 by decide) <|
  .cons (show K.Adj 3 2 by decide) <|
  .cons (show K.Adj 2 4 by decide) <|
  .cons (show K.Adj 4 1 by decide) <|
  .cons (show K.Adj 1 6 by decide) <|
  .cons (show K.Adj 6 9 by decide) <|
  .cons (show K.Adj 9 7 by decide) <|
  .cons (show K.Adj 7 8 by decide) <|
  .cons (show K.Adj 8 5 by decide) <|
  .cons (show K.Adj 5 0 by decide) .nil

def leftWalk : K.Walk 0 0 :=
  .cons (show K.Adj 0 2 by decide) <|
  .cons (show K.Adj 2 1 by decide) <|
  .cons (show K.Adj 1 3 by decide) <|
  .cons (show K.Adj 3 4 by decide) <|
  .cons (show K.Adj 4 0 by decide) .nil

def rightWalk : K.Walk 5 5 :=
  .cons (show K.Adj 5 7 by decide) <|
  .cons (show K.Adj 7 6 by decide) <|
  .cons (show K.Adj 6 8 by decide) <|
  .cons (show K.Adj 8 9 by decide) <|
  .cons (show K.Adj 9 5 by decide) .nil

lemma big_cycle : bigWalk.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine ⟨?_, ?_, ?_⟩
  · decide
  · simp [bigWalk]
  · decide

lemma left_cycle : leftWalk.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine ⟨?_, ?_, ?_⟩
  · decide
  · simp [leftWalk]
  · decide

lemma right_cycle : rightWalk.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine ⟨?_, ?_, ?_⟩
  · decide
  · simp [rightWalk]
  · decide

def graph : SimpleGraph (Fin 10) :=
  bigWalk.toSubgraph.spanningCoe ⊔ leftWalk.toSubgraph.spanningCoe ⊔
    rightWalk.toSubgraph.spanningCoe

def rebase (H : K.Subgraph) (h : H.spanningCoe ≤ graph) : graph.Subgraph where
  verts := H.verts
  Adj := H.Adj
  adj_sub ha := h ha
  edge_vert := H.edge_vert
  symm := H.symm

def B : graph.Subgraph := rebase bigWalk.toSubgraph (le_sup_of_le_left le_sup_left)
def L : graph.Subgraph := rebase leftWalk.toSubgraph (le_sup_of_le_left le_sup_right)
def R : graph.Subgraph := rebase rightWalk.toSubgraph le_sup_right

lemma B_verts : B.verts = Set.univ := by
  ext v
  change v ∈ bigWalk.toSubgraph.verts ↔ v ∈ Set.univ
  rw [Walk.mem_verts_toSubgraph]
  fin_cases v <;> decide

lemma L_verts : L.verts = {v : Fin 10 | v.val < 5} := by
  ext v
  change v ∈ leftWalk.toSubgraph.verts ↔ v.val < 5
  rw [Walk.mem_verts_toSubgraph]
  fin_cases v <;> decide

lemma R_verts : R.verts = {v : Fin 10 | 5 ≤ v.val} := by
  ext v
  change v ∈ rightWalk.toSubgraph.verts ↔ 5 ≤ v.val
  rw [Walk.mem_verts_toSubgraph]
  fin_cases v <;> decide

lemma B_ne_L : B ≠ L := by
  intro h
  have hh := congrArg (fun H : graph.Subgraph => (5 : Fin 10) ∈ H.verts) h
  simp [B_verts, L_verts] at hh

lemma B_ne_R : B ≠ R := by
  intro h
  have hh := congrArg (fun H : graph.Subgraph => (0 : Fin 10) ∈ H.verts) h
  simp [B_verts, R_verts] at hh

lemma L_ne_R : L ≠ R := by
  intro h
  have hh := congrArg (fun H : graph.Subgraph => (0 : Fin 10) ∈ H.verts) h
  simp [L_verts, R_verts] at hh

open scoped Classical
noncomputable def D : Finset graph.Subgraph := {B, L, R}

lemma D_card : D.card = 3 := by
  simp [D, B_ne_L, B_ne_R, L_ne_R]

lemma D_cycles : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  intro H hH
  simp only [D, Finset.mem_insert, Finset.mem_singleton] at hH
  rcases hH with rfl | rfl | rfl
  · have hh := cycle_subgraph_regular K big_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  · have hh := cycle_subgraph_regular K left_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  · have hh := cycle_subgraph_regular K right_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v

lemma BL_disjoint : Disjoint B.edgeSet L.edgeSet := by
  change Disjoint bigWalk.toSubgraph.edgeSet leftWalk.toSubgraph.edgeSet
  simp only [Walk.edgeSet_toSubgraph, Set.disjoint_left, Set.mem_setOf_eq]
  exact List.disjoint_of_nodup_append (by decide : (bigWalk.edges ++ leftWalk.edges).Nodup)

lemma BR_disjoint : Disjoint B.edgeSet R.edgeSet := by
  change Disjoint bigWalk.toSubgraph.edgeSet rightWalk.toSubgraph.edgeSet
  simp only [Walk.edgeSet_toSubgraph, Set.disjoint_left, Set.mem_setOf_eq]
  exact List.disjoint_of_nodup_append (by decide : (bigWalk.edges ++ rightWalk.edges).Nodup)

lemma LR_disjoint : Disjoint L.edgeSet R.edgeSet := by
  change Disjoint leftWalk.toSubgraph.edgeSet rightWalk.toSubgraph.edgeSet
  simp only [Walk.edgeSet_toSubgraph, Set.disjoint_left, Set.mem_setOf_eq]
  exact List.disjoint_of_nodup_append (by decide : (leftWalk.edges ++ rightWalk.edges).Nodup)

lemma D_decomposition : IsDecomposition graph D := by
  constructor
  · intro H hH J hJ hne
    simp only [D, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hH hJ
    rcases hH with rfl | rfl | rfl <;> rcases hJ with rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact BL_disjoint
    · exact BR_disjoint
    · exact BL_disjoint.symm
    · exact (hne rfl).elim
    · exact LR_disjoint
    · exact BR_disjoint.symm
    · exact LR_disjoint.symm
    · exact (hne rfl).elim
  · simp only [D, Finset.mem_insert, Finset.mem_singleton, Set.iUnion_iUnion_eq_or_left,
      Set.iUnion_iUnion_eq_left]
    simp only [graph, SimpleGraph.edgeSet_sup]
    exact Set.union_assoc _ _ _ |>.symm

lemma graph_regular : graph.IsRegularOfDegree 4 := by
  intro v
  have hh := cycle_decomposition_vertex_count graph D D_cycles D_decomposition v
  have hc : (D.filter (fun H => v ∈ H.verts)).card = 2 := by
    by_cases hv : v.val < 5
    · have hn : ¬5 ≤ v.val := by omega
      simp [D, Finset.filter_insert, Finset.filter_singleton, B_verts, L_verts, R_verts, hv, hn, B_ne_L]
    · have hn : 5 ≤ v.val := by omega
      simp [D, Finset.filter_insert, Finset.filter_singleton, B_verts, L_verts, R_verts, hv, hn, B_ne_R]
  rw [hc] at hh
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    using hh.symm

lemma graph_adj_iff (u v : Fin 10) : graph.Adj u v ↔
    s(u, v) ∈ bigWalk.edges ∨ s(u, v) ∈ leftWalk.edges ∨ s(u, v) ∈ rightWalk.edges := by
  change s(u, v) ∈ graph.edgeSet ↔ _
  simp only [graph, SimpleGraph.edgeSet_sup, Set.mem_union]
  change (s(u, v) ∈ bigWalk.toSubgraph.edgeSet ∨ s(u, v) ∈ leftWalk.toSubgraph.edgeSet) ∨
      s(u, v) ∈ rightWalk.toSubgraph.edgeSet ↔ _
  simp only [Walk.mem_edges_toSubgraph, or_assoc]

lemma graph_two_cut : ¬ (graph.deleteEdges {s(0, 5), s(1, 6)}).Preconnected := by
  have hcheck : ∀ u v : Fin 10,
      (s(u, v) ∈ bigWalk.edges ∨ s(u, v) ∈ leftWalk.edges ∨ s(u, v) ∈ rightWalk.edges) →
      s(u, v) ∉ ({s(0, 5), s(1, 6)} : Set (Sym2 (Fin 10))) →
      (u.val < 5 ↔ v.val < 5) := by decide
  have hadj : ∀ {u v}, (graph.deleteEdges {s(0, 5), s(1, 6)}).Adj u v →
      (u.val < 5 ↔ v.val < 5) := by
    intro u v huv
    obtain ⟨huv, hnot⟩ := SimpleGraph.deleteEdges_adj.mp huv
    exact hcheck u v ((graph_adj_iff u v).mp huv) hnot
  have hwalk : ∀ {u v} (p : (graph.deleteEdges {s(0, 5), s(1, 6)}).Walk u v),
      (u.val < 5 ↔ v.val < 5) := by
    intro u v p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hadj h).trans ih
  intro hpre
  obtain ⟨p⟩ := hpre 0 5
  have hp := hwalk p
  norm_num at hp

lemma every_decomposition_at_least_three (E : Finset graph.Subgraph)
    (hcy : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition graph E) : 3 ≤ E.card :=
  regular_four_two_cut_cycle_lower graph graph_regular E hcy hd
    s(0, 5) s(1, 6) graph_two_cut

lemma D_minimum (E : Finset graph.Subgraph)
    (hcy : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition graph E) : D.card ≤ E.card := by
  rw [D_card]
  exact every_decomposition_at_least_three E hcy hd

lemma D_even_vertex_incidence (v : Fin 10) : Even ((D.filter (fun H => v ∈ H.verts)).card) := by
  have hh := cycle_decomposition_vertex_count graph D D_cycles D_decomposition v
  have hr := graph_regular v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hr
  have heq : (D.filter (fun H => v ∈ H.verts)).card = 2 := by omega
  rw [heq]
  decide

lemma no_proper_nonempty_even_incidence (S : Finset graph.Subgraph) (hS : S ⊆ D)
    (heven : ∀ v : Fin 10, Even ((S.filter (fun H => v ∈ H.verts)).card)) :
    S = ∅ ∨ S = D := by
  have hfilter (v : Fin 10) : S.filter (fun H => v ∈ H.verts) =
      D.filter (fun H => H ∈ S ∧ v ∈ H.verts) := by
    ext H
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hS h.1, h⟩, fun h => h.2⟩
  have hzero := heven 0
  have hfive := heven 5
  rw [hfilter] at hzero hfive
  have hBL : B ∈ S ↔ L ∈ S := by
    by_cases hb : B ∈ S <;> by_cases hl : L ∈ S <;>
      simp [D, Finset.filter_insert, Finset.filter_singleton, B_verts, L_verts,
        R_verts, hb, hl, B_ne_L] at hzero ⊢
  have hBR : B ∈ S ↔ R ∈ S := by
    by_cases hb : B ∈ S <;> by_cases hr : R ∈ S <;>
      simp [D, Finset.filter_insert, Finset.filter_singleton, B_verts, L_verts,
        R_verts, hb, hr, B_ne_R] at hfive ⊢
  by_cases hb : B ∈ S
  · right
    apply Finset.Subset.antisymm hS
    intro H hH
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl | rfl
    · exact hb
    · exact hBL.mp hb
    · exact hBR.mp hb
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro H hH
    have hH' := hS hH
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hH'
    rcases hH' with rfl | rfl | rfl
    · exact hb hH
    · exact hb (hBL.mpr hH)
    · exact hb (hBR.mpr hH)

lemma every_mixed_decomposition_at_least_three (E : Finset graph.Subgraph)
    (hc : ∀ H ∈ E, IsCycleOrEdge H.coe) (hd : IsDecomposition graph E) : 3 ≤ E.card := by
  have heven : ∀ v, Even (graph.degree v) := by
    intro v
    rw [graph_regular]
    decide
  obtain ⟨F, hcyF, hdF, hcard⟩ := refine_even_decomposition graph heven E hc hd
  exact (every_decomposition_at_least_three F hcyF hdF).trans hcard

end Erdos184.IncidenceObstruction
