import Submission.CycleMixing

/-! A Hamiltonian example obstructing an acyclic-blue chain repair rule.
This is not a counterexample to Hamiltonian hitting or to Erdős 184. -/
open SimpleGraph
namespace Erdos184.PairBlockChain

abbrev V := Fin 15

def redEdges : Finset (Sym2 V) := {s(0,3), s(3,1), s(1,4), s(4,5), s(5,11), s(11,2), s(2,7), s(7,6), s(6,12), s(12,8), s(8,9), s(9,13), s(13,14), s(14,10), s(10,0)}

def blueEdges : Finset (Sym2 V) := {s(0,1), s(1,2), s(2,0), s(3,4), s(4,6), s(6,5), s(5,3), s(7,8), s(8,10), s(10,9), s(9,7), s(11,13), s(13,12), s(12,14), s(14,11)}

def R : SimpleGraph V := SimpleGraph.fromEdgeSet (redEdges : Set (Sym2 V))
def B : SimpleGraph V := SimpleGraph.fromEdgeSet (blueEdges : Set (Sym2 V))
def G : SimpleGraph V := R ⊔ B

instance : DecidableRel R.Adj := by unfold R; infer_instance
instance : DecidableRel B.Adj := by unfold B; infer_instance
instance : DecidableRel G.Adj := by unfold G; infer_instance

def red : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 2) <|
  .cons (by decide : G.Adj 2 7) <|
  .cons (by decide : G.Adj 7 6) <|
  .cons (by decide : G.Adj 6 12) <|
  .cons (by decide : G.Adj 12 8) <|
  .cons (by decide : G.Adj 8 9) <|
  .cons (by decide : G.Adj 9 13) <|
  .cons (by decide : G.Adj 13 14) <|
  .cons (by decide : G.Adj 14 10) <|
  .cons (by decide : G.Adj 10 0) .nil

lemma red_cycle : red.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [red], by decide⟩

def p0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 4) <|
  .cons (by decide : G.Adj 4 5) <|
  .cons (by decide : G.Adj 5 6) <|
  .cons (by decide : G.Adj 6 7) <|
  .cons (by decide : G.Adj 7 8) <|
  .cons (by decide : G.Adj 8 9) <|
  .cons (by decide : G.Adj 9 10) <|
  .cons (by decide : G.Adj 10 0) .nil

lemma p0_cycle : p0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [p0], by decide⟩

def p1 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 13) <|
  .cons (by decide : G.Adj 13 14) <|
  .cons (by decide : G.Adj 14 12) <|
  .cons (by decide : G.Adj 12 6) <|
  .cons (by decide : G.Adj 6 4) <|
  .cons (by decide : G.Adj 4 1) .nil

lemma p1_cycle : p1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [p1], by decide⟩

def p2 : G.Walk 2 2 :=
  .cons (by decide : G.Adj 2 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 13) <|
  .cons (by decide : G.Adj 13 12) <|
  .cons (by decide : G.Adj 12 8) <|
  .cons (by decide : G.Adj 8 10) <|
  .cons (by decide : G.Adj 10 14) <|
  .cons (by decide : G.Adj 14 11) <|
  .cons (by decide : G.Adj 11 2) .nil

lemma p2_cycle : p2.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [p2], by decide⟩

def triangle : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 0) .nil

lemma triangle_cycle : triangle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [triangle], by decide⟩

def b0 : G.Walk 3 3 :=
  .cons (by decide : G.Adj 3 4) <|
  .cons (by decide : G.Adj 4 6) <|
  .cons (by decide : G.Adj 6 5) <|
  .cons (by decide : G.Adj 5 3) .nil

lemma b0_cycle : b0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [b0], by decide⟩

def b1 : G.Walk 7 7 :=
  .cons (by decide : G.Adj 7 8) <|
  .cons (by decide : G.Adj 8 10) <|
  .cons (by decide : G.Adj 10 9) <|
  .cons (by decide : G.Adj 9 7) .nil

lemma b1_cycle : b1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [b1], by decide⟩

def b2 : G.Walk 11 11 :=
  .cons (by decide : G.Adj 11 13) <|
  .cons (by decide : G.Adj 13 12) <|
  .cons (by decide : G.Adj 12 14) <|
  .cons (by decide : G.Adj 14 11) .nil

lemma b2_cycle : b2.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [b2], by decide⟩

def ham0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 4) <|
  .cons (by decide : G.Adj 4 5) <|
  .cons (by decide : G.Adj 5 6) <|
  .cons (by decide : G.Adj 6 12) <|
  .cons (by decide : G.Adj 12 13) <|
  .cons (by decide : G.Adj 13 9) <|
  .cons (by decide : G.Adj 9 8) <|
  .cons (by decide : G.Adj 8 7) <|
  .cons (by decide : G.Adj 7 2) <|
  .cons (by decide : G.Adj 2 11) <|
  .cons (by decide : G.Adj 11 14) <|
  .cons (by decide : G.Adj 14 10) <|
  .cons (by decide : G.Adj 10 0) .nil

lemma ham0_cycle : ham0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [ham0], by decide⟩

def ham1 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 6) <|
  .cons (by decide : G.Adj 6 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 12) <|
  .cons (by decide : G.Adj 12 14) <|
  .cons (by decide : G.Adj 14 13) <|
  .cons (by decide : G.Adj 13 11) <|
  .cons (by decide : G.Adj 11 5) <|
  .cons (by decide : G.Adj 5 3) <|
  .cons (by decide : G.Adj 3 0) .nil

lemma ham1_cycle : ham1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [ham1], by decide⟩

def piece : Fin 4 → G.Subgraph :=
  ![p0.toSubgraph, p1.toSubgraph, p2.toSubgraph, triangle.toSubgraph]
def pieceEdges : Fin 4 → List (Sym2 V) := ![p0.edges, p1.edges, p2.edges, triangle.edges]
def good (i : Fin 3) : G.Subgraph := piece i.castSucc

def goodEdges : Fin 3 → List (Sym2 V) := ![p0.edges, p1.edges, p2.edges]

lemma piece_edgeSet (i : Fin 4) : (piece i).edgeSet = {e | e ∈ pieceEdges i} := by
  fin_cases i <;> simp [piece, pieceEdges, Walk.edgeSet_toSubgraph]

lemma good_edgeSet (i : Fin 3) : (good i).edgeSet = {e | e ∈ goodEdges i} := by
  fin_cases i <;> simp [good, piece, goodEdges, Walk.edgeSet_toSubgraph]

lemma piece_cycles (i : Fin 4) :
    (piece i).coe.Connected ∧ (piece i).coe.IsRegularOfDegree 2 := by
  fin_cases i
  · have hh := cycle_subgraph_regular G p0_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  · have hh := cycle_subgraph_regular G p1_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  · have hh := cycle_subgraph_regular G p2_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  · have hh := cycle_subgraph_regular G triangle_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma piece_edge_disjoint : ∀ i j : Fin 4, i ≠ j →
    Disjoint (piece i).edgeSet (piece j).edgeSet := by
  simp only [piece_edgeSet, Set.disjoint_left, Set.mem_setOf_eq]
  decide

open scoped Classical
noncomputable def D : Finset G.Subgraph := Finset.univ.image piece
noncomputable def goodPieces : Finset G.Subgraph := Finset.univ.image good

lemma D_cycles : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  intro H hH
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
  have hh := piece_cycles i
  refine ⟨hh.1, ?_⟩
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    using hh.2 v

lemma D_decomposition : IsDecomposition G D := by
  constructor
  · intro H hH K hK hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (show H ∈ Finset.univ.image piece from hH)
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (show K ∈ Finset.univ.image piece from hK)
    exact piece_edge_disjoint i j (fun h => hne (congrArg piece h))
  · ext e
    simp only [D, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_iUnion]
    have hh : e ∈ G.edgeSet ↔ ∃ i : Fin 4, e ∈ pieceEdges i := by
      induction e using Sym2.ind with
      | h u v =>
        have hcomp : ∀ u v : V, G.Adj u v ↔ ∃ i : Fin 4, s(u,v) ∈ pieceEdges i := by decide
        exact hcomp u v
    rw [hh]
    constructor
    · rintro ⟨H, ⟨i, rfl⟩, he⟩
      exact ⟨i, (Set.ext_iff.mp (piece_edgeSet i) e).mp he⟩
    · rintro ⟨i, he⟩
      exact ⟨piece i, ⟨i,rfl⟩, (Set.ext_iff.mp (piece_edgeSet i) e).mpr he⟩


lemma red_spanning : red.toSubgraph.verts = Set.univ := by
  ext v
  simp only [Walk.mem_verts_toSubgraph, Set.mem_univ, iff_true]
  fin_cases v <;> decide

lemma red_edges : red.toSubgraph.spanningCoe = R := by
  ext u v
  change s(u,v) ∈ red.toSubgraph.edgeSet ↔ R.Adj u v
  rw [Walk.edgeSet_toSubgraph]
  have hh : ∀ u v : V, s(u,v) ∈ red.edges ↔ R.Adj u v := by decide
  exact hh u v

set_option maxRecDepth 4096 in
lemma graph_regular : ∀ v : V, G.degree v = 4 := by decide

lemma graph_even : ∀ v : V, Even (G.degree v) := by
  intro v
  rw [graph_regular]
  decide

set_option maxRecDepth 4096 in
lemma blue_regular : ∀ v : V, B.degree v = 2 := by decide

lemma blue_isCycles : B.IsCycles := by
  intro v _
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    using blue_regular v

lemma triangle_blue : triangle.toSubgraph.edgeSet ⊆ B.edgeSet := by
  intro e he
  rw [Walk.edgeSet_toSubgraph] at he
  induction e using Sym2.ind with
  | h u v =>
    have hh : ∀ u v : V, s(u,v) ∈ triangle.edges → B.Adj u v := by decide
    exact hh u v he

lemma triangle_misses_red : Disjoint triangle.toSubgraph.edgeSet R.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hr
  rw [Walk.edgeSet_toSubgraph] at he
  induction e using Sym2.ind with
  | h u v =>
    have hh : ∀ u v : V, s(u,v) ∈ triangle.edges → ¬R.Adj u v := by decide
    exact hh u v he hr

lemma good_hits_red (i : Fin 3) : ((good i).edgeSet ∩ R.edgeSet).Nonempty := by
  fin_cases i
  · exact ⟨s(0,3), by rw [good_edgeSet]; decide, by decide⟩
  · exact ⟨s(1,3), by rw [good_edgeSet]; decide, by decide⟩
  · exact ⟨s(2,7), by rw [good_edgeSet]; decide, by decide⟩

def goodVerts : Fin 3 → List V := ![p0.support, p1.support, p2.support]

lemma good_mem_verts (i : Fin 3) (v : V) : v ∈ (good i).verts ↔ v ∈ goodVerts i := by
  fin_cases i <;> exact Walk.mem_verts_toSubgraph _

lemma good_triangle_overlap (i : Fin 3) :
    ((good i).verts ∩ triangle.toSubgraph.verts).ncard = 1 := by
  have heq : (good i).verts ∩ triangle.toSubgraph.verts =
      {Fin.castLE (by decide : 3 ≤ 15) i} := by
    ext v
    simp only [Set.mem_inter_iff, good_mem_verts, Walk.mem_verts_toSubgraph,
      Set.mem_singleton_iff]
    have hh : ∀ i : Fin 3, ∀ v : V,
        (v ∈ goodVerts i ∧ v ∈ triangle.support) ↔ v = Fin.castLE (by decide : 3 ≤ 15) i := by
      decide
    exact hh i v
  rw [heq]
  simp

def shared (i j : Fin 3) : G.Subgraph :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then b0.toSubgraph
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then b1.toSubgraph
  else b2.toSubgraph

def sharedEdges (i j : Fin 3) : List (Sym2 V) :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then b0.edges
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then b1.edges
  else b2.edges

lemma shared_edgeSet (i j : Fin 3) : (shared i j).edgeSet = {e | e ∈ sharedEdges i j} := by
  unfold shared sharedEdges
  split_ifs <;> simp only [Walk.edgeSet_toSubgraph]

lemma shared_cycles (i j : Fin 3) :
    (shared i j).coe.Connected ∧ (shared i j).coe.IsRegularOfDegree 2 := by
  have hmem : shared i j = b0.toSubgraph ∨ shared i j = b1.toSubgraph ∨
      shared i j = b2.toSubgraph := by
    unfold shared
    split_ifs <;> simp
  rcases hmem with h | h | h
  · rw [h]
    have hh := cycle_subgraph_regular G b0_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  · rw [h]
    have hh := cycle_subgraph_regular G b1_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  · rw [h]
    have hh := cycle_subgraph_regular G b2_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma shared_edges_subset (i j : Fin 3) (hij : i ≠ j) :
    (shared i j).edgeSet ⊆ B.edgeSet ∩ ((good i).edgeSet ∪ (good j).edgeSet) := by
  intro e he
  rw [shared_edgeSet] at he
  rw [good_edgeSet, good_edgeSet]
  induction e using Sym2.ind with
  | h u v =>
    have hh : ∀ i j : Fin 3, i ≠ j → ∀ u v : V, s(u,v) ∈ sharedEdges i j →
        B.Adj u v ∧ (s(u,v) ∈ goodEdges i ∨ s(u,v) ∈ goodEdges j) := by decide
    exact hh i j hij u v he

/-- Any two distinct good pieces already contain a whole all-blue cycle. -/
lemma pair_blue_cyclic (i j : Fin 3) (hij : i ≠ j) :
    ¬(((good i).spanningCoe ⊔ (good j).spanningCoe) ⊓ B).IsAcyclic := by
  intro ha
  have hsub : (shared i j).edgeSet ⊆
      (((good i).spanningCoe ⊔ (good j).spanningCoe) ⊓ B).edgeSet := by
    intro e he
    have hh := shared_edges_subset i j hij he
    rw [SimpleGraph.edgeSet_inf, SimpleGraph.edgeSet_sup]
    exact ⟨hh.2, hh.1⟩
  have hm := cycle_has_edge_outside_forest _ ha (shared i j)
    (shared_cycles i j).1 (by
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (shared_cycles i j).2 v)
  obtain ⟨e, he, hn⟩ := hm
  exact hn (hsub he)


lemma acyclic_blue_subfamily_overlap_le_one (S : Finset G.Subgraph)
    (hS : S ⊆ goodPieces) (ha : (unionPieces G S ⊓ B).IsAcyclic) :
    ((unionPieces G S).support ∩ triangle.toSubgraph.verts).ncard ≤ 1 := by
  have hle : ∀ H ∈ S, H.spanningCoe ≤ unionPieces G S := by
    intro H hH u v huv
    change s(u,v) ∈ (unionPieces G S).edgeSet
    rw [unionPieces_edgeSet]
    simp only [Set.mem_iUnion]
    exact ⟨H, hH, huv⟩
  have hsingle : ∀ H ∈ S, ∀ K ∈ S, H = K := by
    intro H hH K hK
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (show H ∈ Finset.univ.image good from hS hH)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (show K ∈ Finset.univ.image good from hS hK)
    by_cases hij : i = j
    · exact hi.symm.trans (hij ▸ hj)
    · exfalso
      apply pair_blue_cyclic i j hij
      exact ha.anti (inf_le_inf (sup_le (hi.symm ▸ hle H hH) (hj.symm ▸ hle K hK)) le_rfl)
  rcases S.eq_empty_or_nonempty with h0 | ⟨H,hH⟩
  · subst S
    simp [unionPieces]
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp
      (show H ∈ Finset.univ.image good from hS hH)
    have hsub : (unionPieces G S).support ∩ triangle.toSubgraph.verts ⊆
        (good i).verts ∩ triangle.toSubgraph.verts := by
      intro v ⟨⟨w, hvw⟩, hvT⟩
      have he : s(v,w) ∈ (unionPieces G S).edgeSet := hvw
      rw [unionPieces_edgeSet] at he
      simp only [Set.mem_iUnion] at he
      obtain ⟨J, hJ, heJ⟩ := he
      rw [hsingle J hJ (good i) hH] at heJ
      exact ⟨(good i).edge_vert heJ, hvT⟩
    have hh := Set.ncard_le_ncard hsub
    rwa [good_triangle_overlap] at hh

/-- No subfamily of the three good pieces bridges two vertices of the bad
triangle while keeping its blue part acyclic. -/
lemma no_acyclic_blue_bridge :
    ¬ ∃ S : Finset G.Subgraph, S ⊆ goodPieces ∧
      2 ≤ ((unionPieces G S).support ∩ triangle.toSubgraph.verts).ncard ∧
      (unionPieces G S ⊓ B).IsAcyclic := by
  rintro ⟨S, hS, hover, ha⟩
  have hh := acyclic_blue_subfamily_overlap_le_one S hS ha
  omega

noncomputable def efficient : Finset G.Subgraph := {ham0.toSubgraph, ham1.toSubgraph}

lemma efficient_cycles : ∀ H ∈ efficient, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  intro H hH
  simp only [efficient, Finset.mem_insert, Finset.mem_singleton] at hH
  rcases hH with rfl | rfl
  · have hh := cycle_subgraph_regular G ham0_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  · have hh := cycle_subgraph_regular G ham1_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v

lemma efficient_disjoint : Disjoint ham0.toSubgraph.edgeSet ham1.toSubgraph.edgeSet := by
  simp only [Walk.edgeSet_toSubgraph, Set.disjoint_left, Set.mem_setOf_eq]
  exact List.disjoint_of_nodup_append (by decide : (ham0.edges ++ ham1.edges).Nodup)

lemma efficient_decomposition : IsDecomposition G efficient := by
  constructor
  · intro H hH K hK hne
    simp only [efficient, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hH hK
    rcases hH with rfl | rfl <;> rcases hK with rfl | rfl
    · exact (hne rfl).elim
    · exact efficient_disjoint
    · exact efficient_disjoint.symm
    · exact (hne rfl).elim
  · simp only [efficient, Finset.mem_insert, Finset.mem_singleton,
      Set.iUnion_iUnion_eq_or_left, Set.iUnion_iUnion_eq_left]
    ext e
    induction e using Sym2.ind with
    | h u v =>
      simp only [Set.mem_union, Walk.edgeSet_toSubgraph, Set.mem_setOf_eq]
      change (s(u,v) ∈ ham0.edges ∨ s(u,v) ∈ ham1.edges) ↔ G.Adj u v
      have hh : ∀ u v : V, (s(u,v) ∈ ham0.edges ∨ s(u,v) ∈ ham1.edges) ↔ G.Adj u v := by
        decide
      exact hh u v

lemma efficient_hits_red : ∀ H ∈ efficient, (H.edgeSet ∩ R.edgeSet).Nonempty := by
  intro H hH
  simp only [efficient, Finset.mem_insert, Finset.mem_singleton] at hH
  rcases hH with rfl | rfl
  · refine ⟨s(1,3), ?_, by decide⟩
    rw [Walk.edgeSet_toSubgraph]
    decide
  · refine ⟨s(0,3), ?_, by decide⟩
    rw [Walk.edgeSet_toSubgraph]
    decide

lemma efficient_card : efficient.card = 2 := by
  have hne : ham0.toSubgraph ≠ ham1.toSubgraph := by
    intro h
    have he : s(0,1) ∈ ham0.toSubgraph.edgeSet := by rw [Walk.edgeSet_toSubgraph]; decide
    have hn : s(0,1) ∉ ham1.toSubgraph.edgeSet := by rw [Walk.edgeSet_toSubgraph]; decide
    exact hn (h ▸ he)
  simp [efficient, hne]

end Erdos184.PairBlockChain
