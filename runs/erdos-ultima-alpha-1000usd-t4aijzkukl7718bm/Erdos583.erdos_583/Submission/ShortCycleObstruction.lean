import Submission.Work

/-! A counterexample to absorption based only on cycle length and member count.
This is not a counterexample to Gallai's conjecture. -/
open SimpleGraph Erdos583Work
namespace Erdos583ShortCycleObstructionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

abbrev edges : Finset (Sym2 (Fin 9)) :=
  {s(0,1),s(1,2),s(2,3),s(3,4),s(4,0),s(5,0),s(0,2),s(2,4),s(4,1),s(1,3),s(3,6),s(7,5),s(5,8)}

def G : SimpleGraph (Fin 9) := fromEdgeSet (edges : Set (Sym2 (Fin 9)))

instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (edges : Set (Sym2 (Fin 9)))).Adj)

abbrev outside : Finset (Fin 9) := {5,6,7,8}

lemma connected : G.Connected := by decide

lemma boundary : (boundaryGraph G (outside : Set (Fin 9))).edgeSet={s(0,5),s(3,6)} := by
  have he (p q : Prop) : p ≠ q ↔ ¬(p ↔ q) :=
    ⟨fun h hi ↦ h (propext hi),fun h hi ↦ h (hi ▸ Iff.rfl)⟩
  ext e
  induction e using Sym2.ind with
  | h a b =>
    change (G.Adj a b ∧ ((a ∈ outside) ≠ (b ∈ outside))) ↔
      s(a,b) ∈ ({s(0,5),s(3,6)} : Set (Sym2 (Fin 9)))
    rw [he]
    revert a b
    decide

lemma no_three_paths : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ 3 := by
  classical
  rintro ⟨D,hD,hDc⟩
  obtain ⟨E,hE,hmin⟩ := exists_min_decomposition G
  have hEc : E.card ≤ 3 := (hmin D hD).trans hDc
  have hnonempty : ∀ K ∈ E, K.edgeSet.Nonempty := fun K hK ↦ min_decomposition_edgeSet_nonempty hE hmin hK
  have hc : (boundaryGraph G (outside : Set (Fin 9))).edgeSet.ncard=2 := by
    rw [boundary,Set.ncard_pair]
    decide
  have hdeg : ∀ v : Fin 9, v ∉ outside → G.degree v=4 := by decide
  have hodd : (outside.filter fun v ↦ Odd (G.degree v)).card=4 := by decide
  have hs : 4 ≤ ∑ v ∈ outside, endpointMultiplicity E v := by
    rw [←hodd,Finset.card_filter]
    apply Finset.sum_le_sum
    intro v _
    split_ifs with hv
    · have ho := (hE.odd_endpointMultiplicity_iff v).mpr hv
      rw [Nat.odd_iff] at ho
      omega
    · omega
  have hz (v : Fin 9) (hv : v ∉ outside) : endpointMultiplicity E v=0 := by
    have hh := hE.degree_endpoint_cut_bound hnonempty outside hv
    rw [hdeg v hv,hc] at hh
    omega
  have he : ∑ v ∈ outside, endpointMultiplicity E v=2*E.card := by
    rw [Finset.sum_subset (Finset.subset_univ outside) (fun v _ hv ↦ hz v hv)]
    exact hE.sum_endpointMultiplicity hnonempty
  have hh := hE.degree_endpoint_cut_bound hnonempty outside (v := 0) (by decide)
  rw [hdeg 0 (by decide),hc,he] at hh
  omega

def c : G.Walk 0 0 := .cons (by decide : G.Adj 0 1)
  (.cons (by decide : G.Adj 1 2) (.cons (by decide : G.Adj 2 3)
    (.cons (by decide : G.Adj 3 4) (.cons (by decide : G.Adj 4 0) .nil))))

def p : G.Walk 5 6 := .cons (by decide : G.Adj 5 0)
  (.cons (by decide : G.Adj 0 2) (.cons (by decide : G.Adj 2 4)
    (.cons (by decide : G.Adj 4 1) (.cons (by decide : G.Adj 1 3)
      (.cons (by decide : G.Adj 3 6) .nil)))))

def q : G.Walk 7 8 := .cons (by decide : G.Adj 7 5)
  (.cons (by decide : G.Adj 5 8) .nil)

lemma cycle_and_paths : c.IsCycle ∧ p.IsPath ∧ q.IsPath := by
  constructor
  · simp [c,Walk.cons_isCycle_iff,Walk.isPath_def]
  · constructor <;> apply Walk.IsPath.mk' <;> decide

lemma disjoint_edges : Disjoint c.toSubgraph.edgeSet p.toSubgraph.edgeSet ∧
    Disjoint c.toSubgraph.edgeSet q.toSubgraph.edgeSet ∧
    Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet := by
  simp [Set.disjoint_left,c,p,q]

lemma cover : c.toSubgraph.edgeSet ∪ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet=G.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,mem_edgeSet]
    revert a b
    decide

/-- A connected union of one five-cycle and two paths need not have three
paths, although the cycle length is at most twice the member count. -/
lemma witness : G.Connected ∧ c.IsCycle ∧ p.IsPath ∧ q.IsPath ∧ c.length ≤ 2*3 ∧
    Disjoint c.toSubgraph.edgeSet p.toSubgraph.edgeSet ∧
    Disjoint c.toSubgraph.edgeSet q.toSubgraph.edgeSet ∧
    Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet ∧
    c.toSubgraph.edgeSet ∪ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet=G.edgeSet ∧
    ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ 3 :=
  ⟨connected,cycle_and_paths.1,cycle_and_paths.2.1,cycle_and_paths.2.2,by decide,
    disjoint_edges.1,disjoint_edges.2.1,disjoint_edges.2.2,cover,no_three_paths⟩

end Erdos583ShortCycleObstructionDevelopment
