import Submission.ThreeHubGlobalMinimal

/-! An optimal even remainder need not be even-minimal, even when the source
is globally minimal and its singleton forest is secondary-optimal.
This is an auxiliary obstruction, not a negation of Erdős184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.BestEvenRemainderObstruction
open Critical EvenCore SingletonExchange ThreeHubCompleteNumber
set_option maxHeartbeats 1600000
abbrev V := Fin 3 ⊕ Fin 10
abbrev source : SimpleGraph V := graph 10

def hub (b : Fin 10) : Fin 3 := if b.val < 2 then 0 else if b.val < 6 then 1 else 2

def forest : SimpleGraph V := SimpleGraph.fromRel
  (fun x y => ∃ b : Fin 10, x = .inl (hub b) ∧ y = .inr b)
instance : DecidableRel forest.Adj := by unfold forest; infer_instance

def remainder : SimpleGraph V := source \ forest
instance : DecidableRel remainder.Adj := by unfold remainder; infer_instance

lemma forest_le : forest ≤ source := by
  change ∀ x y, forest.Adj x y → source.Adj x y
  decide +kernel

lemma forest_card : Nat.card forest.edgeSet = 10 := by
  have hd : ∀ b : Fin 10, forest.degree (.inr b) = 1 := by decide +kernel
  have he := (BipartiteLower.bipartite_edge_sums forest forest_le).2
  simp only [← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hd he
  simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] at he
  exact he

lemma remainder_even : ∀ v : V, Even (Nat.card (remainder.neighborSet v)) := by
  have h : ∀ v : V, Even (remainder.degree v) := by decide +kernel
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h

private def c₀ : remainder.Walk (.inl 0) (.inl 0) :=
  .cons (show remainder.Adj (.inl 0) (.inr 2) by decide +kernel)
    (.cons (show remainder.Adj (.inr 2) (.inl 2) by decide +kernel)
    (.cons (show remainder.Adj (.inl 2) (.inr 0) by decide +kernel)
    (.cons (show remainder.Adj (.inr 0) (.inl 1) by decide +kernel)
    (.cons (show remainder.Adj (.inl 1) (.inr 6) by decide +kernel) (.cons (by decide +kernel) .nil)))))
private def c₁ : remainder.Walk (.inl 0) (.inl 0) :=
  .cons (show remainder.Adj (.inl 0) (.inr 3) by decide +kernel)
    (.cons (show remainder.Adj (.inr 3) (.inl 2) by decide +kernel)
    (.cons (show remainder.Adj (.inl 2) (.inr 1) by decide +kernel)
    (.cons (show remainder.Adj (.inr 1) (.inl 1) by decide +kernel)
    (.cons (show remainder.Adj (.inl 1) (.inr 7) by decide +kernel) (.cons (by decide +kernel) .nil)))))
private def c₂ : remainder.Walk (.inl 0) (.inl 0) :=
  .cons (show remainder.Adj (.inl 0) (.inr 4) by decide +kernel)
    (.cons (show remainder.Adj (.inr 4) (.inl 2) by decide +kernel)
    (.cons (show remainder.Adj (.inl 2) (.inr 5) by decide +kernel) (.cons (by decide +kernel) .nil)))
private def c₃ : remainder.Walk (.inl 0) (.inl 0) :=
  .cons (show remainder.Adj (.inl 0) (.inr 8) by decide +kernel)
    (.cons (show remainder.Adj (.inr 8) (.inl 1) by decide +kernel)
    (.cons (show remainder.Adj (.inl 1) (.inr 9) by decide +kernel) (.cons (by decide +kernel) .nil)))
private def cycles : Fin 4 → remainder.Walk (.inl 0) (.inl 0) := ![c₀,c₁,c₂,c₃]
private lemma cycles_valid (i : Fin 4) : (cycles i).IsCycle := by
  fin_cases i <;> rw [Walk.isCycle_def, Walk.isTrail_def] <;> decide +kernel

lemma remainder_number : number remainder = 4 := by
  have hu : number remainder ≤ 4 := by
    let P : Fin 4 → remainder.Subgraph := fun i => (cycles i).toSubgraph
    let E : Fin 4 → Finset (Sym2 V) := fun i => (cycles i).edges.toFinset
    have hd : IsDecomposition remainder (Finset.univ.image P) := by
      apply Compression.finite_family_decomposition P E
      · intro i; ext e; simp [P,E]
      · change ∀ i j : Fin 4, i ≠ j → Disjoint (cycles i).edges.toFinset (cycles j).edges.toFinset
        decide +kernel
      · change ∀ a b : V, remainder.Adj a b ↔ ∃ i : Fin 4, s(a,b) ∈ (cycles i).edges.toFinset
        decide +kernel
    have hp : ∀ H ∈ Finset.univ.image P, IsCycleOrEdge H.coe := by
      intro H hH
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
      exact Or.inl (by
        simpa only [P, SimpleGraph.IsRegularOfDegree,
          ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using cycle_coe_regular remainder (cycles_valid i))
    exact (number_le _ hp hd).trans (Finset.card_image_le.trans (by simp))
  have hl := StarCore.number_degree_bound remainder (.inl 0)
  have hd : remainder.degree (.inl 0) = 8 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hd
  omega

lemma source_number : number source = 14 := exact_number 10 (by decide)

lemma forest_best : Best source forest := by
  refine ⟨⟨forest_le,remainder_even,?_⟩,?_⟩
  · change number remainder + Nat.card forest.edgeSet = number source
    rw [remainder_number,forest_card,source_number]
  · intro R hR
    rw [forest_card]
    have hd (b : Fin 10) : 1 ≤ R.degree (.inr b) := by
      have he := Nat.even_iff.mp (hR.2.1 (.inr b))
      have hg := degree_sdiff_add source R hR.1 (.inr b)
      have hs := BipartiteLower.complete_degree_right (A := Fin 3) b
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
        Nat.card_fin] at hg hs ⊢
      change Nat.card (source.neighborSet (.inr b)) = 3 at hs
      omega
    have he := (BipartiteLower.bipartite_edge_sums R hR.1).2
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hd b)
    rw [← he] at hs
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_fin] using hs

lemma source_minimal : EdgeHull.Minimal source :=
  ThreeHubGlobalMinimal.complete_minimal 3 (by decide)

private def missed : remainder.Walk (.inl 1) (.inl 1) :=
  .cons (show remainder.Adj (.inl 1) (.inr 0) by decide +kernel)
    (.cons (show remainder.Adj (.inr 0) (.inl 2) by decide +kernel)
    (.cons (show remainder.Adj (.inl 2) (.inr 1) by decide +kernel) (.cons (by decide +kernel) .nil)))
private lemma missed_cycle : missed.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide +kernel

lemma remainder_not_evenMinimal : ¬ EvenMinimal remainder := by
  intro hm
  have he : ∀ v, Even (remainder.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using remainder_even
  have hn := hm.cycleCritical (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using he) _ missed missed_cycle
  have hd := degree_sdiff_add remainder missed.toSubgraph.spanningCoe
    missed.toSubgraph.spanningCoe_le (.inl 0)
  have hzero := regular_two_spanning_degree missed.toSubgraph
    (cycle_coe_regular remainder missed_cycle).2 (.inl 0)
  have hnot : (.inl 0 : V) ∉ missed.toSubgraph.verts := by
    simp [Walk.mem_verts_toSubgraph, missed]
  rw [if_neg hnot] at hzero
  have hdegree : remainder.degree (.inl 0) = 8 := by decide +kernel
  have hl := StarCore.number_degree_bound (remainder \ missed.toSubgraph.spanningCoe) (.inl 0)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd hzero hdegree hl
  rw [remainder_number] at hn
  omega

/-- Global minimality of the source does not imply even-minimality of the
remainder of a Best split. This theorem is not an original-conjecture disproof. -/
lemma obstruction : EdgeHull.Minimal source ∧ Best source forest ∧
    ¬ EvenMinimal (source \ forest) :=
  ⟨source_minimal,forest_best,remainder_not_evenMinimal⟩

end Erdos184Work.BestEvenRemainderObstruction
#print axioms Erdos184Work.BestEvenRemainderObstruction.obstruction
