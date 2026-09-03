import Submission.ContractionBaseData

/-! The contraction obstruction is not an even-minimal core.
Its six vertex-disjoint triangles already require more cycles than the full graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ContractionGap
open Critical EvenCore BlockRestriction
set_option maxHeartbeats 200000
set_option maxRecDepth 20000

private def triangleEdges : List (Fin 29 × Fin 29) :=
  [(0,7),(7,9),(9,0), (1,5),(5,12),(12,1), (2,4),(4,14),(14,2),
   (6,10),(10,13),(13,6), (15,19),(19,26),(26,15), (16,18),(18,28),(28,16)]

private def triangles : SimpleGraph (Fin 29) :=
  SimpleGraph.fromRel (fun x y => (x,y) ∈ triangleEdges)
private instance : DecidableRel triangles.Adj := by unfold triangles; infer_instance

private def triVertex : Fin 6 → Fin 3 → Fin 29 :=
  ![![0,7,9], ![1,5,12], ![2,4,14], ![6,10,13], ![15,19,26], ![16,18,28]]

private def triEmb (i : Fin 6) : Fin 3 ↪ Fin 29 where
  toFun := triVertex i
  inj' := by fin_cases i <;> decide +kernel

private def triangleBlock : SimpleGraph (Option (Fin 3)) :=
  SimpleGraph.fromRel (fun x y => x.isSome ∧ y.isSome)
private instance : DecidableRel triangleBlock.Adj := by unfold triangleBlock; infer_instance

private lemma triOutside (i : Fin 6) : ∀ u : Fin 3, (3 : Fin 29) ∉ Set.range (triEmb i) := by
  fin_cases i <;> decide +kernel
private lemma triInternal (i : Fin 6) : ∀ u v,
    triangles.Adj (triEmb i u) (triEmb i v) ↔ triangleBlock.Adj (some u) (some v) := by
  fin_cases i <;> decide +kernel
private lemma triBoundary (i : Fin 6) : ∀ u x, x ∉ Set.range (triEmb i) →
    (triangles.Adj (triEmb i u) x ↔ x = 3 ∧ triangleBlock.Adj (some u) none) := by
  fin_cases i <;> decide +kernel

private def triangleModel (i : Fin 6) : BlockModel triangles triangleBlock where
  emb := triEmb i
  outer := fun _ => 3
  outside := triOutside i
  internal := triInternal i
  boundary := triBoundary i

private lemma triDisjoint : Pairwise (fun i j : Fin 6 =>
    Disjoint (Set.range (triangleModel i).emb) (Set.range (triangleModel j).emb)) := by
  intro i j hij
  rw [Set.disjoint_left]
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | decide +kernel

private lemma triangles_even : ∀ v, Even (triangles.degree v) := by
  intro v
  fin_cases v <;> decide +kernel

private lemma triangleBlock_gap : triangleBlock.degree none < 2 * number triangleBlock := by
  have hd : triangleBlock.degree none = 0 := by decide +kernel
  have hn : triangleBlock ≠ ⊥ := by
    intro h
    have he : triangleBlock.Adj (some 0) (some 1) := by decide +kernel
    rw [h] at he
    exact he
  have hk : number triangleBlock ≠ 0 := mt (StarCharacterization.number_eq_zero_iff _).mp hn
  omega

private lemma triangles_number_lower : 6 ≤ number triangles := by
  have h := card_blocks_le_number triangles (fun _ : Fin 6 => triangleBlock) triangleModel
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using triangles_even)
    (fun _ => by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using triangleBlock_gap) triDisjoint
  simpa only [Fintype.card_fin] using h

private lemma triangles_le : triangles ≤ graph := by
  intro x
  fin_cases x <;> decide +kernel

private lemma triangles_card_lt : triangles.edgeFinset.card < graph.edgeFinset.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeFinset_mono triangles_le, ?_⟩
  intro h
  have he : s((0 : Fin 29),15) ∈ graph.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset] using closing_adj
  rw [← h] at he
  have hn : s((0 : Fin 29),15) ∉ triangles.edgeFinset := by decide +kernel
  exact hn he

/-- This obstruction cannot refute a rule restricted to minimal even cores. -/
lemma graph_not_evenMinimal : ¬ EvenMinimal graph := by
  intro hm
  have h := hm triangles triangles_le
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using triangles_even)
    (by simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card]
      using triangles_card_lt)
  have hl := triangles_number_lower
  have hu := graph_upper
  omega

#print axioms graph_not_evenMinimal
end Erdos184Work.ContractionGap
