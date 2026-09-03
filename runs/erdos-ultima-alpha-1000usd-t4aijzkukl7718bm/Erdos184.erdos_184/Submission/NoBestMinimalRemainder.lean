import Submission.BestEvenRemainderObstruction

/-! In the globally minimal graph K_(3,10), no secondary-optimal singleton
forest has an even-minimal remainder. This rules out an auxiliary inheritance
principle, not the original asymptotic conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.NoBestMinimalRemainder
open Critical EvenCore SingletonExchange BestEvenRemainderObstruction
set_option maxHeartbeats 1600000

lemma any_best_not_evenMinimal {F : SimpleGraph V} (hF : Best source F) :
    ¬ EvenMinimal (source \ F) := by
  let E := source \ F
  have hFC : Nat.card F.edgeSet = 10 := by
    have h₁ := hF.2 forest forest_best.1
    have h₂ := forest_best.2 F hF.1
    rw [forest_card] at h₁ h₂
    omega
  have hEn : number E = 4 := by
    have hh := hF.1.2.2
    rw [hFC,source_number] at hh
    change number E + 10 = 14 at hh
    omega
  have hEe : ∀ v, Even (Nat.card (E.neighborSet v)) := hF.1.2.1
  have hEC : Nat.card E.edgeSet = 20 := by
    have hh := Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hF.1.1)
    rw [← SimpleGraph.edgeFinset_sdiff] at hh
    have hs := BipartiteLower.complete_edge_card (A := Fin 3) (B := Fin 10)
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_fin] at hh hs
    change Nat.card source.edgeSet = 30 at hs
    change Nat.card E.edgeSet + Nat.card F.edgeSet = Nat.card source.edgeSet at hh
    omega
  have hsat : ∃ a : Fin 3, Nat.card (E.neighborSet (.inl a)) = 8 := by
    by_contra! hn
    have hd (a : Fin 3) : Nat.card (E.neighborSet (.inl a)) ≤ 6 := by
      have hb := StarCore.number_degree_bound E (.inl a)
      have he := Nat.even_iff.mp (hEe (.inl a))
      have hh := hn a
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hb
      rw [hEn] at hb
      omega
    have hs := (BipartiteLower.bipartite_edge_sums E
      (show E ≤ completeBipartiteGraph (Fin 3) (Fin 10) from sdiff_le)).1
    simp only [SimpleGraph.edgeFinset_card, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hs
    have hb : (∑ a : Fin 3, Nat.card (E.neighborSet (.inl a))) ≤ 18 := by
      calc
        _ ≤ ∑ _a : Fin 3, 6 := Finset.sum_le_sum (fun a _ => hd a)
        _ = _ := by simp
    omega
  obtain ⟨a,ha⟩ := hsat
  intro hm
  change EvenMinimal E at hm
  have hacy : (E.induce ({Sum.inl a}ᶜ : Set V)).IsAcyclic := by
    apply (StarCore.EvenMinimal.saturated_vertex hm ?_ (Sum.inl a) ?_).1
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hEe
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
        hEn] using ha
  letI : Nonempty ({Sum.inl a}ᶜ : Set V) := ⟨⟨Sum.inr 0,by simp⟩⟩
  have hf := acyclic_card_edges_lt (E.induce ({Sum.inl a}ᶜ : Set V)) hacy
  have hv : Fintype.card ({Sum.inl a}ᶜ : Set V) = 12 := by
    rw [Fintype.card_compl_set]
    simp [V]
  have he : (E.induce ({Sum.inl a}ᶜ : Set V)).edgeFinset.card + E.degree (.inl a) =
      E.edgeFinset.card := by
    rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
      SimpleGraph.card_edgeFinset_deleteIncidenceSet]
    have hb := E.degree_le_card_edgeFinset (.inl a)
    simp only [SimpleGraph.edgeFinset_card, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hb ⊢
    omega
  simp only [SimpleGraph.edgeFinset_card, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hf hv he
  omega

lemma no_best_even_minimal : ¬ ∃ F : SimpleGraph V,
    Best source F ∧ EvenMinimal (source \ F) := by
  rintro ⟨F,hF,hm⟩
  exact any_best_not_evenMinimal hF hm

/-- The obstruction includes global minimality of the source, rather than
mere saturation of its decomposition number. -/
lemma obstruction : EdgeHull.Minimal source ∧
    ¬ ∃ F : SimpleGraph V, Best source F ∧ EvenMinimal (source \ F) :=
  ⟨source_minimal,no_best_even_minimal⟩

lemma optimal_singleton_count {F : SimpleGraph V} (hF : Optimal source F) :
    Nat.card F.edgeSet = 10 := by
  let E := source \ F
  have hlo := forest_best.2 F hF
  rw [forest_card] at hlo
  have hnum := hF.2.2
  rw [source_number] at hnum
  change number E + Nat.card F.edgeSet = 14 at hnum
  have hcard : Nat.card E.edgeSet + Nat.card F.edgeSet = 30 := by
    have h := Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hF.1)
    rw [← SimpleGraph.edgeFinset_sdiff] at h
    have hs := BipartiteLower.complete_edge_card (A := Fin 3) (B := Fin 10)
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_fin] at h hs
    change Nat.card source.edgeSet = 30 at hs
    change Nat.card E.edgeSet + Nat.card F.edgeSet = Nat.card source.edgeSet at h
    exact h.trans hs
  have hb : Nat.card E.edgeSet ≤ 6 * number E := by
    have he := (BipartiteLower.bipartite_edge_sums E
      (show E ≤ completeBipartiteGraph (Fin 3) (Fin 10) from sdiff_le)).1
    simp only [SimpleGraph.edgeFinset_card, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at he
    have hd (a : Fin 3) : Nat.card (E.neighborSet (.inl a)) ≤ 2 * number E := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using StarCore.number_degree_bound E (.inl a)
    rw [he]
    calc
      _ ≤ ∑ _a : Fin 3, 2 * number E := Finset.sum_le_sum (fun a _ => hd a)
      _ = _ := by simp; omega
  omega

lemma every_optimal_best {F : SimpleGraph V} (hF : Optimal source F) : Best source F := by
  refine ⟨hF,?_⟩
  intro R hR
  rw [optimal_singleton_count hF,optimal_singleton_count hR]

lemma any_optimal_not_evenMinimal {F : SimpleGraph V} (hF : Optimal source F) :
    ¬ EvenMinimal (source \ F) :=
  any_best_not_evenMinimal (every_optimal_best hF)

/-- Even allowing a different optimal singleton forest cannot produce an
 even-minimal remainder in this globally minimal graph. -/
lemma optimal_obstruction : EdgeHull.Minimal source ∧
    ¬ ∃ F : SimpleGraph V, Optimal source F ∧ EvenMinimal (source \ F) := by
  refine ⟨source_minimal,?_⟩
  rintro ⟨F,hF,hm⟩
  exact any_optimal_not_evenMinimal hF hm

end Erdos184Work.NoBestMinimalRemainder
#print axioms Erdos184Work.NoBestMinimalRemainder.obstruction
#print axioms Erdos184Work.NoBestMinimalRemainder.optimal_obstruction
