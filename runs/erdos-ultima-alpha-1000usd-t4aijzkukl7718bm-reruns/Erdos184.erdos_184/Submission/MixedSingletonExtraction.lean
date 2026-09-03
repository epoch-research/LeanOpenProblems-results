import Submission.MixedOptimalExtension
import Submission.MixedSevenCritical

/-! Singleton-maximal optima need not be preserved by exact-count critical
extraction. This obstruction is not a disproof of Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.MixedSingletonExtraction
open MixedCritical MixedCriticalNonforest RankCritical
set_option maxHeartbeats 1500000

lemma maximumSingles_forest {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hf : H.IsAcyclic) : maximumSingles H = number H := by
  obtain ⟨D,hc,hd,hcard,hs⟩ := maximumSingles_spec H
  have he : ∀ J ∈ D, J.edgeSet.ncard = 1 := by
    intro J hJ
    rcases hc J hJ with hcy | hedge
    · obtain ⟨e,he,hn⟩ := cycle_has_edge_outside_forest H hf J hcy.1 (by
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using hcy.2 v)
      exact (hn (J.edgeSet_subset he)).elim
    · rwa [coe_edgeFinset_card] at hedge
  have hsD : singles D = D := by
    ext J
    simp only [singles,Finset.mem_filter]
    exact ⟨fun h => h.1,fun h => ⟨h,he J h⟩⟩
  rw [hsD,hcard] at hs
  exact hs.symm

def A : SimpleGraph V := G.deleteEdges {s(0,1)}
instance : DecidableRel A.Adj := by unfold A; infer_instance

lemma A_number : number A = 6 := by
  have h := MixedSevenCritical.graph_critical.delete_edge_number
    (show G.Adj 0 1 by decide)
  change number A + 1 = 7 at h
  omega

lemma A_edges : A.edgeFinset.card = 14 := by decide

lemma A_connected : A.Connected := by
  have h : ∀ v : V, v ≠ 2 → A.Adj 2 v := by decide
  have hr (v : V) : A.Reachable 2 v := by
    by_cases hv : v = 2
    · subst v; exact Reachable.refl _
    · exact (h v hv).reachable
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

lemma A_rank : graphRank A = 6 := by
  have h := RankCriticalPartitions.connected_rank A_connected
  simpa using h

lemma A_singletons_le_four : maximumSingles A ≤ 4 := by
  obtain ⟨D,hc,hd,hcard,hs⟩ := maximumSingles_spec A
  have h := partition_edge_bound A D hc hd
  have he := A_edges
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at he
  rw [A_number] at hcard
  simp only [Fintype.card_fin] at h
  have hb := singles_card_le D
  omega

lemma critical_extraction_increases_singletons :
    ∃ T : SimpleGraph V, T ≤ A ∧ MixedCritical.IsCritical 6 T ∧
      number T = number A ∧ maximumSingles A < maximumSingles T := by
  obtain ⟨T,hTA,hf,hr⟩ := exists_forest_same_rank A
  have hn : number T = 6 := by
    rw [forest_number_eq_rank T hf,hr,A_rank]
  have hcrit := forest_critical T hf
  have hm := forest_number T hf
  have hs := maximumSingles_forest T hf
  have ha := A_singletons_le_four
  refine ⟨T,hTA,?_,hn.trans A_number.symm,?_⟩
  · rwa [← hm,hn] at hcrit
  · omega

lemma not_singleton_monotone_under_exact_critical_extraction :
    ¬ (∀ (B T : SimpleGraph V) (k : ℕ), T ≤ B → MixedCritical.IsCritical k T →
      number T = number B → maximumSingles T ≤ maximumSingles B) := by
  intro h
  obtain ⟨T,hTA,hcrit,hn,hs⟩ := critical_extraction_increases_singletons
  exact (not_le_of_gt hs) (h A T 6 hTA hcrit hn)

end Erdos184.MixedSingletonExtraction
