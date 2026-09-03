import Submission.BestTransferRawLower
import Submission.BestTransferRawUpper

/-! A full transfer along a Best singleton edge can strictly lower the raw
cycle-and-edge decomposition number. This is not a hull-loss theorem or a
disproof of Erdős184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.BestTransferRaw
open Critical SingletonExchange
lemma source_number : number source = 13 := by
  have hu := split_lower_bound forest_le_source
  change number source ≤ number evenSource + Nat.card forest.edgeSet at hu
  rw [forest_card] at hu
  have he := evenSource_upper
  have hl := source_number_ge_thirteen
  omega

lemma forest_best : Best source forest := by
  have hu := split_lower_bound forest_le_source
  have hn : number evenSource = 6 := by
    change number source ≤ number evenSource + Nat.card forest.edgeSet at hu
    rw [source_number,forest_card] at hu
    exact Nat.le_antisymm evenSource_upper (by omega)
  refine ⟨⟨forest_le_source,source_even,?_⟩,?_⟩
  · change number evenSource + Nat.card forest.edgeSet = number source
    rw [hn,forest_card,source_number]
  · intro T hT
    rw [forest_card]
    have hp (v : V) (hv : v ∈ oddVertices) : 1 ≤ T.degree v := by
      have h := degree_sdiff_add source T hT.1 v
      have he := Nat.even_iff.mp (hT.2.1 v)
      have ho := Nat.odd_iff.mp (odd_vertices v hv)
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ho ⊢
      omega
    have hs := Finset.sum_le_sum (s := oddVertices) (fun v hv => hp v hv)
    have hb := ParityDegreeLower.independent_degree_sum_le T oddVertices
      (fun u hu v hv huv => odd_independent u hu v hv (hT.1 huv))
    simp only [Finset.sum_const,smul_eq_mul,mul_one,odd_card] at hs
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hb
    exact hs.trans hb

lemma target_upper : number target ≤ 11 := by
  have hu := split_lower_bound forest_le_target
  change number target ≤ number evenTarget + Nat.card forest.edgeSet at hu
  rw [forest_card] at hu
  have ht := evenTarget_upper
  omega

lemma raw_transfer_loss : Best source forest ∧ forest.Adj 0 9 ∧
    number (Compression.transfer source 0 9) + 1 < number source := by
  refine ⟨forest_best,forest_pair,?_⟩
  rw [transfer_eq,source_number]
  have h := target_upper
  omega

end Erdos184Work.BestTransferRaw
#print axioms Erdos184Work.BestTransferRaw.source_number
#print axioms Erdos184Work.BestTransferRaw.forest_best
#print axioms Erdos184Work.BestTransferRaw.raw_transfer_loss
