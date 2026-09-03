import Submission.OrderedCutBudget
import Submission.FractionalSaturation

/-! Ordered-cut lower bounds hold for exact fractional cycle partitions too.
This is a lower-bound tool, not a proof of Erdős 184. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalOrderedCuts
open FractionalCycles OrderedCutBudget RankCriticalCuts RankCriticalPartitions
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
set_option maxHeartbeats 1000000

lemma representative_degree_le_image (f : V → Fin n) (r : Fin n → V)
    (hr : Function.RightInverse r f) (H : CyclePiece G) :
    (∑ j, H.val.degree (r j)) ≤ 2 * (f '' H.val.verts).ncard := by
  let S := Finset.univ.filter (fun j => r j ∈ H.val.verts)
  have hs : S ⊆ (f '' H.val.verts).toFinset := by
    intro j hj
    exact Set.mem_toFinset.mpr ⟨r j,(Finset.mem_filter.mp hj).2,hr j⟩
  have hb := Finset.card_le_card hs
  have he : (∑ j, H.val.degree (r j)) = 2 * S.card := by
    simp only [cycle_piece_degree]
    simp only [S,Finset.card_filter,Finset.mul_sum,mul_ite,Nat.mul_one,Nat.mul_zero]
  rw [he,Set.ncard_eq_toFinset_card']
  omega

lemma cycle_degree_budget (f : V → Fin n) (r : Fin n → V)
    (hr : Function.RightInverse r f) (H : CyclePiece G) :
    (∑ j, H.val.degree (r j)) ≤ 2 +
      ∑ j, (H.val.edgeSet \ (monochromatic G (threshold f j)).edgeSet).ncard := by
  have hrep := representative_degree_le_image f r hr H
  have himg := image_card_le_crossed_add_one f H.val H.property.1
  have hcut : 2 * (crossedThresholds G f H.val).card ≤
      ∑ j, (H.val.edgeSet \ (monochromatic G (threshold f j)).edgeSet).ncard := by
    rw [crossedThresholds,Finset.card_filter,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    split_ifs with hj
    · simpa using cycle_omits_zero_or_two G _ (monochromatic_closed G (threshold f j))
        H.val H.property.1 H.property.2 hj
    · simp
  omega

lemma weighted_cut_sum (t : CyclePiece G → ℝ) (ht : IsFractionalPartition G t)
    (R : SimpleGraph V) :
    (∑ H : CyclePiece G, t H * ((H.val.edgeSet \ R.edgeSet).ncard : ℝ)) =
      ((G.edgeSet \ R.edgeSet).ncard : ℝ) := by
  have hh := weighted_edge_test G t ht (fun e => if e ∉ R.edgeSet then 1 else 0)
  simpa only [cycle_test_diff,edge_test_diff] using hh

/-- The ordinary ordered-cut lower bound needs no integrality: exact fractional
coverage suffices. In particular, examples certified only by this lower bound
need not have any integral/fractional gap. -/
lemma degree_budget (f : V → Fin n) (r : Fin n → V)
    (hr : Function.RightInverse r f) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) :
    (∑ j, (G.degree (r j) : ℝ)) ≤ 2 * (∑ H, t H) + (variation G f : ℝ) := by
  have hp (H : CyclePiece G) :
      (∑ j, (H.val.degree (r j) : ℝ)) ≤ 2 +
        ∑ j, ((H.val.edgeSet \ (monochromatic G (threshold f j)).edgeSet).ncard : ℝ) := by
    exact_mod_cast cycle_degree_budget f r hr H
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun H _ =>
    mul_le_mul_of_nonneg_left (hp H) (ht.1 H))
  have hl : (∑ H : CyclePiece G, t H * ∑ j, (H.val.degree (r j) : ℝ)) =
      ∑ j, (G.degree (r j) : ℝ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [weighted_degree_sum G t ht]
  have hc : (∑ H : CyclePiece G, t H * ∑ j,
      ((H.val.edgeSet \ (monochromatic G (threshold f j)).edgeSet).ncard : ℝ)) =
      (variation G f : ℝ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [weighted_cut_sum t ht]
    simp only [variation,Nat.cast_sum]
  rw [hl] at hh
  simp_rw [mul_add] at hh
  rw [Finset.sum_add_distrib,hc,← Finset.sum_mul] at hh
  nlinarith

end Erdos184.FractionalOrderedCuts
