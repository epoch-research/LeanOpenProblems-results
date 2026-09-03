import Submission.GreedyLinearLocal

/-!
One-step local estimates without linearity of the original hypergraph.
Original-edge multiplicities are retained. These estimates do not yet
supply a nonlinear tracking or running-time theorem.
-/
namespace Erdos773.GreedyCodegreeLocal
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearLocal
open FourUniformRegularization
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma promoted_card_le_codegree {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (I : Finset α) (j : ℕ) {u w : α} (huw : u ≠ w) :
    (localPromoted H I j u w).card ≤ K := by
  have hs : localPromoted H I j u w ⊆ H.filter (fun e => u ∈ e ∧ w ∈ e) := by
    intro e he
    obtain ⟨he,hu⟩ := mem_filter.mp he
    obtain ⟨he,hw,_⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_sdiff.mp hu).1,(mem_sdiff.mp hw).1⟩
  exact (card_le_card hs).trans (hK u w huw)

lemma lost_card_le_codegree_closes {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) (j : ℕ) :
    (localLost H I j u w).card ≤ K*((closes H I w).card+1) := by
  have huD : u ∉ insert w (closes H I w) := by
    rw [available_insert hw] at hu
    exact (mem_sdiff.mp hu).2
  have hs : localLost H I j u w ⊆ (insert w (closes H I w)).biUnion
      (fun x => H.filter (fun e => u ∈ e ∧ x ∈ e)) := by
    intro e he
    obtain ⟨he,hur⟩ := mem_filter.mp he
    obtain ⟨he,hnot⟩ := mem_filter.mp he
    obtain ⟨x,hx,hx'⟩ := not_subset.mp hnot
    have hxA := (mem_filter.mp he).2.1 hx
    have hxD : x ∈ insert w (closes H I w) := by
      by_contra h
      apply hx'
      rw [available_insert hw]
      exact mem_sdiff.mpr ⟨hxA,h⟩
    exact mem_biUnion.mpr ⟨x,hxD,mem_filter.mpr
      ⟨(mem_filter.mp he).1,(mem_sdiff.mp hur).1,(mem_sdiff.mp hx).1⟩⟩
  calc
    _ ≤ ((insert w (closes H I w)).biUnion
        (fun x => H.filter (fun e => u ∈ e ∧ x ∈ e))).card := card_le_card hs
    _ ≤ ∑ x ∈ insert w (closes H I w), (H.filter (fun e => u ∈ e ∧ x ∈ e)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ insert w (closes H I w), K := by
      apply sum_le_sum
      intro x hx
      exact hK u x (fun h => huD (h ▸ hx))
    _ = _ := by simp [card_insert_of_notMem (notMem_closes_self H I w), Nat.mul_comm]

/-- A bounded local increment as long as the tracked vertex survives. It is
    not asserted across the death of that vertex. -/
theorem incident_increment_bound {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) (j : ℕ) :
    |((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card| ≤
      (K:ℝ)*((closes H I w).card+1) := by
  have huw : u ≠ w := by
    intro h
    exact (mem_available.mp hu).1 (by simp [h])
  have hb := incident_card_step hw huw j
  have hl := lost_card_le_codegree_closes K hK hw hu j
  have hp := promoted_card_le_codegree K hK I j huw
  have hbR : ((incident H (insert w I) j u).card:ℝ)+(localLost H I j u w).card =
      (incident H I j u).card+(localPromoted H I j u w).card := by exact_mod_cast hb
  have hlR : ((localLost H I j u w).card:ℝ) ≤ (K:ℝ)*((closes H I w).card+1) := by exact_mod_cast hl
  have hpR : ((localPromoted H I j u w).card:ℝ) ≤ K := by exact_mod_cast hp
  have hnL : (0:ℝ) ≤ (localLost H I j u w).card := by positivity
  have hnP : (0:ℝ) ≤ (localPromoted H I j u w).card := by positivity
  have hnC : (0:ℝ) ≤ (closes H I w).card := by positivity
  have hKn : (0:ℝ) ≤ K := by positivity
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- The exact multiplicity correction among common residual neighbors. -/
def lostDuplicate (H : Finset (Finset α)) (I : Finset α) (u w : α) : ℕ :=
  ∑ x ∈ closes H I u ∩ closes H I w, ((pairReps H I u x).card-1)

/-- The linear identity becomes an exact identity with a nonnegative,
    explicitly counted duplicate correction. -/
theorem localLost_two_card {H : Finset (Finset α)}
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) :
    (localLost H I 2 u w).card = commonDegree H I u w + lostDuplicate H I u w := by
  rw [localLost_two_eq hw hu]
  have hd : ((closes H I u ∩ closes H I w : Finset α):Set α).PairwiseDisjoint
      (pairReps H I u) := by
    intro x hx y hy hxy
    apply disjoint_left.mpr
    intro e hex hey
    obtain ⟨_,hux,heq⟩ := mem_filter.mp hex
    obtain ⟨_,_,hey⟩ := mem_filter.mp hey
    have hx : x ∈ ({u,y}:Finset α) := by rw [← hey,heq]; simp
    have hh := (mem_insert.mp hx).resolve_left hux.symm
    exact hxy (mem_singleton.mp hh)
  rw [card_biUnion hd]
  have hc (x : α) (hx : x ∈ closes H I u ∩ closes H I w) :
      (pairReps H I u x).card = 1+((pairReps H I u x).card-1) := by
    have hx := (mem_inter.mp hx).1
    have hn := card_pos.mpr ((pairReps_nonempty_iff (closes_subset H I u hx)).mpr hx)
    omega
  rw [sum_congr rfl hc, sum_add_distrib]
  simp [commonDegree,lostDuplicate]

lemma lostDuplicate_le (H : Finset (Finset α)) (I : Finset α) (u w : α) :
    lostDuplicate H I u w ≤ duplicateExcess H I u := by
  unfold lostDuplicate duplicateExcess
  apply sum_le_sum_of_subset_of_nonneg inter_subset_left
  intros
  exact Nat.zero_le _

lemma lostDuplicate_le_common {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (I : Finset α) (u w : α) :
    lostDuplicate H I u w ≤ (K-1)*commonDegree H I u w := by
  calc
    _ ≤ ∑ _x ∈ closes H I u ∩ closes H I w, (K-1) := by
      unfold lostDuplicate
      apply sum_le_sum
      intro x hx
      have hux := (mem_closes.mp (mem_inter.mp hx).1).2.1.symm
      exact Nat.sub_le_sub_right ((pairReps_card_le H I u x).trans (hK u x hux)) 1
    _ = _ := by simp [commonDegree, Nat.mul_comm]

/-- The surviving two-degree is controlled by actual common neighbors plus
    the explicit duplicate correction, rather than treating every original
    pair representative as a different closed vertex. -/
theorem incident_two_increment_interval {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) :
    -(commonDegree H I u w:ℝ)-(lostDuplicate H I u w:ℝ) ≤
      ((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card ∧
    ((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card ≤
      K-(commonDegree H I u w:ℝ)-(lostDuplicate H I u w:ℝ) := by
  have huw : u ≠ w := by
    intro h
    exact (mem_available.mp hu).1 (by simp [h])
  have hb := incident_card_step hw huw 2
  rw [localLost_two_card hw hu] at hb
  have hp := promoted_card_le_codegree K hK I 2 huw
  have hbR : ((incident H (insert w I) 2 u).card:ℝ)+
      ((commonDegree H I u w:ℝ)+(lostDuplicate H I u w:ℝ)) =
      (incident H I 2 u).card+(localPromoted H I 2 u w).card := by exact_mod_cast hb
  have hpR : ((localPromoted H I 2 u w).card:ℝ) ≤ K := by exact_mod_cast hp
  have hnP : (0:ℝ) ≤ (localPromoted H I 2 u w).card := by positivity
  constructor <;> linarith only [hbR,hpR,hnP]

theorem incident_two_increment_bound {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) (C E : ℕ)
    (hC : commonDegree H I u w ≤ C) (hE : duplicateExcess H I u ≤ E) :
    |((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card| ≤
      (K:ℝ)+C+E := by
  obtain ⟨hl,hh⟩ := incident_two_increment_interval K hK hw hu
  have hCR : (commonDegree H I u w:ℝ) ≤ C := by exact_mod_cast hC
  have hER : (lostDuplicate H I u w:ℝ) ≤ E := by
    exact_mod_cast (lostDuplicate_le H I u w).trans hE
  have hK0 : (0:ℝ) ≤ K := by positivity
  have hC0 : (0:ℝ) ≤ C := by positivity
  have hE0 : (0:ℝ) ≤ E := by positivity
  have hc0 : (0:ℝ) ≤ commonDegree H I u w := by positivity
  have he0 : (0:ℝ) ≤ lostDuplicate H I u w := by positivity
  exact abs_le.mpr ⟨by linarith only [hl,hCR,hER,hK0],
    by linarith only [hh,hc0,he0,hC0,hE0]⟩

#print axioms promoted_card_le_codegree
#print axioms lost_card_le_codegree_closes
#print axioms incident_increment_bound
#print axioms localLost_two_card
#print axioms lostDuplicate_le
#print axioms lostDuplicate_le_common
#print axioms incident_two_increment_interval
#print axioms incident_two_increment_bound
end
end Erdos773.GreedyCodegreeLocal
