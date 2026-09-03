import Submission.GreedyBatchPromotions
import Submission.GreedyBatchGraphLoss

/-! Deterministic simultaneous residual-rank accounting for a conservative
batch. Old-edge losses and every higher-rank promotion are retained. -/
namespace Erdos773.GreedyBatchDegreeStep
open Finset HypergraphDegreeTrim UniformLayerRegularization GreedyBatchState
open GreedyBatchPromotions
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def sources (H : Finset (Finset α)) (R : Finset α) (j : ℕ) (x : α) : Finset (Finset α) :=
  H.filter (fun e => e \ R⊆carrier H R ∧ (e \ R).card=j ∧ x∈e \ R)

def oldCount (H : Finset (Finset α)) (R : Finset α) (j : ℕ) (x : α) : ℕ :=
  ((incidentLayer H j x).filter (fun e => e⊆carrier H R)).card

lemma degree_le_sources (H : Finset (Finset α)) (R : Finset α) (j : ℕ) (x : α) :
    degree (layer (next H R) j) x≤(sources H R j x).card := by
  have hs : (layer (next H R) j).filter (fun e => x∈e) ⊆
      (sources H R j x).image (fun e => e \ R) := by
    intro f hf
    obtain ⟨hf,hx⟩ := mem_filter.mp hf
    obtain ⟨hf,hj⟩ := mem_filter.mp hf
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    obtain ⟨he,hlo,hQ⟩ := mem_filter.mp he
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hQ,hj,hx⟩,rfl⟩
  exact (card_le_card hs).trans card_image_le

lemma same_rank_le_old (H : Finset (Finset α)) (R : Finset α) (j : ℕ) (x : α) :
    ((sources H R j x).filter (fun e => e.card=j)).card≤oldCount H R j x := by
  apply card_le_card
  intro e he
  obtain ⟨he,her⟩ := mem_filter.mp he
  obtain ⟨he,hQ,hj,hx⟩ := mem_filter.mp he
  have heq : e \ R=e := eq_of_subset_of_card_le sdiff_subset (by omega)
  rw [heq] at hQ hx
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨he,her⟩,hx⟩,hQ⟩

lemma higher_rank_le_cost (H : Finset (Finset α)) (R : Finset α) (j r : ℕ) (x : α)
    (hjr : j≤r) :
    ((sources H R j x).filter (fun e => e.card=r)).card≤cost H x r (r-j) R := by
  have heq : j+(r-j)=r := Nat.add_sub_of_le hjr
  have hs : (sources H R j x).filter (fun e => e.card=r) ⊆
      (layer H (j+(r-j))).filter (fun e => x∈e \ R ∧ (e \ R).card=j) := by
    intro e he
    obtain ⟨he,her⟩ := mem_filter.mp he
    obtain ⟨he,hQ,hj,hx⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨he,by rwa [heq]⟩,hx,hj⟩
  have hh := (card_le_card hs).trans (contraction_count H R x j (r-j))
  rwa [heq] at hh

lemma lower_rank_empty (H : Finset (Finset α)) (R : Finset α) (j r : ℕ) (x : α)
    (hrj : r<j) : (sources H R j x).filter (fun e => e.card=r)=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,her⟩ := mem_filter.mp he
  obtain ⟨he,hQ,hj,hx⟩ := mem_filter.mp he
  have hh := card_le_card (sdiff_subset : e \ R⊆e)
  omega

def rankBudget (H : Finset (Finset α)) (R : Finset α) (x : α) (j r : ℕ) : ℕ :=
  if r=j then oldCount H R j x else if j<r then cost H x r (r-j) R else 0

/-- A finite update inequality, without any asserted typical profile. -/
theorem degree_step (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x : α) (j : ℕ) :
    degree (layer (next H R) j) x≤∑ r∈range 5, rankBudget H R x j r := by
  apply (degree_le_sources H R j x).trans
  have he := card_eq_sum_card_fiberwise (s := sources H R j x) (t := range 5)
    (f := Finset.card) (fun e he => mem_range.mpr (by have := hH e (mem_filter.mp he).1; omega))
  rw [he]
  apply sum_le_sum
  intro r hr
  unfold rankBudget
  split_ifs with hrj hjr
  · subst r
    exact same_rank_le_old H R j x
  · exact higher_rank_le_cost H R j r x hjr.le
  · rw [lower_rank_empty H R j r x (by omega),card_empty]

/-- Rank four to rank two is charged with a two-mark witness. -/
theorem degree_two (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x : α) :
    degree (layer (next H R) 2) x≤oldCount H R 2 x+cost H x 3 1 R+cost H x 4 2 R := by
  simpa [sum_range_succ,rankBudget] using degree_step H R hH x 2

theorem degree_three (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x : α) :
    degree (layer (next H R) 3) x≤oldCount H R 3 x+cost H x 4 1 R := by
  simpa [sum_range_succ,rankBudget] using degree_step H R hH x 3

theorem degree_four (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x : α) :
    degree (layer (next H R) 4) x≤oldCount H R 4 x := by
  simpa [sum_range_succ,rankBudget] using degree_step H R hH x 4

#print axioms degree_step
#print axioms degree_two
#print axioms degree_three
#print axioms degree_four
end
end Erdos773.GreedyBatchDegreeStep
