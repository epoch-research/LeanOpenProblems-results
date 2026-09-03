import Submission.GreedyHypergraphState
import Submission.Hypergraph

/-! A conservative batched greedy state. Rejected marked vertices remain
outside the next carrier. This prevents alteration from reopening constraints.
The expectation identities here do not assert local profile concentration. -/
namespace Erdos773.GreedyBatchState
open Finset GreedyHypergraphState
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

def discarded (H : Finset (Finset α)) (R : Finset α) : Finset α :=
  (H.filter (·⊆R)).biUnion id

def chosen (H : Finset (Finset α)) (R : Finset α) : Finset α := R \ discarded H R

def closed (H : Finset (Finset α)) (R : Finset α) : Finset α :=
  H.biUnion (fun e => e.filter (fun v => e.erase v⊆R))

def discardCost (H : Finset (Finset α)) (R : Finset α) : ℕ :=
  ∑ e∈H, if e⊆R then e.card else 0

def closureCost (H : Finset (Finset α)) (R : Finset α) : ℕ :=
  ∑ e∈H, (e.filter (fun v => e.erase v⊆R)).card

lemma chosen_subset (H : Finset (Finset α)) (R : Finset α) : chosen H R⊆R := sdiff_subset

lemma mem_closed {H : Finset (Finset α)} {R : Finset α} {x : α} :
    x∈closed H R ↔ ∃ e∈H, x∈e ∧ e.erase x⊆R := by
  simp [closed]

/-- All vertices of any fully marked edge are rejected. -/
lemma chosen_independent (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.Nonempty) : Independent H (chosen H R) := by
  intro e he hesub
  obtain ⟨x,hx⟩ := hH e he
  have hxJ := hesub hx
  have hxD : x∈discarded H R := mem_biUnion.mpr
    ⟨e,mem_filter.mpr ⟨he,hesub.trans (chosen_subset H R)⟩,hx⟩
  exact (mem_sdiff.mp hxJ).2 hxD

lemma chosen_card (H : Finset (Finset α)) (R : Finset α) :
    R.card≤(chosen H R).card+discardCost H R := by
  have hs : R⊆chosen H R∪discarded H R := by
    intro a ha
    by_cases hd : a∈discarded H R
    · exact mem_union_right _ hd
    · exact mem_union_left _ (mem_sdiff.mpr ⟨ha,hd⟩)
  have hc : (discarded H R).card≤discardCost H R := by
    have hh := card_biUnion_le (s := H.filter (·⊆R)) (t := id)
    simpa only [discardCost,sum_filter] using hh
  exact (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_left hc _))

variable [Fintype α]

def carrier (H : Finset (Finset α)) (R : Finset α) : Finset α :=
  univ \ (R∪closed H R)

lemma mem_carrier {H : Finset (Finset α)} {R : Finset α} {x : α} :
    x∈carrier H R ↔ x∉R ∧ x∉closed H R := by simp [carrier]

lemma carrier_disjoint (H : Finset (Finset α)) (R : Finset α) : Disjoint (carrier H R) R :=
  disjoint_left.mpr (fun _ hx hxR => (mem_carrier.mp hx).1 hxR)

lemma carrier_card (H : Finset (Finset α)) (R : Finset α) :
    Fintype.card α≤(carrier H R).card+R.card+closureCost H R := by
  have hh := card_sdiff_add_card_eq_card (subset_univ (R∪closed H R))
  rw [card_univ] at hh
  have hc : (closed H R).card≤closureCost H R := card_biUnion_le
  have hu := card_union_le R (closed H R)
  change (carrier H R).card+(R∪closed H R).card=Fintype.card α at hh
  omega

/-- Empty residuals are omitted: they are already dealt with by alteration.
Singleton residuals cannot meet the conservative carrier. -/
def next (H : Finset (Finset α)) (R : Finset α) : Finset (Finset α) :=
  (H.filter (fun e => 2≤(e \ R).card ∧ e \ R⊆carrier H R)).image (fun e => e \ R)

lemma next_subset {H : Finset (Finset α)} {R f : Finset α} (hf : f∈next H R) :
    f⊆carrier H R := by
  obtain ⟨e,he,rfl⟩ := mem_image.mp hf
  exact (mem_filter.mp he).2.2

lemma next_rank {H : Finset (Finset α)} {R : Finset α} (hH : ∀ e∈H, e.card≤4)
    {f : Finset α} (hf : f∈next H R) : 2≤f.card ∧ f.card≤4 := by
  obtain ⟨e,he,rfl⟩ := mem_image.mp hf
  obtain ⟨he,hlo,hQ⟩ := mem_filter.mp he
  exact ⟨hlo,(card_le_card sdiff_subset).trans (hH e he)⟩

/-- A sufficient residual system for genuine extensions. The tentative
mark set itself need not be independent. -/
theorem extension {H : Finset (Finset α)} (R : Finset α)
    (hH : ∀ e∈H, e.Nonempty) {A : Finset α} (hA : A⊆carrier H R)
    (hi : Independent (next H R) A) : Independent H (chosen H R∪A) := by
  intro e he hesub
  have hres : e \ R⊆A := by
    intro x hx
    rcases mem_union.mp (hesub (mem_sdiff.mp hx).1) with hxJ | hxA
    · exact ((mem_sdiff.mp hx).2 (chosen_subset H R hxJ)).elim
    · exact hxA
  have hnon : (e \ R).Nonempty := by
    apply sdiff_nonempty.mpr
    intro heR
    apply chosen_independent H R hH e he
    intro x hx
    rcases mem_union.mp (hesub hx) with hxJ | hxA
    · exact hxJ
    · exact ((mem_carrier.mp (hA hxA)).1 (heR hx)).elim
  have hnotone : (e \ R).card≠1 := by
    intro h1
    obtain ⟨x,hx⟩ := card_eq_one.mp h1
    have hxe : x∈e \ R := by rw [hx]; simp
    have hxQ := hA (hres hxe)
    apply (mem_carrier.mp hxQ).2
    apply mem_closed.mpr
    refine ⟨e,he,(mem_sdiff.mp hxe).1,?_⟩
    intro y hy
    by_contra hyR
    have hm : y∈e \ R := mem_sdiff.mpr ⟨(mem_erase.mp hy).2,hyR⟩
    rw [hx] at hm
    exact (mem_erase.mp hy).1 (mem_singleton.mp hm)
  have hlo : 2≤(e \ R).card := by have := card_pos.mpr hnon; omega
  exact hi (e \ R) (mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hlo,hres.trans hA⟩,rfl⟩) hres

lemma extension_card (H : Finset (Finset α)) (R : Finset α) {A : Finset α}
    (hA : A⊆carrier H R) : (chosen H R∪A).card=(chosen H R).card+A.card := by
  apply card_union_of_disjoint
  exact ((carrier_disjoint H R).mono hA (chosen_subset H R)).symm

lemma discardCost_expectation (H : Finset (Finset α)) (p : ℝ) :
    (∑ f : α → Bool, trialWeight p f*(discardCost H (selected f):ℝ)) =
      ∑ e∈H, (e.card:ℝ)*p^e.card := by
  simp only [discardCost,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  calc
    _ = (e.card:ℝ)*(∑ f : α → Bool, if e⊆selected f then trialWeight p f else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro f hf
      split_ifs <;> ring
    _ = _ := by rw [sum_trialWeight_contains]

lemma closureCost_expectation (H : Finset (Finset α)) (p : ℝ) :
    (∑ f : α → Bool, trialWeight p f*(closureCost H (selected f):ℝ)) =
      ∑ e∈H, (e.card:ℝ)*p^(e.card-1) := by
  simp only [closureCost,Nat.cast_sum,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  have hc (f : α → Bool) : ((e.filter (fun v => e.erase v⊆selected f)).card:ℝ)=
      ∑ v∈e, if e.erase v⊆selected f then (1:ℝ) else 0 := by
    rw [← sum_filter]
    simp
  simp_rw [hc,mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ v∈e, p^(e.erase v).card := by
      apply sum_congr rfl
      intro v hv
      have hh := sum_trialWeight_contains p (e.erase v)
      convert hh using 1
      apply sum_congr rfl
      intro f hf
      split_ifs <;> simp
    _ = ∑ _v∈e, p^(e.card-1) := sum_congr rfl (fun v hv => by rw [card_erase_of_mem hv])
    _ = _ := by simp

/-- Expected reward for one batched stage followed by a hypothetical
residual density δ. The local-profile and subsequent density bounds are
not asserted by this lemma. -/
theorem reward_expectation (H : Finset (Finset α)) (p δ : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hδ : 0≤δ) :
    p*Fintype.card α-(∑ e∈H, (e.card:ℝ)*p^e.card)+
      δ*((1-p)*Fintype.card α-∑ e∈H, (e.card:ℝ)*p^(e.card-1)) ≤
      ∑ f : α → Bool, trialWeight p f*
        ((chosen H (selected f)).card+δ*(carrier H (selected f)).card) := by
  have hpoint (f : α → Bool) :
      ((selected f).card:ℝ)-(discardCost H (selected f):ℝ)+
        δ*(Fintype.card α-(selected f).card-(closureCost H (selected f):ℝ)) ≤
        (chosen H (selected f)).card+δ*(carrier H (selected f)).card := by
    have hJ : ((selected f).card:ℝ)≤(chosen H (selected f)).card+(discardCost H (selected f):ℝ) := by
      exact_mod_cast chosen_card H (selected f)
    have hQ : (Fintype.card α:ℝ)≤(carrier H (selected f)).card+(selected f).card+
        (closureCost H (selected f):ℝ) := by exact_mod_cast carrier_card H (selected f)
    nlinarith only [hJ,mul_le_mul_of_nonneg_left hQ hδ]
  have hh := sum_le_sum (s := (univ : Finset (α → Bool)))
    (fun f _ => mul_le_mul_of_nonneg_left (hpoint f) (trialWeight_nonneg hp hp1 f))
  apply le_trans (le_of_eq ?_) hh
  simp only [mul_add,mul_sub,sum_add_distrib,sum_sub_distrib]
  rw [sum_trialWeight_card,discardCost_expectation]
  have hdelta : (∑ f : α → Bool, trialWeight p f*(δ*(Fintype.card α-(selected f).card-
      (closureCost H (selected f):ℝ)))) =
      δ*((1-p)*Fintype.card α-∑ e∈H, (e.card:ℝ)*p^(e.card-1)) := by
    simp only [mul_sub,sum_sub_distrib]
    simp_rw [mul_left_comm (trialWeight p _) δ]
    rw [← mul_sum,← mul_sum,← mul_sum,← sum_mul,sum_trialWeight,one_mul,
      sum_trialWeight_card,closureCost_expectation]
    ring
  simp only [mul_sub,sum_sub_distrib] at hdelta
  nlinarith only [hdelta]

#print axioms chosen_independent
#print axioms carrier_card
#print axioms extension
#print axioms discardCost_expectation
#print axioms closureCost_expectation
#print axioms reward_expectation
end
end Erdos773.GreedyBatchState
