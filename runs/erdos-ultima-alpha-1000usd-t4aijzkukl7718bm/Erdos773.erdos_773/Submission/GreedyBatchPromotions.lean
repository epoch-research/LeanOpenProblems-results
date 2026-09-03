import Submission.GreedyBatchState
import Submission.IndexedBernoulliMoments
import Submission.UniformLayerRegularization

/-! Indexed batched promotion witnesses and their overlap-sensitive tails.
The selected supports retain their original edge indices. -/
namespace Erdos773.GreedyBatchPromotions
open Finset HypergraphDegreeTrim UniformLayerRegularization
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def incidentLayer (H : Finset (Finset α)) (r : ℕ) (x : α) : Finset (Finset α) :=
  (layer H r).filter (fun e => x∈e)

def family (H : Finset (Finset α)) (x : α) (r k : ℕ) : Finset (Σ _ : Finset α, Finset α) :=
  (incidentLayer H r x).sigma (fun e => (e.erase x).powersetCard k)

def cost (H : Finset (Finset α)) (x : α) (r k : ℕ) (R : Finset α) : ℕ :=
  ((family H x r k).filter (fun i => i.2⊆R)).card

lemma family_card (H : Finset (Finset α)) (x : α) (r k : ℕ) :
    (family H x r k).card=degree (layer H r) x*(r-1).choose k := by
  rw [family,card_sigma]
  have he (e : Finset α) (he : e∈incidentLayer H r x) : ((e.erase x).powersetCard k).card=(r-1).choose k := by
    obtain ⟨he,hx⟩ := mem_filter.mp he
    rw [card_powersetCard,card_erase_of_mem hx,(mem_filter.mp he).2]
  rw [sum_congr rfl he]
  simp [degree,incidentLayer]

lemma positive_incidence (H : Finset (Finset α)) (x : α) (r k P : ℕ) (hr : r≤4)
    (hP : ∀ a, x≠a → pairDegree H x a≤P)
    (S : Finset α) (hS : S.Nonempty) :
    IndexedBernoulliMoments.incidence (family H x r k) (fun i => i.2) S≤8*P := by
  by_cases hxS : x∈S
  · have he : (family H x r k).filter (fun i => S⊆i.2)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨e,A⟩ hi
      obtain ⟨hi,hSA⟩ := mem_filter.mp hi
      have hAe := (mem_powersetCard.mp (mem_sigma.mp hi).2).1
      exact notMem_erase x e (hAe (hSA hxS))
    simp [IndexedBernoulliMoments.incidence,he]
  · obtain ⟨a,ha⟩ := hS
    have hxa : x≠a := fun he => hxS (he.symm ▸ ha)
    let E := (layer H r).filter (fun e => x∈e ∧ a∈e)
    have hs : (family H x r k).filter (fun i => S⊆i.2) ⊆
        E.sigma (fun e => (e.erase x).powersetCard k) := by
      rintro ⟨e,A⟩ hi
      obtain ⟨hi,hSA⟩ := mem_filter.mp hi
      obtain ⟨he,hA⟩ := mem_sigma.mp hi
      obtain ⟨he,hx⟩ := mem_filter.mp he
      have hae := (mem_erase.mp ((mem_powersetCard.mp hA).1 (hSA ha))).2
      exact mem_sigma.mpr ⟨mem_filter.mpr ⟨he,hx,hae⟩,hA⟩
    have hEc : E.card≤P := by
      apply (card_le_card (show E⊆H.filter (fun e => x∈e ∧ a∈e) from ?_)).trans (hP a hxa)
      intro e he
      obtain ⟨he,hx,ha⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨(mem_filter.mp he).1,hx,ha⟩
    have hcount (e : Finset α) (he : e∈E) : ((e.erase x).powersetCard k).card≤8 := by
      obtain ⟨he,hx,ha⟩ := mem_filter.mp he
      have hc := (mem_filter.mp he).2
      rw [card_powersetCard,card_erase_of_mem hx,hc]
      apply (Nat.choose_le_two_pow _ _).trans
      exact (Nat.pow_le_pow_right (by omega : 0<2) (by omega : r-1≤3))
    calc
      _ ≤ (E.sigma (fun e => (e.erase x).powersetCard k)).card := card_le_card hs
      _ = ∑ e∈E, ((e.erase x).powersetCard k).card := card_sigma _ _
      _ ≤ ∑ _e∈E, 8 := sum_le_sum hcount
      _ = 8*E.card := by simp [mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left 8 hEc

def overlapCaps (m P : ℕ) (i : ℕ) : ℕ := if i=0 then m else 8*P

lemma incidence_bound (H : Finset (Finset α)) (x : α) (r k P : ℕ) (hr : r≤4)
    (hP : ∀ a, x≠a → pairDegree H x a≤P) (S : Finset α) :
    IndexedBernoulliMoments.incidence (family H x r k) (fun i => i.2) S≤
      overlapCaps (degree (layer H r) x*(r-1).choose k) P S.card := by
  by_cases hS : S.card=0
  · have he := card_eq_zero.mp hS
    subst S
    simp [IndexedBernoulliMoments.incidence,overlapCaps,family_card]
  · rw [overlapCaps,if_neg hS]
    exact positive_incidence H x r k P hr hP S (card_pos.mp (by omega))

/-- Tail for all k-mark promotion witnesses of a rank-r original link. -/
theorem cost_tail (H : Finset (Finset α)) (x : α) (r k P q : ℕ) (hr : r≤4)
    (hP : ∀ a, x≠a → pairDegree H x a≤P) (p L : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hL : 0<L) :
    (∑ f : α → Bool, if L≤(cost H x r k (selected f):ℝ) then trialWeight p f else 0) ≤
      (IndexedBernoulliMoments.budget k q
        (overlapCaps (degree (layer H r) x*(r-1).choose k) P) p/L)^q := by
  exact IndexedBernoulliMoments.tail_bound (family H x r k) (fun i => i.2) k q
    (overlapCaps (degree (layer H r) x*(r-1).choose k) P) p L hp hp1 hL
    (fun i hi => (mem_powersetCard.mp (mem_sigma.mp hi).2).2)
    (fun S _ => incidence_bound H x r k P hr hP S)

/-- Every actual contraction has the required marked witness, including
contractions from rank four directly to rank two. -/
lemma contraction_count (H : Finset (Finset α)) (R : Finset α) (x : α) (j k : ℕ) :
    ((layer H (j+k)).filter (fun e => x∈e \ R ∧ (e \ R).card=j)).card ≤
      cost H x (j+k) k R := by
  apply card_le_card_of_injOn (fun e : Finset α => (⟨e,e∩R⟩ : Σ _ : Finset α, Finset α))
  · intro e he
    obtain ⟨he,hx,hj⟩ := mem_filter.mp he
    have her := (mem_filter.mp he).2
    have hcard : (e∩R).card=k := by
      have hh := card_sdiff_add_card_inter e R
      omega
    have hs : e∩R⊆e.erase x := by
      intro a ha
      obtain ⟨hae,haR⟩ := mem_inter.mp ha
      exact mem_erase.mpr ⟨fun he => (mem_sdiff.mp hx).2 (he ▸ haR),hae⟩
    exact mem_filter.mpr ⟨mem_sigma.mpr ⟨mem_filter.mpr ⟨he,(mem_sdiff.mp hx).1⟩,
      mem_powersetCard.mpr ⟨hs,hcard⟩⟩,inter_subset_right⟩
  · intro e he f hf hef
    exact congrArg Sigma.fst hef

#print axioms family_card
#print axioms positive_incidence
#print axioms incidence_bound
#print axioms cost_tail
#print axioms contraction_count
end
end Erdos773.GreedyBatchPromotions
