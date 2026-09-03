import Submission.GreedyLinearDrift
import Submission.GreedyPowerYoung

/-!
A finite survival-aware target potential. Selection probabilities are charged
only while every remaining target is available. The one-step certificate uses
closure hazards and their pairwise overlaps, not a uniform lower bound on the
number of available vertices over the whole run.
-/
namespace Erdos773.GreedyTargetHazard
open Finset GreedyHypergraphState GreedyLinearDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A dead, unselected target gives potential zero. Completed targets give one. -/
def value (H : Finset (Finset α)) (U I : Finset α) (r : ℝ) : ℝ :=
  if U \ I ⊆ available H I then r ^ (U \ I).card else 0

lemma value_nonneg (H : Finset (Finset α)) (U I : Finset α) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ value H U I r := by
  unfold value
  split_ifs <;> positivity

lemma value_eq_one {H : Finset (Finset α)} {U I : Finset α} (hUI : U ⊆ I) (r : ℝ) :
    value H U I r = 1 := by
  simp [value, sdiff_eq_empty_iff_subset.mpr hUI]

/-- A target killed earlier cannot become viable at a later legal choice. -/
lemma viable_predecessor {H : Finset (Finset α)} {U I : Finset α} {v : α}
    (hv : v ∈ available H I) (hs : U \ insert v I ⊆ available H (insert v I)) :
    U \ I ⊆ available H I := by
  intro u hu
  by_cases huv : u = v
  · simpa only [huv] using hv
  · apply available_antitone (subset_insert v I)
    apply hs
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hu).1, by
      simpa only [mem_insert, not_or] using And.intro huv (mem_sdiff.mp hu).2⟩

lemma value_eq_zero_of_dead {H : Finset (Finset α)} {U I : Finset α} {v : α}
    (hv : v ∈ available H I) (hs : ¬ U \ I ⊆ available H I) (r : ℝ) :
    value H U (insert v I) r = 0 := by
  exact if_neg (fun h => hs (viable_predecessor hv h))

/-- Remaining targets' closure neighborhoods, including overlaps. -/
def hazard (H : Finset (Finset α)) (I B : Finset α) : Finset α :=
  B.biUnion (closes H I)

lemma hazard_subset (H : Finset (Finset α)) (I B : Finset α) :
    hazard H I B ⊆ available H I := by
  intro v hv
  obtain ⟨u, hu, hv⟩ := mem_biUnion.mp hv
  exact closes_subset H I u hv

/-- Unless a target itself is chosen, a viable step avoids every target closure. -/
lemma avoids_hazard {H : Finset (Finset α)} {U I : Finset α} {v : α}
    (hv : v ∈ available H I) (hB : U \ I ⊆ available H I)
    (hn : v ∉ U \ I) (hs : U \ insert v I ⊆ available H (insert v I)) :
    v ∉ hazard H I (U \ I) := by
  intro hh
  obtain ⟨u, hu, hvu⟩ := mem_biUnion.mp hh
  have huv : u ≠ v := fun he => hn (he ▸ hu)
  have hu' : u ∈ U \ insert v I := by
    rw [sdiff_insert]
    exact mem_erase.mpr ⟨huv, hu⟩
  have hav := hs hu'
  rw [available_insert hv] at hav
  exact (mem_sdiff.mp hav).2 (mem_insert_of_mem (closes_symm (hB hu) hvu))

/-- A pointwise bound which allows harmless double counting of target choices. -/
lemma value_step_bound {H : Finset (Finset α)} {U I : Finset α} {v : α}
    (hv : v ∈ available H I) (hB : U \ I ⊆ available H I)
    {r : ℝ} (hr : 0 ≤ r) :
    value H U (insert v I) r ≤
      (if v ∈ U \ I then r ^ ((U \ I).card - 1) else 0) +
      (if v ∉ hazard H I (U \ I) then r ^ (U \ I).card else 0) := by
  by_cases hs : U \ insert v I ⊆ available H (insert v I)
  · rw [value, if_pos hs]
    by_cases hvB : v ∈ U \ I
    · rw [if_pos hvB, sdiff_insert, card_erase_of_mem hvB]
      have hh : 0 ≤ (if v ∉ hazard H I (U \ I) then r ^ (U \ I).card else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [if_neg hvB, if_pos (avoids_hazard hv hB hvB hs), zero_add,
        sdiff_insert, erase_eq_of_notMem hvB]
  · rw [value, if_neg hs]
    have h1 : 0 ≤ (if v ∈ U \ I then r ^ ((U \ I).card - 1) else 0) := by
      split_ifs <;> positivity
    have h2 : 0 ≤ (if v ∉ hazard H I (U \ I) then r ^ (U \ I).card else 0) := by
      split_ifs <;> positivity
    exact add_nonneg h1 h2

/-- The one-step sum, with the exact complement-of-hazard cardinality. -/
theorem step_sum_bound {H : Finset (Finset α)} {U I : Finset α}
    (hB : U \ I ⊆ available H I) {r : ℝ} (hr : 0 ≤ r) :
    (∑ v ∈ available H I, value H U (insert v I) r) ≤
      (U \ I).card * r ^ ((U \ I).card - 1) +
      (available H I \ hazard H I (U \ I)).card * r ^ (U \ I).card := by
  have hh := sum_le_sum (fun v hv => value_step_bound hv hB hr)
  rw [sum_add_distrib] at hh
  have h1 : (∑ v ∈ available H I,
      if v ∈ U \ I then r ^ ((U \ I).card - 1) else 0) =
      (U \ I).card * r ^ ((U \ I).card - 1) := by
    rw [← sum_filter]
    have he : (available H I).filter (fun v => v ∈ U \ I) = U \ I := by
      ext v
      simp only [mem_filter]
      exact ⟨And.right, fun hv => ⟨hB hv, hv⟩⟩
    rw [he]
    simp
  have h2 : (∑ v ∈ available H I,
      if v ∉ hazard H I (U \ I) then r ^ (U \ I).card else 0) =
      (available H I \ hazard H I (U \ I)).card * r ^ (U \ I).card := by
    rw [← sum_filter]
    have he : (available H I).filter (fun v => v ∉ hazard H I (U \ I)) =
        available H I \ hazard H I (U \ I) := by ext v; simp
    rw [he]
    simp
  rwa [h1, h2] at hh

/-- Bonferroni supplies a real lower hazard, permitting nonintegral profiles. -/
theorem complement_card_bound (H : Finset (Finset α)) (I B : Finset α)
    (l : ℝ) (C : ℕ)
    (hl : ∀ u ∈ B, l ≤ (closes H I u).card)
    (hC : ∀ u ∈ B, ∀ v ∈ B, u ≠ v →
      (closes H I u ∩ closes H I v).card ≤ C) :
    ((available H I \ hazard H I B).card : ℝ) ≤
      (available H I).card - B.card * l + B.card.choose 2 * C := by
  have hh := union_card_lower B (closes H I) C hC
  have hh' : (∑ u ∈ B, ((closes H I u).card : ℝ)) ≤
      (hazard H I B).card + (B.card.choose 2 : ℝ) * C := by
    exact_mod_cast hh
  have hs := sum_le_sum hl
  simp only [sum_const, nsmul_eq_mul] at hs
  have hc : ((available H I \ hazard H I B).card : ℝ) + (hazard H I B).card =
      (available H I).card := by
    exact_mod_cast card_sdiff_add_card_eq_card (hazard_subset H I B)
  linarith

/-- The closure lower bound and pair overlap are the only geometric inputs. -/
theorem step_hazard_bound {H : Finset (Finset α)} {U I : Finset α}
    (hB : U \ I ⊆ available H I) {r : ℝ} (hr : 0 ≤ r)
    (l : ℝ) (C : ℕ)
    (hl : ∀ u ∈ U \ I, l ≤ (closes H I u).card)
    (hC : ∀ u ∈ U \ I, ∀ v ∈ U \ I, u ≠ v →
      (closes H I u ∩ closes H I v).card ≤ C) :
    (∑ v ∈ available H I, value H U (insert v I) r) ≤
      (U \ I).card * r ^ ((U \ I).card - 1) +
      ((available H I).card - (U \ I).card * l +
        (U \ I).card.choose 2 * C) * r ^ (U \ I).card := by
  apply (step_sum_bound hB hr).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (complement_card_bound H I (U \ I) l C hl hC) (pow_nonneg hr _))

omit [Fintype α] [DecidableEq α] in
/-- Convexity of a natural power in the form needed by the backward potential. -/
lemma power_tangent (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (k : ℕ) :
    s^k + (k : ℝ)*s^(k-1)*(r-s) ≤ r^k := by
  cases k with
  | zero => simp
  | succ k =>
    have hh := GreedyPowerYoung.power_young s r hs hr k
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ] at *
    nlinarith only [hh]

omit [Fintype α] [DecidableEq α] in
/-- A single scalar inequality controls every target set of size at most K.
No monotonicity of the two consecutive potential parameters is required. -/
theorem scalar_supersolution (Q l r s : ℝ) (C k K : ℕ)
    (hQ : 0 ≤ Q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hk : k ≤ K)
    (hscalar : 1 ≤ Q*(r-s)+(l-((K:ℝ)-1)/2*C)*s) :
    (k:ℝ)*s^(k-1)+(Q-(k:ℝ)*l+(k.choose 2:ℝ)*C)*s^k ≤ Q*r^k := by
  by_cases hk0 : k = 0
  · simp [hk0]
  have hk1 : 1 ≤ k := by omega
  have hc : (k.choose 2 : ℝ) = (k:ℝ)*((k:ℝ)-1)/2 := Nat.cast_choose_two ℝ k
  have hk' : (k:ℝ) ≤ K := by exact_mod_cast hk
  have hn : 0 ≤ (C:ℝ)*s := by positivity
  have hsc : 1 ≤ Q*(r-s)+(l-((k:ℝ)-1)/2*C)*s := by
    nlinarith only [hscalar, mul_nonneg (sub_nonneg.mpr hk') hn]
  have ht := mul_le_mul_of_nonneg_left (power_tangent r s hr hs k) hQ
  have hm := mul_le_mul_of_nonneg_left hsc (show 0 ≤ (k:ℝ)*s^(k-1) by positivity)
  have hpow : s^(k-1)*s = s^k := by rw [← pow_succ, Nat.sub_add_cancel hk1]
  rw [hc]
  have he : (k:ℝ)*s^(k-1)+(Q-(k:ℝ)*l+(k:ℝ)*((k:ℝ)-1)/2*C)*s^k -
      Q*(s^k+(k:ℝ)*s^(k-1)*(r-s)) =
      (k:ℝ)*s^(k-1)*(1-(Q*(r-s)+(l-((k:ℝ)-1)/2*C)*s)) := by
    rw [← hpow]
    ring
  nlinarith only [hm, ht, he]

/-- A complete local supermartingale certificate, also valid at dead states. -/
theorem average_le_value (H : Finset (Finset α)) (U I : Finset α)
    (r s l : ℝ) (C K : ℕ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hne : (available H I).Nonempty) (hsize : (U \ I).card ≤ K)
    (hl : ∀ u ∈ U \ I, l ≤ (closes H I u).card)
    (hC : ∀ u ∈ U \ I, ∀ v ∈ U \ I, u ≠ v →
      (closes H I u ∩ closes H I v).card ≤ C)
    (hscalar : 1 ≤ (available H I).card*(r-s)+(l-((K:ℝ)-1)/2*C)*s) :
    (∑ v ∈ available H I, value H U (insert v I) s) / (available H I).card ≤
      value H U I r := by
  have hQ : (0:ℝ) < (available H I).card := by exact_mod_cast card_pos.mpr hne
  by_cases hB : U \ I ⊆ available H I
  · rw [value, if_pos hB]
    apply (div_le_iff₀ hQ).mpr
    have hh := (step_hazard_bound hB hs l C hl hC).trans
      (scalar_supersolution (available H I).card l r s C (U \ I).card K
        hQ.le hr hs hsize hscalar)
    simpa only [mul_comm] using hh
  · have hz : (∑ v ∈ available H I, value H U (insert v I) s) = 0 :=
      sum_eq_zero (fun v hv => value_eq_zero_of_dead hv hB s)
    rw [hz, zero_div, value, if_neg hB]

#print axioms viable_predecessor
#print axioms step_hazard_bound
#print axioms power_tangent
#print axioms scalar_supersolution
#print axioms average_le_value
end
end Erdos773.GreedyTargetHazard
