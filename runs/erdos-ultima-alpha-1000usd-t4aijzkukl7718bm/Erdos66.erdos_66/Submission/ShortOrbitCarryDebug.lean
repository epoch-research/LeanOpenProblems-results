import Submission.AntitonePairIntervalsExplore
import Submission.TranslatedPrefixPaletteExplore

/-! Deterministic short-orbit carry transfer for antitone row families.
An interval discrepancy hypothesis on one phase orbit replaces averaging
over all phases. Both the old pair and the row-index interval are retained. -/
namespace Erdos66ShortOrbitCarryDebug
open Erdos66OriginRepair Erdos66AntitonePairIntervals
  Erdos66IntegerBlock Erdos66OuterCarryProfile Erdos66OuterMixedPrefix
  Erdos66TranslatedPrefixPalette
open scoped Classical
set_option maxHeartbeats 2200000

variable (M : ℕ) [NeZero M]

noncomputable def phasedRows (C : ℕ → Finset (ZMod M)) (b : ZMod M) (k : ℕ) :
    Finset (ZMod M) := shift M (C k) (b*(k : ZMod M))

noncomputable def hit (b a : ZMod M) (t k : ℕ) : ℝ :=
  if (b*(k : ZMod M)+a).val ≤ t then 1 else 0

noncomputable def IntervalBound (b : ZMod M) (Q t : ℕ) (E : ℝ) : Prop :=
  ∀ a : ZMod M, ∀ l u : ℕ, l ≤ u → u ≤ Q →
    |(∑ k ∈ Finset.Ico l u, hit M b a t k) -
      ((u-l : ℕ) : ℝ) * ((t+1 : ℕ) : ℝ)/M| ≤ E

lemma phasedRows_zero (C : ℕ → Finset (ZMod M)) (b : ZMod M) :
    phasedRows M C b 0 = C 0 := by simp [phasedRows]

lemma lower_eq_prefix (A B : Finset (ZMod M)) (t : ℕ) :
    lower M A B t = prefixCount M A B (t : ZMod M) (t+1) := by
  rw [lower_zmod,prefixCount_sum]
  simp only [Nat.lt_succ_iff]

lemma lower_phased_sum (C D : ℕ → Finset (ZMod M)) (b : ZMod M)
    (q t k : ℕ) (hk : k ≤ q) :
    (lower M (phasedRows M C b k) (phasedRows M D b (q-k)) t : ℝ) =
      ∑ a : ZMod M, if k ∈ active C D q ((t : ZMod M)-b*q) a
        then hit M b a t k else 0 := by
  have hp : (t : ZMod M)-b*k-b*(q-k : ℕ) = (t : ZMod M)-b*q := by
    rw [Nat.cast_sub hk]
    ring
  rw [phasedRows,phasedRows,lower_eq_prefix,shift_prefix_formula,hp]
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp only [mem_active,hk,true_and,hit,ite_and,Finset.sum_ite_mem,Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h1 : (b*(k : ZMod M)+a).val ≤ t
  · simp only [Nat.lt_succ_iff,h1,true_and,ite_true]
  · simp only [Nat.lt_succ_iff,h1,false_and,ite_false,ite_self]

lemma lower_sum_eq_active (C D : ℕ → Finset (ZMod M)) (b : ZMod M) (q t : ℕ) :
    (∑ k ∈ Finset.range (q+1),
      (lower M (phasedRows M C b k) (phasedRows M D b (q-k)) t : ℝ)) =
      ∑ a : ZMod M, ∑ k ∈ active C D q ((t : ZMod M)-b*q) a, hit M b a t k := by
  calc
    _ = ∑ k ∈ Finset.range (q+1), ∑ a : ZMod M,
        if k ∈ active C D q ((t : ZMod M)-b*q) a then hit M b a t k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact lower_phased_sum M C D b q t k (by simpa using Finset.mem_range.mp hk)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter,Finset.mem_range,mem_active]
      trace_state
      omega

lemma count_sum_eq_active (C D : ℕ → Finset (ZMod M)) (q : ℕ) (z : ZMod M) :
    (∑ k ∈ Finset.range (q+1), (pairCount (C k) (D (q-k)) z : ℝ)) =
      ∑ a : ZMod M, ((active C D q z a).card : ℝ) := by
  have he (k : ℕ) (hk : k ≤ q) :
      (pairCount (C k) (D (q-k)) z : ℝ) =
        ∑ a : ZMod M, if k ∈ active C D q z a then 1 else 0 := by
    change (cyclicCount M (C k) (D (q-k)) z : ℝ) = _
    rw [cyclicCount_sum]
    simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,mem_active,hk,true_and]
  calc
    _ = ∑ k ∈ Finset.range (q+1), ∑ a : ZMod M,
        if k ∈ active C D q z a then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact he k (by simpa using Finset.mem_range.mp hk)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_filter]
      have hfilter : (Finset.range (q+1)).filter (fun k ↦ k ∈ active C D q z a) =
          active C D q z a := by
        ext k
        simp only [Finset.mem_filter,Finset.mem_range,mem_active]
        trace_state
      omega
      rw [hfilter]
      simp

lemma active_orbit_error (C D : ℕ → Finset (ZMod M))
    (hC : Antitone C) (hD : Antitone D) (b z a : ZMod M) (q t : ℕ) (E : ℝ)
    (hOrbit : IntervalBound M b (q+1) t E) :
    |(∑ k ∈ active C D q z a, hit M b a t k) -
      (((t+1 : ℕ) : ℝ)/M) * (active C D q z a).card| ≤ E := by
  obtain ⟨l,u,hlu,hu,he⟩ := active_eq_interval C D hC hD q z a
  have hh := hOrbit a l u hlu hu
  rw [he,Finset.card_Ico]
  convert hh using 1
  ring

/-- The number of potentially active old pairs is controlled by the two
half-row mixed counts, not by all pairs of the largest row. -/
theorem lower_short_orbit_error (C D : ℕ → Finset (ZMod M))
    (hC : Antitone C) (hD : Antitone D) (b : ZMod M) (q t : ℕ) (E : ℝ)
    (hE : 0 ≤ E) (hOrbit : IntervalBound M b (q+1) t E) :
    |(∑ k ∈ Finset.range (q+1),
        (lower M (phasedRows M C b k) (phasedRows M D b (q-k)) t : ℝ)) -
      (((t+1 : ℕ) : ℝ)/M) *
        (∑ k ∈ Finset.range (q+1),
          (pairCount (C k) (D (q-k)) ((t : ZMod M)-b*q) : ℝ))| ≤
      E*((pairCount (C 0) (D (q/2)) ((t : ZMod M)-b*q) : ℝ) +
        pairCount (C (q/2)) (D 0) ((t : ZMod M)-b*q)) := by
  let z : ZMod M := (t : ZMod M)-b*q
  let S := halfSupport C D q z
  rw [lower_sum_eq_active,count_sum_eq_active,Finset.mul_sum,← Finset.sum_sub_distrib]
  have hpoint (a : ZMod M) :
      |(∑ k ∈ active C D q z a, hit M b a t k) -
        (((t+1 : ℕ) : ℝ)/M)*(active C D q z a).card| ≤ if a ∈ S then E else 0 := by
    by_cases ha : a ∈ S
    · rw [if_pos ha]
      exact active_orbit_error M C D hC hD b z a q t E hOrbit
    · rw [if_neg ha,active_empty_off_halfSupport C D hC hD q z a ha]
      simp
  have hh := (Finset.abs_sum_le_sum_abs
    (fun a : ZMod M ↦ (∑ k ∈ active C D q z a, hit M b a t k) -
      (((t+1 : ℕ) : ℝ)/M)*(active C D q z a).card) Finset.univ).trans
        (Finset.sum_le_sum (fun a _ ↦ hpoint a))
  simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul] at hh
  have hc : (S.card : ℝ) ≤ (pairCount (C 0) (D (q/2)) z : ℝ)+
      pairCount (C (q/2)) (D 0) z := by exact_mod_cast halfSupport_card_le C D q z
  exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hc hE])

end Erdos66ShortOrbitCarryDebug
