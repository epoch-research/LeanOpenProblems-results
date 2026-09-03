import Submission.FiniteLogMassBudgetExplore
import Submission.DiscreteRotationMassExplore
import Submission.ShortOrbitNaturalExplore

/-! Aggregate carry error charged to the number of active old pairs and
their total expected endpoint mass, not to the maximum orbit length. -/
namespace Erdos66ActivityMassCarry
open Erdos66FiniteLogMassBudget Erdos66AntitonePairIntervals
  Erdos66ShortOrbitCarry Erdos66ShortOrbitNatural Erdos66DiscreteRotationMass
  Erdos66DiscreteRotationBridge Erdos66OriginRepair Erdos66IntegerBlock
open scoped Classical
set_option maxHeartbeats 2200000

section Support
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def activeSupport (C D : ℕ → Finset G) (q : ℕ) (z : G) : Finset G :=
  Finset.univ.filter (fun a ↦ (active C D q z a).Nonempty)

lemma mem_activeSupport (C D : ℕ → Finset G) (q : ℕ) (z a : G) :
    a ∈ activeSupport C D q z ↔ (active C D q z a).Nonempty := by
  simp only [activeSupport,Finset.mem_filter,Finset.mem_univ,true_and]

lemma active_empty_off_support (C D : ℕ → Finset G) (q : ℕ) (z a : G)
    (ha : a ∉ activeSupport C D q z) : active C D q z a=∅ := by
  exact Finset.not_nonempty_iff_eq_empty.mp (fun h ↦ ha ((mem_activeSupport C D q z a).mpr h))

lemma activeSupport_subset_halfSupport (C D : ℕ → Finset G)
    (hC : Antitone C) (hD : Antitone D) (q : ℕ) (z : G) :
    activeSupport C D q z ⊆ halfSupport C D q z := by
  intro a ha
  obtain ⟨k,hk⟩ := (mem_activeSupport C D q z a).mp ha
  exact active_mem_halfSupport C D hC hD q z a k hk

lemma activeSupport_card_le (C D : ℕ → Finset G)
    (hC : Antitone C) (hD : Antitone D) (q : ℕ) (z : G) :
    (activeSupport C D q z).card  ≤  pairCount (C 0) (D (q/2)) z+
      pairCount (C (q/2)) (D 0) z :=
  (Finset.card_le_card (activeSupport_subset_halfSupport C D hC hD q z)).trans
    (halfSupport_card_le C D q z)

lemma sum_active_card_on_support (C D : ℕ → Finset G) (q : ℕ) (z : G) :
    (∑ a ∈ activeSupport C D q z, ((active C D q z a).card : ℝ))=
      ∑ a : G, ((active C D q z a).card : ℝ) := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a ha hnot
  rw [active_empty_off_support C D q z a hnot,Finset.card_empty,Nat.cast_zero]

end Support

variable (M : ℕ) [NeZero M]

noncomputable def mixedPhaseMass (C D : ℕ → Finset (ZMod M)) (b : ZMod M)
    (q t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (q+1), (pairCount (C k) (D (q-k)) ((t : ZMod M)-b*q) : ℝ)

noncomputable def supportCount (C D : ℕ → Finset (ZMod M)) (b : ZMod M)
    (q t : ℕ) : ℝ := (activeSupport C D q ((t : ZMod M)-b*q)).card

omit [NeZero M] in
lemma mixedPhaseMass_nonneg (C D : ℕ → Finset (ZMod M)) (b : ZMod M) (q t : ℕ) :
    0 ≤ mixedPhaseMass M C D b q t := Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)

lemma supportCount_nonneg (C D : ℕ → Finset (ZMod M)) (b : ZMod M) (q t : ℕ) :
    0 ≤ supportCount M C D b q t := Nat.cast_nonneg _

lemma active_mass_orbit_error (C D : ℕ → Finset (ZMod M))
    (hC : Antitone C) (hD : Antitone D) (z a : ZMod M) (q t : ℕ)
    (ht : t<M) (horizon : (q+1)^2 ≤ M) :
    |(∑ k ∈ active C D q z a, hit M (phase M) a t k)-
      (((t+1 : ℕ) : ℝ)/M)*(active C D q z a).card|  ≤ 
      30+50*Real.log ((((t+1 : ℕ) : ℝ)/M)*(active C D q z a).card+1) := by
  obtain ⟨l,u,hlu,hu,he⟩ := active_eq_interval C D hC hD q z a
  have hh := phase_interval_mass_error M (q+1) t l u horizon ht hu a
  rw [he,Nat.card_Ico]
  simpa only [div_mul_eq_mul_div,mul_comm,mul_div_assoc] using hh

/-- Actual lower carries have an error bounded by 30K+100 sqrt(K P),
where K counts active old pairs and P is their expected lower-carry mass. -/
theorem lower_activity_budget (C D : ℕ → Finset (ZMod M))
    (hC : Antitone C) (hD : Antitone D) (q t : ℕ)
    (ht : t<M) (horizon : (q+1)^2 ≤ M) :
    |(∑ k ∈ Finset.range (q+1),
        (lower M (phasedRows M C (phase M) k) (phasedRows M D (phase M) (q-k)) t : ℝ))-
      (((t+1 : ℕ) : ℝ)/M)*mixedPhaseMass M C D (phase M) q t|  ≤ 
      budget (supportCount M C D (phase M) q t)
        ((((t+1 : ℕ) : ℝ)/M)*mixedPhaseMass M C D (phase M) q t) := by
  let z : ZMod M := (t : ZMod M)-phase M*q
  let S := activeSupport C D q z
  let ρ : ℝ := ((t+1 : ℕ) : ℝ)/M
  let e : ZMod M → ℝ := fun a ↦
    (∑ k ∈ active C D q z a, hit M (phase M) a t k)-ρ*(active C D q z a).card
  let f : ZMod M → ℝ := fun a ↦ ρ*(active C D q z a).card
  have hf : ∀ a ∈ S, 0 ≤ f a := by intro a ha; dsimp [f,ρ]; positivity
  have hpoint (a : ZMod M) : |e a| ≤ if a ∈ S then 30+50*Real.log (f a+1) else 0 := by
    by_cases ha : a ∈ S
    · rw [if_pos ha]
      exact active_mass_orbit_error M C D hC hD z a q t ht horizon
    · rw [if_neg ha]
      dsimp [e]
      rw [active_empty_off_support C D q z a ha]
      simp
  have hsum := (Finset.abs_sum_le_sum_abs e Finset.univ).trans
    (Finset.sum_le_sum (fun a _ ↦ hpoint a))
  simp only [Finset.sum_ite_mem,Finset.univ_inter] at hsum
  have hmass : (∑ a ∈ S, f a)=ρ*mixedPhaseMass M C D (phase M) q t := by
    dsimp only [f,S]
    rw [←Finset.mul_sum,sum_active_card_on_support,←count_sum_eq_active]
    rfl
  have hbound := hsum.trans (log_budget_sum_le S f hf)
  rw [hmass] at hbound
  change |(∑ k ∈ Finset.range (q+1),
      (lower M (phasedRows M C (phase M) k) (phasedRows M D (phase M) (q-k)) t : ℝ))-
    ρ*mixedPhaseMass M C D (phase M) q t|  ≤  budget S.card (ρ*mixedPhaseMass M C D (phase M) q t)
  rw [lower_sum_eq_active,mixedPhaseMass,count_sum_eq_active,Finset.mul_sum,←Finset.sum_sub_distrib]
  rw [mixedPhaseMass,count_sum_eq_active,Finset.mul_sum] at hbound
  exact hbound

end Erdos66ActivityMassCarry
