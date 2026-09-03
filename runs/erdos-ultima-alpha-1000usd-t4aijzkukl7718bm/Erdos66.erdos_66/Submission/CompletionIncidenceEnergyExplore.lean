import Submission.SignedRepairEnergyStabilityExplore

/-! Natural-set endpoints for aggregate signed-repair energy. A monotone
completion with the same counting profile must have unbounded normalized
midpoint contrast energy along persistent deficient target sets. This is a
necessary condition, not an impossibility claim. -/
namespace Erdos66CompletionIncidenceEnergy
open Erdos66SignedRepairEnergy Erdos66SignedRepairEnergyStability
  Erdos66SignedRepairIncidence Erdos66UnrestrictedRepairIncidence Erdos66Counting
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 2200000

lemma editCount_of_subset {A B : Finset ℕ} (hAB : A⊆B) :
    editCount A B=(B.card : ℝ)-A.card := by
  have he : A\B=∅ := Finset.sdiff_eq_empty_iff_subset.mpr hAB
  have hh := card_difference A B
  simpa only [editCount,he,Finset.card_empty,Nat.cast_zero,add_zero,sub_zero] using hh

lemma cutoff_subset_of_subset {A B : Set ℕ} (hAB : A⊆B) (N : ℕ) :
    cutoff A N⊆cutoff B N := by
  intro n hn
  obtain ⟨hn,ha⟩ := mem_cutoff.mp hn
  exact mem_cutoff.mpr ⟨hn,hAB ha⟩

lemma monotone_edit_count_zero (A B : Set ℕ) (hAB : A⊆B) (R : ℕ → ℝ) (a : ℝ)
    (hA : Tendsto (fun N ↦ (count A N : ℝ)/R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N : ℝ)/R N) atTop (𝓝 a)) :
    Tendsto (fun N ↦ editCount (cutoff A N) (cutoff B N)/R N) atTop (𝓝 0) := by
  have hh := hB.sub hA
  simp only [sub_self] at hh
  apply hh.congr
  intro N
  rw [editCount_of_subset (cutoff_subset_of_subset hAB N),sub_div]
  rfl

/-- Infinite signed repairs: energy vanishing only on the changed points
already excludes persistent positive gains at unchanged counting density. -/
theorem same_counting_vanishing_energy_empty (A B : Set ℕ) (T : ℕ → Finset ℕ)
    (R L : ℕ → ℝ) (a δ β : ℝ) (hδ : 0<δ)
    (hA : Tendsto (fun N ↦ (count A N : ℝ)/R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N : ℝ)/R N) atTop (𝓝 a))
    (hE : Tendsto (fun N ↦ normalizedEnergy (cutoff A N) (cutoff B N) (T N) (L N) (R N) β)
      atTop (𝓝 0))
    (hdata : ∀ᶠ N in atTop, 0<L N ∧ 0<R N ∧ (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n : ℝ)+δ*L N ≤ sumRep B n)) :
    ∀ᶠ N in atTop, T N=∅ := by
  apply same_mass_vanishing_energy_empty (fun N ↦ cutoff A N) (fun N ↦ cutoff B N)
    T R L a δ β hδ hA hB hE
  filter_upwards [hdata] with N hN
  refine ⟨hN.1,hN.2.1,?_⟩
  intro n hn
  rw [cutoff_sumRep A (hN.2.2.1 n hn),cutoff_sumRep B (hN.2.2.1 n hn)]
  exact hN.2.2.2 n hn

/-- No target-degree hypothesis is used here: unbounded energy is the
conclusion, forced by negligible additions and persistent macroscopic gains. -/
theorem same_counting_monotone_energy_unbounded (A B : Set ℕ) (hAB : A⊆B)
    (T : ℕ → Finset ℕ) (R L : ℕ → ℝ) (a δ β : ℝ) (hδ : 0<δ)
    (hA : Tendsto (fun N ↦ (count A N : ℝ)/R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N : ℝ)/R N) atTop (𝓝 a))
    (hdata : ∀ᶠ N in atTop, 0<L N ∧ 0<R N ∧ (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n : ℝ)+δ*L N ≤ sumRep B n)) :
    ∀ M : ℝ, ∀ᶠ N in atTop, (T N).Nonempty →
      M<normalizedEnergy (cutoff A N) (cutoff B N) (T N) (L N) (R N) β := by
  apply small_edits_require_unbounded_energy (fun N ↦ cutoff A N) (fun N ↦ cutoff B N)
    T R L a δ β hδ hA hB (monotone_edit_count_zero A B hAB R a hA hB)
  filter_upwards [hdata] with N hN
  refine ⟨hN.1,hN.2.1,?_⟩
  intro n hn
  rw [cutoff_sumRep A (hN.2.2.1 n hn),cutoff_sumRep B (hN.2.2.1 n hn)]
  exact hN.2.2.2 n hn

/-- Logarithmic specialization. The base counting profile is an explicit
hypothesis; only the completion's profile comes from the conjectured limit. -/
theorem same_coefficient_completion_energy_unbounded (A B : Set ℕ) (hAB : A⊆B)
    (c : ℝ) (hc : c≠0)
    (hB : Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 c))
    (hA : Tendsto (fun N ↦ (count A N : ℝ)/Real.sqrt ((N : ℝ)*Real.log N))
      atTop (𝓝 (2*Real.sqrt (c/Real.pi))))
    (T : ℕ → Finset ℕ) (δ β : ℝ) (hδ : 0<δ)
    (hdata : ∀ᶠ N in atTop, (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n : ℝ)+δ*Real.log N ≤ sumRep B n)) :
    ∀ M : ℝ, ∀ᶠ N in atTop, (T N).Nonempty →
      M<normalizedEnergy (cutoff A N) (cutoff B N) (T N) (Real.log N)
        (Real.sqrt ((N : ℝ)*Real.log N)) β := by
  apply same_counting_monotone_energy_unbounded A B hAB T
    (fun N ↦ Real.sqrt ((N : ℝ)*Real.log N)) (fun N ↦ Real.log N)
    (2*Real.sqrt (c/Real.pi)) δ β hδ hA (Erdos66TauberianProfile.witness_counting_profile hc hB)
  filter_upwards [hdata,eventually_ge_atTop 2] with N hN hN2
  have hNr : (1 : ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hlog : 0<Real.log (N : ℝ) := Real.log_pos hNr
  exact ⟨hlog,Real.sqrt_pos.mpr (mul_pos (by linarith) hlog),hN⟩

/-- Along persistent target sets, the same energy exceeds every bound
arbitrarily late. A large maximum contrast alone is not substituted for
this aggregate quadratic conclusion. -/
theorem same_coefficient_completion_frequent_energy (A B : Set ℕ) (hAB : A⊆B)
    (c : ℝ) (hc : c≠0)
    (hB : Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 c))
    (hA : Tendsto (fun N ↦ (count A N : ℝ)/Real.sqrt ((N : ℝ)*Real.log N))
      atTop (𝓝 (2*Real.sqrt (c/Real.pi))))
    (T : ℕ → Finset ℕ) (δ β : ℝ) (hδ : 0<δ)
    (hdata : ∀ᶠ N in atTop, (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n : ℝ)+δ*Real.log N ≤ sumRep B n))
    (hT : ∃ᶠ N in atTop, (T N).Nonempty) :
    ∀ M : ℝ, ∃ᶠ N in atTop, M<normalizedEnergy (cutoff A N) (cutoff B N) (T N)
      (Real.log N) (Real.sqrt ((N : ℝ)*Real.log N)) β := by
  intro M
  have hh := same_coefficient_completion_energy_unbounded A B hAB c hc hB hA T δ β hδ hdata M
  exact (hT.and_eventually hh).mono (fun N hN ↦ hN.2 hN.1)

end Erdos66CompletionIncidenceEnergy
