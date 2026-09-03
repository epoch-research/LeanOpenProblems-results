import Submission.OldNewRepairSplitExplore

/-! New/new obligations in a same-counting-profile monotone completion.
The old-set incidence hypothesis is explicit and is not inferred from
power-saving counts of exceptional targets. -/
namespace Erdos66CompletionSelfMass
open Filter AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66Counting
  Erdos66BoundedReuseRepair Erdos66UnrestrictedRepairIncidence Erdos66OldNewRepairSplit
open scoped Classical Topology
set_option maxHeartbeats 1800000

/-- A same-counting-profile completion must supply nearly all deficit mass
by new/new pairs if its old-set target incidences stay bounded as displayed. -/
theorem same_counting_completion_self_mass (A B : Set ℕ) (hAB : A ⊆ B)
    (T : ℕ → Finset ℕ) (R L : ℕ → ℝ) (a δ H d : ℝ) (hd : d<δ)
    (hA : Tendsto (fun N ↦ (count A N:ℝ)/R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N:ℝ)/R N) atTop (𝓝 a))
    (hdata : ∀ᶠ N in atTop, 0 ≤ L N ∧ 0<R N ∧
      (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n:ℝ)+δ*L N ≤ sumRep B n) ∧
      (∀ x<N, x∈B\A → R N*(targetDegree (cutoff A N) (T N) x:ℝ) ≤ H*(T N).card*L N)) :
    ∀ᶠ N in atTop, d*(T N).card*L N ≤ ∑ n∈T N, (sumRep (B\A) n:ℝ) := by
  have hm := negligible_old_incidence_forces_self_mass
    (fun N ↦ cutoff A N) (fun N ↦ cutoff (B\A) N) T R L δ H d hd
    (added_count_limit_zero A B hAB R a hA hB) (by
      filter_upwards [hdata] with N hN
      obtain ⟨hL,hR,hs,hg,hdeg⟩ := hN
      refine ⟨cutoff_disjoint_diff A B N,hL,hR,?_,?_⟩
      · intro n hn
        rw [cutoff_union_diff A B hAB N,cutoff_sumRep A (hs n hn),cutoff_sumRep B (hs n hn)]
        exact hg n hn
      · intro x hx
        exact hdeg x (mem_cutoff.mp hx).1 (mem_cutoff.mp hx).2)
  filter_upwards [hm,hdata] with N hm hN
  convert hm using 1
  unfold selfMass
  apply Finset.sum_congr rfl
  intro n hn
  rw [pairs_self,cutoff_sumRep (B\A) (hN.2.2.1 n hn)]

/-- The square-root target-mass cost of such a completion. No packet shapes
or reuse restrictions occur in this bound. -/
theorem same_counting_completion_card_lower (A B : Set ℕ) (hAB : A ⊆ B)
    (T : ℕ → Finset ℕ) (R L : ℕ → ℝ) (a δ H d : ℝ) (hd : d<δ)
    (hA : Tendsto (fun N ↦ (count A N:ℝ)/R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N:ℝ)/R N) atTop (𝓝 a))
    (hdata : ∀ᶠ N in atTop, 0 ≤ L N ∧ 0<R N ∧
      (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n:ℝ)+δ*L N ≤ sumRep B n) ∧
      (∀ x<N, x∈B\A → R N*(targetDegree (cutoff A N) (T N) x:ℝ) ≤ H*(T N).card*L N)) :
    ∀ᶠ N in atTop, Real.sqrt (d*(T N).card*L N) ≤ count (B\A) N := by
  apply negligible_old_incidence_card_lower
    (fun N ↦ cutoff A N) (fun N ↦ cutoff (B\A) N) T R L δ H d hd
    (added_count_limit_zero A B hAB R a hA hB)
  filter_upwards [hdata] with N hN
  obtain ⟨hL,hR,hs,hg,hdeg⟩ := hN
  refine ⟨cutoff_disjoint_diff A B N,hL,hR,?_,?_⟩
  · intro n hn
    rw [cutoff_union_diff A B hAB N,cutoff_sumRep A (hs n hn),cutoff_sumRep B (hs n hn)]
    exact hg n hn
  · intro x hx
    exact hdeg x (mem_cutoff.mp hx).1 (mem_cutoff.mp hx).2

/-- The same-profile specialization for a hypothetical logarithmic witness.
Only the completion's counting profile is deduced from its representation
limit; the base profile and its target-incidence bounds remain hypotheses. -/
theorem same_coefficient_completion_self_mass (A B : Set ℕ) (hAB : A ⊆ B)
    (c : ℝ) (hc : c≠0)
    (hB : Tendsto (fun n ↦ (sumRep B n:ℝ)/Real.log n) atTop (𝓝 c))
    (hA : Tendsto (fun N ↦ (count A N:ℝ)/Real.sqrt ((N:ℝ)*Real.log N))
      atTop (𝓝 (2*Real.sqrt (c/Real.pi))))
    (T : ℕ → Finset ℕ) (δ H d : ℝ) (hd : d<δ)
    (hdata : ∀ᶠ N in atTop, (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n:ℝ)+δ*Real.log N ≤ sumRep B n) ∧
      (∀ x<N, x∈B\A → Real.sqrt ((N:ℝ)*Real.log N)*
        (targetDegree (cutoff A N) (T N) x:ℝ) ≤ H*(T N).card*Real.log N)) :
    ∀ᶠ N in atTop, d*(T N).card*Real.log N ≤ ∑ n∈T N, (sumRep (B\A) n:ℝ) := by
  apply same_counting_completion_self_mass A B hAB T
    (fun N ↦ Real.sqrt ((N:ℝ)*Real.log N)) (fun N ↦ Real.log N)
    (2*Real.sqrt (c/Real.pi)) δ H d hd hA
    (Erdos66TauberianProfile.witness_counting_profile hc hB)
  filter_upwards [hdata,eventually_ge_atTop 2] with N hN hN2
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos hNr
  exact ⟨hlog.le,Real.sqrt_pos.mpr (mul_pos (by linarith) hlog),hN⟩

/-- Persistent deficient targets require logarithmic self-representation
peaks in the addition itself, under the old-incidence hypothesis. -/
theorem same_coefficient_completion_frequent_self_peak (A B : Set ℕ) (hAB : A ⊆ B)
    (c : ℝ) (hc : c≠0)
    (hB : Tendsto (fun n ↦ (sumRep B n:ℝ)/Real.log n) atTop (𝓝 c))
    (hA : Tendsto (fun N ↦ (count A N:ℝ)/Real.sqrt ((N:ℝ)*Real.log N))
      atTop (𝓝 (2*Real.sqrt (c/Real.pi))))
    (T : ℕ → Finset ℕ) (δ H d : ℝ) (hd : d<δ)
    (hdata : ∀ᶠ N in atTop, (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n:ℝ)+δ*Real.log N ≤ sumRep B n) ∧
      (∀ x<N, x∈B\A → Real.sqrt ((N:ℝ)*Real.log N)*
        (targetDegree (cutoff A N) (T N) x:ℝ) ≤ H*(T N).card*Real.log N))
    (hT : ∃ᶠ N in atTop, (T N).Nonempty) :
    ∃ᶠ N in atTop, ∃ n∈T N, d*Real.log N ≤ (sumRep (B\A) n:ℝ) := by
  have hm := same_coefficient_completion_self_mass A B hAB c hc hB hA T δ H d hd hdata
  apply (hT.and_eventually hm).mono
  intro N hN
  apply Finset.exists_le_of_sum_le hN.1
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using hN.2

end Erdos66CompletionSelfMass
