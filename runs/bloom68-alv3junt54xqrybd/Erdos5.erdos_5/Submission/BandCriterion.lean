import Submission.GapBridge

/-!
# Exact band-recurrence criterion

These are equivalences and conditional implications only.  No band-recurrence
hypothesis for the prime sequence is asserted in this module.
-/

open Filter Set
open scoped Topology

namespace Erdos5BandCriterion

/-- Every positive open band is visited at arbitrarily late indices. -/
def BandRecurrence (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∀ N : ℕ,
    ∃ k : ℕ, N ≤ k ∧ a < f k ∧ f k < b

/-- The desired finite nonnegative subsequential limits. -/
def AllNonnegativeLimits (f : ℕ → ℝ) : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ n : ℕ → ℕ,
    StrictMono n ∧ Tendsto (fun i => f (n i)) atTop (𝓝 C)

/-- Metric cluster points are exactly strictly increasing subsequential limits. -/
theorem cluster_iff_subsequence (f : ℕ → ℝ) (C : ℝ) :
    MapClusterPt C atTop f ↔
      ∃ n : ℕ → ℕ, StrictMono n ∧
        Tendsto (fun i => f (n i)) atTop (𝓝 C) := by
  constructor
  · exact TopologicalSpace.FirstCountableTopology.tendsto_subseq
  · rintro ⟨n, hn, ht⟩
    have hcl : ClusterPt C (map (f ∘ n) atTop) := ClusterPt.of_le_nhds ht
    have hle : map (f ∘ n) atTop ≤ map f atTop := by
      rw [← map_map]
      exact map_mono hn.tendsto_atTop
    exact hcl.mono hle

/-- A real cluster point is characterized by late metric approximations. -/
theorem cluster_iff_approximations (f : ℕ → ℝ) (C : ℝ) :
    MapClusterPt C atTop f ↔
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ k : ℕ, N ≤ k ∧ |f k - C| < ε := by
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
  simp only [frequently_atTop, Metric.mem_ball, Real.dist_eq]

/-- Recurrence in all positive open bands is equivalent to all nonnegative limits. -/
theorem bandRecurrence_iff_allNonnegativeLimits (f : ℕ → ℝ) :
    BandRecurrence f ↔ AllNonnegativeLimits f := by
  constructor
  · intro h C hC
    apply (cluster_iff_subsequence f C).mp
    apply (cluster_iff_approximations f C).mpr
    intro ε hε N
    by_cases hz : C = 0
    · obtain ⟨k, hkN, hlo, hhi⟩ := h (ε / 3) (2 * ε / 3)
        (by linarith) (by linarith) N
      refine ⟨k, hkN, ?_⟩
      rw [hz, sub_zero, abs_of_pos (by linarith : 0 < f k)]
      linarith
    · have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hz)
      let δ : ℝ := min ε C / 2
      have hδp : 0 < δ := div_pos (lt_min hε hCp) (by norm_num)
      have hδε : δ ≤ ε / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      have hδC : δ ≤ C / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      obtain ⟨k, hkN, hlo, hhi⟩ := h (C - δ) (C + δ)
        (by linarith) (by linarith) N
      exact ⟨k, hkN, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  · intro h a b ha hab N
    have hC : 0 ≤ (a + b) / 2 := by linarith
    obtain ⟨n, hn, ht⟩ := h ((a + b) / 2) hC
    have hc := (cluster_iff_subsequence f ((a + b) / 2)).mpr ⟨n, hn, ht⟩
    obtain ⟨k, hkN, hk⟩ := (cluster_iff_approximations f ((a + b) / 2)).mp hc
      ((b - a) / 2) (by linarith) N
    rcases abs_lt.mp hk with ⟨hlo, hhi⟩
    exact ⟨k, hkN, by linarith, by linarith⟩

/-- A genuine failure is witnessed by an eventually empty positive band. -/
theorem not_allNonnegativeLimits_iff_empty_band (f : ℕ → ℝ) :
    (¬ AllNonnegativeLimits f) ↔
      ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ N : ℕ,
        ∀ k : ℕ, N ≤ k → ¬ (a < f k ∧ f k < b) := by
  classical
  rw [← bandRecurrence_iff_allNonnegativeLimits]
  simp only [BandRecurrence, not_forall, not_exists, not_and, exists_prop]

open Erdos5CoveredGapBridge

/-- The finite-limit statement is invariant under the two logarithmic normalizations. -/
theorem all_normalizations_iff :
    AllNonnegativeLimits normalizedGap ↔
      AllNonnegativeLimits primeNormalizedGap := by
  constructor <;> intro h C hC
  · obtain ⟨n, hn, ht⟩ := h C hC
    exact ⟨n, hn, (subsequence_normalizations_iff n hn C).mp ht⟩
  · obtain ⟨n, hn, ht⟩ := h C hC
    exact ⟨n, hn, (subsequence_normalizations_iff n hn C).mpr ht⟩

/-- Positive bands of actual globally consecutive prime pairs, beyond every prime height. -/
def ConsecutiveBandRecurrence : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∀ X : ℕ,
    ∃ q r : ℕ, X ≤ q ∧ ConsecutivePrimePair q r ∧
      a < (r - q : ℕ) / Real.log (q : ℝ) ∧
      (r - q : ℕ) / Real.log (q : ℝ) < b

/-- The endpoint formulation is exactly indexed prime-log band recurrence. -/
theorem consecutiveBandRecurrence_iff :
    ConsecutiveBandRecurrence ↔ BandRecurrence primeNormalizedGap := by
  constructor
  · intro h a b ha hab N
    obtain ⟨q, r, hqN, hpair, hlo, hhi⟩ := h a b ha hab (Nat.nth Nat.Prime N)
    obtain ⟨k, hkq, hkr⟩ := indexed_of_consecutive hpair
    have hNk : N ≤ k := by
      by_contra h
      have hkN : k < N := Nat.lt_of_not_ge h
      have hp := (Nat.nth_strictMono Nat.infinite_setOf_prime) hkN
      rw [hkq] at hp
      exact (not_lt_of_ge hqN) hp
    refine ⟨k, hNk, ?_, ?_⟩ <;>
      simpa only [primeNormalizedGap, primeGap, hkq, hkr] using (by assumption)
  · intro h a b ha hab X
    obtain ⟨k, hkX, hlo, hhi⟩ := h a b ha hab X
    have hqX : X ≤ Nat.nth Nat.Prime k := by
      have hp := Nat.add_two_le_nth_prime k
      omega
    refine ⟨Nat.nth Nat.Prime k, Nat.nth Nat.Prime (k + 1), hqX,
      consecutive_of_indexed k, ?_, ?_⟩ <;>
      simpa only [primeNormalizedGap, primeGap] using (by assumption)

/-- An exact reduction to the unresolved arithmetic recurrence assertion. -/
theorem index_limits_iff_consecutive_band_recurrence :
    AllNonnegativeLimits normalizedGap ↔ ConsecutiveBandRecurrence := by
  rw [consecutiveBandRecurrence_iff, bandRecurrence_iff_allNonnegativeLimits]
  exact all_normalizations_iff

end Erdos5BandCriterion
