import Submission.GapBridge
import Submission.EfficientCover.EfficientCRT

/-!
# Arbitrarily large normalized prime gaps

The efficient residue cover produces prime-free intervals whose length is any
fixed multiple of their logarithmic height. They yield actual indexed prime
gaps tending to infinity after normalization by the logarithm of the index.
This proves an infinite-limit variant, not any prescribed finite positive limit.
-/

open Filter
open scoped Topology
open Erdos5CoveredGapBridge

namespace Erdos5LargeNormalizedGaps

/-- A composite interval lies in an actual consecutive indexed prime gap. -/
theorem indexed_gap_of_composite_interval (m L : ℕ) (hm : 2 ≤ m)
    (hcover : ∀ s : ℕ, 0 < s → s ≤ L → ¬ Nat.Prime (m + s)) :
    ∃ k : ℕ, Nat.nth Nat.Prime k ≤ m ∧ m < Nat.nth Nat.Prime (k + 1) ∧
      L ≤ primeGap k := by
  let t := Nat.count Nat.Prime (m + 1)
  have ht : 0 < t := by
    have h2 : Nat.count Nat.Prime (2 + 1) = 1 := by
      simpa only [Nat.nth_prime_zero_eq_two] using
        Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime 0
    have hmono := Nat.count_monotone Nat.Prime (show 2 + 1 ≤ m + 1 by omega)
    change Nat.count Nat.Prime (2 + 1) ≤ t at hmono
    rw [h2] at hmono
    omega
  let k := t - 1
  have hkt : k + 1 = t := by dsimp [k]; omega
  have hleft : Nat.nth Nat.Prime k ≤ m := by
    have hk : k < Nat.count Nat.Prime (m + 1) := by change k < t; dsimp [k]; omega
    have h := Nat.nth_lt_of_lt_count hk
    omega
  have hright : m < Nat.nth Nat.Prime (k + 1) := by
    rw [hkt]
    have h := Nat.le_nth_count Nat.infinite_setOf_prime (m + 1)
    change m + 1 ≤ Nat.nth Nat.Prime t at h
    omega
  have hfar : m + L < Nat.nth Nat.Prime (k + 1) := by
    by_contra h
    have hlo : 0 < Nat.nth Nat.Prime (k + 1) - m := by omega
    have hhi : Nat.nth Nat.Prime (k + 1) - m ≤ L := by omega
    have hcomp := hcover (Nat.nth Nat.Prime (k + 1) - m) hlo hhi
    have hsum : m + (Nat.nth Nat.Prime (k + 1) - m) = Nat.nth Nat.Prime (k + 1) := by omega
    rw [hsum] at hcomp
    exact hcomp (Nat.prime_nth_prime _)
  refine ⟨k, hleft, hright, ?_⟩
  unfold primeGap
  omega

/-- The normalization can exceed any real threshold at arbitrarily large indices. -/
theorem arbitrarily_late_large_normalized_gap (R : ℝ) (N : ℕ) :
    ∃ k : ℕ, N < k ∧ R < normalizedGap k := by
  let D : ℝ := 2 + Real.log 4
  have hD : 0 < D := by
    have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    dsimp [D]
    linarith
  obtain ⟨c, hc⟩ := exists_nat_gt (max 1 (max 0 R * D))
  have hc1 : 1 ≤ c := by
    have h : (1 : ℝ) < c := (le_max_left _ _).trans_lt hc
    exact_mod_cast h.le
  have hcR : max 0 R * D < c := (le_max_right _ _).trans_lt hc
  obtain ⟨Y, hY⟩ := Erdos5EfficientCover.efficient_crt_interval c hc1
  let y := max Y (max 2 (Nat.nth Nat.Prime (N + 2)))
  have hyY : Y ≤ y := le_max_left _ _
  have hy2 : 2 ≤ y := (le_max_left _ _).trans (le_max_right _ _)
  have hyp : Nat.nth Nat.Prime (N + 2) ≤ y :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨m, hm2, hym, _, hlogm, hcover⟩ := hY y hyY
  obtain ⟨k, hleft, hright, hgap⟩ := indexed_gap_of_composite_interval m (c * y) hm2 hcover
  have hkN : N + 1 < k := by
    by_contra h
    have hk : k + 1 ≤ N + 2 := by omega
    have hprime : Nat.nth Nat.Prime (k + 1) ≤ Nat.nth Nat.Prime (N + 2) :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hk
    exact (not_le_of_gt hright) (hprime.trans (hyp.trans hym.le))
  have hk2 : 2 ≤ k := by omega
  have hkm : k ≤ m := by
    have hlow := Nat.add_two_le_nth_prime k
    omega
  have hlogk : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hlogs : Real.log (k : ℝ) ≤ D * (y : ℝ) := by
    exact (Real.log_le_log (by positivity) (by exact_mod_cast hkm)).trans hlogm
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hprod : R * Real.log (k : ℝ) < (c : ℝ) * y := by
    calc
      R * Real.log (k : ℝ) ≤ max 0 R * Real.log (k : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hlogk.le
      _ ≤ max 0 R * (D * (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogs (le_max_left _ _)
      _ = (max 0 R * D) * (y : ℝ) := by ring
      _ < (c : ℝ) * y := mul_lt_mul_of_pos_right hcR hypos
  refine ⟨k, by omega, ?_⟩
  unfold normalizedGap
  apply (lt_div_iff₀ hlogk).mpr
  have hgap' : (c : ℝ) * y ≤ (primeGap k : ℝ) := by exact_mod_cast hgap
  exact hprod.trans_le hgap'

/-- The normalized gaps exceed every fixed threshold frequently. -/
theorem frequently_large_normalized_gap (R : ℝ) :
    ∃ᶠ k : ℕ in atTop, R < normalizedGap k := by
  apply frequently_atTop.mpr
  intro N
  obtain ⟨k, hk, hR⟩ := arbitrarily_late_large_normalized_gap R N
  exact ⟨k, hk.le, hR⟩

/-- A strictly increasing index subsequence of normalized gaps tends to infinity. -/
theorem exists_strictMono_normalized_gaps_tendsto_atTop :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun i => normalizedGap (n i)) atTop atTop := by
  have hf : ∀ i : ℕ, ∃ᶠ k : ℕ in atTop, (i : ℝ) ≤ normalizedGap k := by
    intro i
    exact (frequently_large_normalized_gap (i : ℝ)).mono fun _ h => h.le
  obtain ⟨n, hn, hbound⟩ := extraction_forall_of_frequently hf
  exact ⟨n, hn, tendsto_atTop_mono hbound tendsto_natCast_atTop_atTop⟩

end Erdos5LargeNormalizedGaps

#print axioms Erdos5LargeNormalizedGaps.indexed_gap_of_composite_interval
#print axioms Erdos5LargeNormalizedGaps.arbitrarily_late_large_normalized_gap
#print axioms Erdos5LargeNormalizedGaps.frequently_large_normalized_gap
#print axioms Erdos5LargeNormalizedGaps.exists_strictMono_normalized_gaps_tendsto_atTop
