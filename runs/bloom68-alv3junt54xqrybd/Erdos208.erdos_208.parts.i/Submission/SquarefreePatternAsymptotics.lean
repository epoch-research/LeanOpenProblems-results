import Submission.SquarefreePatternCriteria
import Submission.GapCriteria

/-!
# Conditional squarefree gaps from fixed-pattern asymptotics

The pattern estimates in this file are explicit hypotheses, not established
counting results.  For a fixed exponent and pattern size, finitely many little-o
estimates give the strict counting premise of the finite interval criterion.
This yields an interval bound with constant `2`.  Assuming such estimates for
every exponent strictly between `0` and `1` then gives the all-positive-exponent
squarefree-gap bound.  This is a conditional implication, not a settlement of
the unconditional gap conjecture.
-/

open Filter

namespace SquarefreePatternCriteria

/-- For every bounded-width pattern of size `k`, the number of starts with
large-prime-square witnesses is little-o of the proposed interval length. -/
def PatternEstimate (δ : ℝ) (k : ℕ) : Prop :=
  ∀ I : Finset ℕ, I ⊆ Finset.Icc 1 (24 * k) → I.card = k →
    (fun N : ℕ => ((patternStarts N ⌈(N : ℝ) ^ δ⌉₊ I).card : ℝ))
      =o[atTop] (fun N : ℕ => (N : ℝ) ^ δ)

/-- Finiteness of the pattern list makes the little-o estimates simultaneous.
The fixed loss `patternConstant k` is absorbed before taking the bound. -/
lemma eventually_pattern_half_bound {δ : ℝ} {k : ℕ}
    (hestimate : PatternEstimate δ k) :
    ∀ᶠ N : ℕ in atTop, ∀ I : Finset ℕ,
      I ⊆ Finset.Icc 1 (24 * k) → I.card = k →
        (patternConstant k : ℝ) *
            ((patternStarts N ⌈(N : ℝ) ^ δ⌉₊ I).card : ℝ) ≤
          (N : ℝ) ^ δ / 2 := by
  classical
  let P := (Finset.Icc 1 (24 * k)).powersetCard k
  have hfinite : ∀ᶠ N : ℕ in atTop, ∀ I ∈ P,
      (patternConstant k : ℝ) *
          ((patternStarts N ⌈(N : ℝ) ^ δ⌉₊ I).card : ℝ) ≤
        (N : ℝ) ^ δ / 2 := by
    apply (Filter.eventually_all_finset P).mpr
    intro I hI
    obtain ⟨hIsub, hIcard⟩ := Finset.mem_powersetCard.mp hI
    have hsmall := (hestimate I hIsub hIcard).const_mul_left (patternConstant k : ℝ)
    filter_upwards [hsmall.bound (show 0 < (1 / 2 : ℝ) by norm_num)] with N hN
    have hnonneg : 0 ≤ (patternConstant k : ℝ) *
        ((patternStarts N ⌈(N : ℝ) ^ δ⌉₊ I).card : ℝ) := by positivity
    have hpow_nonneg : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg N) δ
    rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hpow_nonneg] at hN
    linarith
  filter_upwards [hfinite] with N hN
  intro I hIsub hIcard
  exact hN I (Finset.mem_powersetCard.mpr ⟨hIsub, hIcard⟩)

/-- One explicit pattern-estimate hypothesis yields a short-interval bound.
The proof uses interval length `⌈N^δ⌉₊`, with implicit constant `2`. -/
theorem intervalBound_of_patternEstimate {δ : ℝ} {k : ℕ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hk : 0 < k)
    (hestimate : PatternEstimate δ k) : SquarefreeCriteria.IntervalBound δ := by
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop,
      ∃ m : ℕ, Squarefree m ∧ N < m ∧
        (m : ℝ) - (N : ℝ) ≤ 2 * (N : ℝ) ^ δ := by
    filter_upwards [eventually_pattern_half_bound hestimate,
      hlim.eventually (eventually_ge_atTop ((48 * k : ℕ) : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with N hcount hlarge hN
    let H : ℕ := ⌈(N : ℝ) ^ δ⌉₊
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hpowpos : 0 < (N : ℝ) ^ δ :=
      Real.rpow_pos_of_pos (by linarith) δ
    have hH : 48 * k ≤ H := by
      exact_mod_cast hlarge.trans (Nat.le_ceil ((N : ℝ) ^ δ))
    have hHN : H ≤ N :=
      Nat.ceil_le.mpr (Real.rpow_le_self_of_one_le hNreal hδ1.le)
    have hstrict : ∀ I : Finset ℕ,
        I ⊆ Finset.Icc 1 (24 * k) → I.card = k →
          patternConstant k * (patternStarts N H I).card < H := by
      intro I hIsub hIcard
      have hreal : (patternConstant k : ℝ) * ((patternStarts N H I).card : ℝ) <
          (H : ℝ) := calc
        _ ≤ (N : ℝ) ^ δ / 2 := hcount I hIsub hIcard
        _ < (N : ℝ) ^ δ := by linarith
        _ ≤ (H : ℝ) := Nat.le_ceil ((N : ℝ) ^ δ)
      exact_mod_cast hreal
    obtain ⟨m, hNm, hmH, hmsf⟩ :=
      exists_squarefree_of_pattern_bound N H k hk hH hHN hstrict
    refine ⟨m, hmsf, hNm, ?_⟩
    have hmreal : (m : ℝ) ≤ (N : ℝ) + (H : ℝ) := by exact_mod_cast hmH
    have hceil : (H : ℝ) < (N : ℝ) ^ δ + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) δ)
    have hone : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hNreal hδ.le
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  exact ⟨2, by norm_num, N, hN⟩

/-- CONDITIONAL all-positive-exponent gap theorem.  The fixed-pattern
little-o estimates are an explicit premise for each `0 < δ < 1`. -/
theorem all_exponent_gaps_of_patternEstimates
    (hestimate : ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ k : ℕ, 0 < k ∧ PatternEstimate δ k) :
    ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ => ((Nat.nth Squarefree (n + 1) : ℝ) -
          (Nat.nth Squarefree n : ℝ)))
        =O[atTop] (fun n : ℕ => (Nat.nth Squarefree n : ℝ) ^ ε) := by
  have hunit : ∀ ε > (0 : ℝ), SquarefreeCriteria.UnitIntervals ε := by
    intro ε hε
    let δ : ℝ := min (ε / 2) (1 / 2)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (by linarith) (by norm_num)
    have hδ1 : δ < 1 :=
      (min_le_right (ε / 2) (1 / 2)).trans_lt (by norm_num)
    have hδε : δ < ε :=
      (min_le_left (ε / 2) (1 / 2)).trans_lt (by linarith)
    obtain ⟨k, hk, hkestimate⟩ := hestimate δ hδ hδ1
    exact SquarefreeCriteria.unitIntervals_of_intervalBound_lt hδε
      (intervalBound_of_patternEstimate hδ hδ1 hk hkestimate)
  simpa only [SquarefreeSqrt.s] using
    (SquarefreeCriteria.all_exponents_iff_unitIntervals.mpr hunit)

end SquarefreePatternCriteria

#print axioms SquarefreePatternCriteria.eventually_pattern_half_bound
#print axioms SquarefreePatternCriteria.intervalBound_of_patternEstimate
#print axioms SquarefreePatternCriteria.all_exponent_gaps_of_patternEstimates
