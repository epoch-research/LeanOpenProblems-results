import Submission.Certificate

/-! A divergent natural-number budget below every own-level certificate bound. -/

namespace E74

open Filter

/-- Every order is dominated by a certificate bound at a useful level. -/
theorem exists_useful_bound (n : ℕ) : ∃ k : ℕ, 2 ≤ k ∧ n ≤ ownCertificateBound k := by
  refine ⟨max 2 n, le_max_left _ _, ?_⟩
  exact (le_max_right _ _).trans (le_ownCertificateBound _)

/-- The smallest useful level whose universal bound covers the given order. -/
noncomputable def coveringLevel (n : ℕ) : ℕ := Nat.find (exists_useful_bound n)

/-- This budget tends to infinity, but is strictly below every covered useful level. -/
noncomputable def slowBudget (n : ℕ) : ℕ := coveringLevel n - 1

theorem coveringLevel_spec (n : ℕ) :
    2 ≤ coveringLevel n ∧ n ≤ ownCertificateBound (coveringLevel n) :=
  Nat.find_spec (exists_useful_bound n)

theorem slowBudget_lt {n k : ℕ} (hk : 2 ≤ k) (hn : n ≤ ownCertificateBound k) :
    slowBudget n < k := by
  have h := Nat.find_min' (exists_useful_bound n) (show 2 ≤ k ∧ n ≤ ownCertificateBound k from ⟨hk, hn⟩)
  have hpos := (coveringLevel_spec n).1
  change coveringLevel n - 1 < k
  change coveringLevel n ≤ k at h
  omega

theorem slowBudget_tendsto : Tendsto slowBudget atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro m
  refine ⟨ownCertificateBound (m + 2) + 1, ?_⟩
  intro n hn
  have hspec := (coveringLevel_spec n).2
  have hlarge : m + 2 < coveringLevel n := by
    by_contra h
    have hle : coveringLevel n ≤ m + 2 := by omega
    have hbound := ownCertificateBound_mono hle
    omega
  change m ≤ coveringLevel n - 1
  omega

end E74
