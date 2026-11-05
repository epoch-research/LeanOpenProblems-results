import Submission.Compactness

/-!
# Counting-profile reduction for the infinite Sidon question

The compactness reduction is combined with the real-power growth condition. The
result isolates a uniform finite-prefix existence statement; it does not establish
that finite existence statement.
-/

namespace Erdos39

open Filter Asymptotics

/-- The number of positive members of `A` up to `N`. -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Set.Icc 1 N ∩ A).ncard

/-- A natural-valued counting profile with the powers required in the question. -/
def NearSquareRootProfile (b : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 - ε)) =O[atTop]
      (fun N => (b N : ℝ))

/-- The positive quarter-power estimate already makes the profile unbounded. -/
theorem NearSquareRootProfile.unbounded {b : ℕ → ℕ} (h : NearSquareRootProfile b) :
    ∀ M : ℕ, ∃ N : ℕ, M < b N := by
  have hquarter := h (1 / 4) (by norm_num)
  obtain ⟨c, hc, hbound⟩ := isBigO_iff'.mp hquarter
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] at hbound
  have htop : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  intro M
  obtain ⟨N, hN, hlarge⟩ := (hbound.and (htop.eventually_gt_atTop (c * (M : ℝ)))).exists
  refine ⟨N, ?_⟩
  by_contra! hle
  have hmul : c * (b N : ℝ) ≤ c * (M : ℝ) :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hle) hc.le
  linarith

/-- Pointwise domination transfers a counting profile to a set. -/
theorem NearSquareRootProfile.of_le {b : ℕ → ℕ} {A : Set ℕ}
    (h : NearSquareRootProfile b) (hb : ∀ N, b N ≤ countingFunction A N) :
    NearSquareRootProfile (countingFunction A) := by
  intro ε hε
  refine (h ε hε).trans (isBigO_of_le atTop fun N => ?_)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
    (Nat.cast_le.mpr (hb N) : (b N : ℝ) ≤ (countingFunction A N : ℝ))

/-- A set with the required profile is necessarily infinite. -/
theorem infinite_of_counting_profile {A : Set ℕ}
    (h : NearSquareRootProfile (countingFunction A)) : A.Infinite := by
  by_contra hnot
  have hfinite : A.Finite := Set.not_infinite.mp hnot
  obtain ⟨N, hN⟩ := h.unbounded A.ncard
  have hle : countingFunction A N ≤ A.ncard :=
    Set.ncard_le_ncard Set.inter_subset_right hfinite
  omega

/-- Uniform finite-prefix witnesses for one near-square-root profile suffice for
an infinite Sidon set with exactly the growth condition in the question. -/
theorem exists_sidon_of_finite_prefix_profile (b : ℕ → ℕ)
    (hgrowth : NearSquareRootProfile b)
    (hfinite : ∀ K : ℕ, ∃ B : Finset ℕ, IsSidon (B : Set ℕ) ∧
      ∀ N ≤ K, b N ≤ (Set.Icc 1 N ∩ (B : Set ℕ)).ncard) :
    ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 - ε)) =O[atTop]
          (fun N => ((Set.Icc 1 N ∩ A).ncard : ℝ)) := by
  obtain ⟨A, hsidon, hcount⟩ := finite_prefix_compactness b hfinite
  have hprofile : NearSquareRootProfile (countingFunction A) :=
    hgrowth.of_le hcount
  exact ⟨A, infinite_of_counting_profile hprofile, hsidon, hprofile⟩

/-- The infinite assertion is equivalent to the existence of a single prescribed
counting profile realized through every finite cutoff. Endpoint-only finite bounds
are not the premise of this equivalence. -/
theorem sidon_growth_iff_finite_prefix_profile :
    (∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 - ε)) =O[atTop]
          (fun N => ((Set.Icc 1 N ∩ A).ncard : ℝ))) ↔
    ∃ b : ℕ → ℕ, NearSquareRootProfile b ∧
      ∀ K : ℕ, ∃ B : Finset ℕ, IsSidon (B : Set ℕ) ∧
        ∀ N ≤ K, b N ≤ (Set.Icc 1 N ∩ (B : Set ℕ)).ncard := by
  constructor
  · rintro ⟨A, _, hsidon, hgrowth⟩
    refine ⟨countingFunction A, hgrowth, ?_⟩
    intro K
    let hfin : (Set.Icc 1 K ∩ A).Finite := (Set.finite_Icc 1 K).inter_of_left A
    let B : Finset ℕ := hfin.toFinset
    have hB : (B : Set ℕ) = Set.Icc 1 K ∩ A := by simp [B]
    refine ⟨B, Set.IsSidon.subset hsidon ?_, ?_⟩
    · rw [hB]
      exact Set.inter_subset_right
    · intro N hNK
      have heq : Set.Icc 1 N ∩ (B : Set ℕ) = Set.Icc 1 N ∩ A := by
        rw [hB]
        ext n
        simp only [Set.mem_inter_iff, Set.mem_Icc]
        constructor
        · rintro ⟨hn, _, hA⟩
          exact ⟨hn, hA⟩
        · rintro ⟨hn, hA⟩
          exact ⟨hn, ⟨hn.1, hn.2.trans hNK⟩, hA⟩
      rw [heq]
      exact le_rfl
  · rintro ⟨b, hgrowth, hfinite⟩
    exact exists_sidon_of_finite_prefix_profile b hgrowth hfinite

#print axioms sidon_growth_iff_finite_prefix_profile

end Erdos39
