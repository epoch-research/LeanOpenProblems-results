import Submission.BudgetScaleFilteredRows

/-! Any quadratic-length cover forces a deep low-count phase for the complete
initial small-prime core. This is a necessary condition, not an exclusion of
such phases and not a settlement of the Jacobsthal conjecture. -/
namespace Erdos970.GapAverages
open Finset Real Filter WeightedMertens
set_option maxHeartbeats 1600000

noncomputable def initialCoreCount (z m : ℕ) (r : ℕ → ℕ) : ℝ := by
  classical
  exact (((range m).filter (fun x => ∀ p ∈ (z+1).primesBelow, ¬x ≡ r p [MOD p])).card : ℝ)

/-- The full initial core is added only for this necessary condition. The
number of primes in its complementary tail remains at most the original
budget, so no enlargement of that tail budget is hidden. -/
theorem core_count_le_fourth_deletion_ratio (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (t m : ℕ) (ht : 3 ≤ t) (hm : t^8 ≤ m)
    (hcard : P.card ≤ t^4) (r : ℕ → ℕ)
    (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) :
    initialCoreCount (t^4) m r ≤ fourthScaleDeletionRatio t*((m : ℝ)/log t) := by
  classical
  let Q := (t^4+1).primesBelow
  let S := P ∪ Q
  have hQP : Q ⊆ S := subset_union_right
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hQ p hp
  let s : Phase S := fun p => ⟨r p.val % p.val, Nat.mod_lt _ (hS p.val p.property).pos⟩
  have hs : intervalCount S m s = 0 := by
    apply count_zero_of_cover
    intro x hx
    obtain ⟨p,hp,hxp⟩ := hcover x hx
    exact ⟨⟨p,mem_union_left _ hp⟩,hxp⟩
  have htail : (S\Q).card ≤ t^4 := by
    dsimp only [S]
    rw [union_sdiff_right]
    exact (card_le_card sdiff_subset).trans hcard
  have hlarge : ∀ p ∈ S\Q, t^4 < p := by
    intro p hp
    have hpp := hS p (mem_sdiff.mp hp).1
    have hn := (mem_sdiff.mp hp).2
    have he : p ∉ (t^4+1).primesBelow := hn
    rw [Nat.mem_primesBelow] at he
    have hn : ¬p < t^4+1 := fun hp => he ⟨hp,hpp⟩
    omega
  have hfull : ∀ a, a.Prime → a ≤ t → a ∈ Q := by
    intro a ha hat
    exact mem_primes.mpr ⟨ha,hat.trans (Nat.le_self_pow (by norm_num) t)⟩
  have hh := (core_count_le_filteredDeletionBudget S Q hQP m s hs).trans
    (filteredDeletionBudget_le_fourth_scale S Q hQP hS t m ht hm htail hlarge hfull s)
  have he : intervalCount Q m (corePhase S Q hQP s) = initialCoreCount (t^4) m r := by
    rw [← CoverFibers.phaseSurvivors_card]
    unfold initialCoreCount
    congr 2
    ext x
    simp only [CoverFibers.phaseSurvivors,mem_filter,corePhase,s,Nat.ModEq]
    constructor
    · rintro ⟨hx,ha⟩
      exact ⟨hx,fun p hp => ha ⟨p,hp⟩⟩
    · rintro ⟨hx,ha⟩
      exact ⟨hx,fun p => ha p.val p.property⟩
  rwa [he] at hh

/-- Uniform deep-deficit necessity: for every positive fraction, all sufficiently
large quadratic-length covers would have a complete initial core with count
below that fraction of m/log t. No lower bound for that core is assumed. -/
theorem eventually_cover_forces_initial_core_deficit (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ t^4 →
      ∀ m : ℕ, t^8 ≤ m → ∀ r : ℕ → ℕ,
        (∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) →
        initialCoreCount (t^4) m r ≤ ε*((m : ℝ)/log t) := by
  have he := (fourthScaleDeletionRatio_tendsto_zero.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_lt_nhds hε)
  filter_upwards [he,eventually_ge_atTop 3] with t ht h3
  intro P hP hcard m hm r hcover
  apply (core_count_le_fourth_deletion_ratio P hP t m h3 hm hcard r hcover).trans
  exact mul_le_mul_of_nonneg_right ht.le
    (div_nonneg (Nat.cast_nonneg m) (log_natCast_nonneg t))

#print axioms core_count_le_fourth_deletion_ratio
#print axioms eventually_cover_forces_initial_core_deficit
end Erdos970.GapAverages
