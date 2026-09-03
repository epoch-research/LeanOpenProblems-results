import Submission.LowCountCylinder
import Submission.RowConditionalVariance

/-! The deletion-cylinder budget with the retained core applied first.
The phase-specific budget is kept explicit. No uniform upper bound on it
at quadratic length is assumed. -/
namespace Erdos970.GapAverages
open Finset Real

noncomputable def corePhase (P Q : Finset ℕ) (hQP : Q ⊆ P) (r : Phase P) : Phase Q :=
  fun q => r ⟨q.val, hQP q.property⟩

lemma point_le_core_of_agrees (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (r s : Phase P) (hs : AgreesOn P Q r s) (x : ℕ) :
    point P x s ≤ point Q x (corePhase P Q hQP r) := by
  classical
  rw [CoverFibers.point_eq_avoidance_indicator, CoverFibers.point_eq_avoidance_indicator]
  split_ifs with ha hb hb
  · rfl
  · exfalso
    apply hb
    intro q
    have hh := ha ⟨q.val, hQP q.property⟩
    simpa only [hs ⟨q.val, hQP q.property⟩ q.property, corePhase] using hh
  · norm_num
  · rfl

lemma count_le_core_of_agrees (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (m : ℕ) (r s : Phase P) (hs : AgreesOn P Q r s) :
    intervalCount P m s ≤ intervalCount Q m (corePhase P Q hQP r) :=
  sum_le_sum (fun x _ => point_le_core_of_agrees P Q hQP r s hs x)

/-- The old tail hits, counted only at positions surviving the retained core.
Tail overlaps are still counted with multiplicity. -/
noncomputable def filteredDeletionBudget (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (m : ℕ) (r : Phase P) : ℝ :=
  ∑ p : P, if p.val ∈ Q then 0 else
    rowCount Q m p.val (r p) (corePhase P Q hQP r)

lemma point_nonneg' (P : Finset ℕ) (r : Phase P) (x : ℕ) : 0 ≤ point P x r := by
  rw [CoverFibers.point_eq_avoidance_indicator]
  split_ifs <;> norm_num

lemma rowCount_nonneg' (P : Finset ℕ) (m p : ℕ) (a : Fin p) (r : Phase P) :
    0 ≤ rowCount P m p a r :=
  sum_nonneg (fun x _ => point_nonneg' P r x)

lemma rowCount_le_residueHits (Q : Finset ℕ) (m p : ℕ) (a : Fin p) (r : Phase Q) :
    rowCount Q m p a r ≤ (residueHits m p a : ℝ) := by
  classical
  calc
    _ ≤ ∑ _x ∈ (range m).filter (fun x => x % p = a.val), (1 : ℝ) := by
      apply sum_le_sum
      intro x hx
      rw [CoverFibers.point_eq_avoidance_indicator]
      split_ifs <;> norm_num
    _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one, residueHits]

/-- Applying the retained core never enlarges the raw deletion budget. -/
theorem filteredDeletionBudget_le_deletionBudget (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (r : Phase P) :
    filteredDeletionBudget P Q hQP m r ≤ deletionBudget P Q m := by
  classical
  calc
    _ ≤ ∑ p : P, if p.val ∈ Q then 0 else (m : ℝ) / p.val + 1 := by
      apply sum_le_sum
      intro p hp
      by_cases hpQ : p.val ∈ Q
      · simp only [hpQ, if_true, le_refl]
      · simp only [hpQ, if_false]
        exact (rowCount_le_residueHits Q m p.val (r p) (corePhase P Q hQP r)).trans
          (residueHits_le_real m p.val (hP p.val p.property).pos (r p))
    _ = ∑ p ∈ P, if p ∈ Q then 0 else (m : ℝ) / p + 1 :=
      sum_coe_sort P (fun p : ℕ => if p ∈ Q then 0 else (m : ℝ) / p + 1)
    _ = deletionBudget P Q m := by
      rw [deletionBudget, ← filter_notMem_eq_sdiff, sum_filter]
      simp only [ite_not]

lemma core_count_le_filteredDeletionBudget (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (m : ℕ) (r : Phase P) (hr : intervalCount P m r = 0) :
    intervalCount Q m (corePhase P Q hQP r) ≤ filteredDeletionBudget P Q hQP m r := by
  classical
  let c := corePhase P Q hQP r
  have hpoint (x : ℕ) (hx : x < m) : point Q x c ≤
      ∑ p : P, if p.val ∈ Q then 0 else
        if x % p.val = (r p).val then point Q x c else 0 := by
    have hnonneg (p : P) (_hp : p ∈ univ) :
        0 ≤ (if p.val ∈ Q then 0 else
          if x % p.val = (r p).val then point Q x c else 0) := by
      split_ifs <;> first | exact le_rfl | exact point_nonneg' Q c x
    by_cases ha : ∀ q : Q, x % q.val ≠ (c q).val
    · obtain ⟨p, hp⟩ := cover_of_count_zero P m r hr x hx
      have hpQ : p.val ∉ Q := by
        intro hpQ
        exact ha ⟨p.val, hpQ⟩ hp
      have hh := single_le_sum hnonneg (mem_univ p)
      simpa only [hpQ, if_false, hp, if_true] using hh
    · calc
        point Q x c = 0 := by rw [CoverFibers.point_eq_avoidance_indicator, if_neg ha]
        _ ≤ _ := sum_nonneg hnonneg
  have hh := sum_le_sum (fun x (hx : x ∈ range m) => hpoint x (mem_range.mp hx))
  rw [sum_comm] at hh
  change intervalCount Q m c ≤ _ at hh
  convert hh using 1
  unfold filteredDeletionBudget rowCount
  apply sum_congr rfl
  intro p hp
  by_cases hpQ : p.val ∈ Q
  · simp only [hpQ, if_true, sum_const_zero]
  · simp only [hpQ, if_false, sum_filter, c]

/-- Any change of the tail residues can expose at most the core-filtered old hits. -/
theorem count_le_filteredDeletionBudget (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (m : ℕ) (r : Phase P) (hr : intervalCount P m r = 0)
    (s : Phase P) (hs : AgreesOn P Q r s) :
    intervalCount P m s ≤ filteredDeletionBudget P Q hQP m r :=
  (count_le_core_of_agrees P Q hQP m r s hs).trans
    (core_count_le_filteredDeletionBudget P Q hQP m r hr)

/-- Retaining a phase with a small core count gives the whole cylinder, even
without assuming that the original full phase is covered. -/
theorem reciprocal_le_lowCountFraction_of_core (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (B : ℝ) (r : Phase P)
    (hB : intervalCount Q m (corePhase P Q hQP r) ≤ B) :
    (∏ p ∈ Q, (p : ℝ)⁻¹) ≤ lowCountFraction P m B := by
  have hh := phaseMean_lower_of_cylinder P Q hQP hP r
    (fun s => if intervalCount P m s ≤ B then (1 : ℝ) else 0) 1
    (fun s => by dsimp only; split_ifs <;> norm_num) (fun s hs => by
      dsimp only
      rw [if_pos ((count_le_core_of_agrees P Q hQP m r s hs).trans hB)])
  simpa only [one_mul] using hh

/-- The core-filtered budget can replace the raw deletion budget in the
low-count cylinder argument. The upper bound on that budget is a premise. -/
theorem reciprocal_le_lowCountFraction_filtered (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (B : ℝ)
    (r : Phase P) (hr : intervalCount P m r = 0)
    (hB : filteredDeletionBudget P Q hQP m r ≤ B) :
    (∏ p ∈ Q, (p : ℝ)⁻¹) ≤ lowCountFraction P m B :=
  reciprocal_le_lowCountFraction_of_core P Q hQP hP m B r
    ((core_count_le_filteredDeletionBudget P Q hQP m r hr).trans hB)

#print axioms filteredDeletionBudget_le_deletionBudget
#print axioms count_le_filteredDeletionBudget
#print axioms reciprocal_le_lowCountFraction_filtered
end Erdos970.GapAverages
