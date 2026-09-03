import Submission.RoundingExplore
import Submission.Explore

/-!
# Exact local-move identities for representation counts

These identities describe a possible repair operation. No sequence of repairs
with uniformly vanishing relative error has been constructed.
-/

namespace Erdos66LocalMoves
open AdditiveCombinatorics Erdos66Generating Erdos66Rounding

noncomputable def pointMass (a n : ℕ) : ℝ := if n = a then 1 else 0

noncomputable def shiftedIndicator (A : Set ℕ) (a n : ℕ) : ℝ :=
  if a ≤ n then indicator A (n - a) else 0

lemma pointMass_convolution (a : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    sumConv (pointMass a) f n = if a ≤ n then f (n - a) else 0 := by
  classical
  unfold sumConv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [pointMass, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range, Nat.lt_succ_iff]

lemma pointMass_square (a n : ℕ) :
    sumConv (pointMass a) (pointMass a) n = pointMass (2 * a) n := by
  rw [pointMass_convolution]
  unfold pointMass
  split_ifs <;> first | rfl | omega

lemma indicator_insert_eq {A : Set ℕ} {a : ℕ} (ha : a ∉ A) :
    indicator (insert a A) = fun n ↦ indicator A n + pointMass a n := by
  classical
  funext n
  simp only [indicator, pointMass, Set.mem_insert_iff]
  by_cases hn : n = a
  · subst n
    simp [ha]
  · simp [hn]

lemma sumRep_insert_exact {A : Set ℕ} {a : ℕ} (ha : a ∉ A) (n : ℕ) :
    (sumRep (insert a A) n : ℝ) = (sumRep A n : ℝ) +
      2 * shiftedIndicator A a n + pointMass (2 * a) n := by
  rw [← sum_indicator_antidiagonal (insert a A) n, ← sum_indicator_antidiagonal A n]
  change sumConv (indicator (insert a A)) (indicator (insert a A)) n = _
  rw [indicator_insert_eq ha, sumConv_add_self,
    sumConv_comm_real (indicator A) (pointMass a), pointMass_convolution, pointMass_square]
  rfl

/-- Both sets consist of the same core, with one different point added. -/
lemma move_exact {C : Set ℕ} {a b : ℕ} (ha : a ∉ C) (hb : b ∉ C) (n : ℕ) :
    (sumRep (insert b C) n : ℝ) - (sumRep (insert a C) n : ℝ) =
      2 * (shiftedIndicator C b n - shiftedIndicator C a n) +
        pointMass (2 * b) n - pointMass (2 * a) n := by
  rw [sumRep_insert_exact ha, sumRep_insert_exact hb]
  ring

/-- Moving one point changes any particular ordered representation count by at most two. -/
lemma move_bound (C : Set ℕ) (a b n : ℕ) :
    |(sumRep (insert b C) n : ℝ) - (sumRep (insert a C) n : ℝ)| ≤ 2 := by
  have ha0 : (sumRep C n : ℝ) ≤ (sumRep (insert a C) n : ℝ) := by
    exact_mod_cast Erdos66Explore.sumRep_mono (Set.subset_insert a C) n
  have hb0 : (sumRep C n : ℝ) ≤ (sumRep (insert b C) n : ℝ) := by
    exact_mod_cast Erdos66Explore.sumRep_mono (Set.subset_insert b C) n
  have ha1 : (sumRep (insert a C) n : ℝ) ≤ (sumRep C n : ℝ) + 2 := by
    exact_mod_cast Erdos66Explore.sumRep_insert_le C a n
  have hb1 : (sumRep (insert b C) n : ℝ) ≤ (sumRep C n : ℝ) + 2 := by
    exact_mod_cast Erdos66Explore.sumRep_insert_le C b n
  rw [abs_le]
  constructor <;> linarith

lemma shiftedIndicator_zero {C : Set ℕ} (a n : ℕ)
    (h : ¬∃ c ∈ C, a + c = n) : shiftedIndicator C a n = 0 := by
  classical
  unfold shiftedIndicator indicator
  split_ifs with ha hc
  · exact False.elim (h ⟨n - a, hc, by omega⟩)
  · rfl
  · rfl

lemma move_unchanged_outside {C : Set ℕ} {a b : ℕ} (ha : a ∉ C) (hb : b ∉ C) (n : ℕ)
    (hna : ¬∃ c ∈ C, a + c = n) (hnb : ¬∃ c ∈ C, b + c = n)
    (hn2a : n ≠ 2 * a) (hn2b : n ≠ 2 * b) :
    sumRep (insert b C) n = sumRep (insert a C) n := by
  have hh := move_exact ha hb n
  rw [shiftedIndicator_zero a n hna, shiftedIndicator_zero b n hnb] at hh
  simp only [pointMass, if_neg hn2a, if_neg hn2b] at hh
  have he : (sumRep (insert b C) n : ℝ) = (sumRep (insert a C) n : ℝ) := by linarith
  exact_mod_cast he

noncomputable def squaredError (S : Finset ℕ) (q : ℕ → ℝ) (A : Set ℕ) : ℝ :=
  ∑ n ∈ S, ((sumRep A n : ℝ) - q n) ^ 2

/-- The exact energy change includes collateral changes at every affected target. -/
lemma squaredError_change (S : Finset ℕ) (q : ℕ → ℝ) (A B : Set ℕ) :
    squaredError S q B - squaredError S q A =
      ∑ n ∈ S, (2 * ((sumRep A n : ℝ) - q n) *
        ((sumRep B n : ℝ) - (sumRep A n : ℝ)) +
          ((sumRep B n : ℝ) - (sumRep A n : ℝ)) ^ 2) := by
  unfold squaredError
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end Erdos66LocalMoves
