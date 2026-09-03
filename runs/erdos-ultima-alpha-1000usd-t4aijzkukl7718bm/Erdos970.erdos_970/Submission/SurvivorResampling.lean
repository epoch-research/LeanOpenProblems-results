import Submission.OptimalCoverCore
import Submission.GapPhaseMoments

/-!
Exact one-coordinate resampling identities for finite survivor populations.
The private-position contribution is retained, including at a covered phase.
No unproved concentration estimate or quadratic Jacobsthal bound is used.
-/
namespace Erdos970.Resampling
open Finset

noncomputable def residueMean (p : ℕ) (f : Fin p → ℝ) : ℝ := (∑ a, f a) / p

lemma residueMean_add (p : ℕ) (f g : Fin p → ℝ) :
    residueMean p (fun a => f a + g a) = residueMean p f + residueMean p g := by
  simp only [residueMean, sum_add_distrib, add_div]

lemma residueMean_sub (p : ℕ) (f g : Fin p → ℝ) :
    residueMean p (fun a => f a - g a) = residueMean p f - residueMean p g := by
  simp only [residueMean, sum_sub_distrib, sub_div]

lemma residueMean_mul (p : ℕ) (c : ℝ) (f : Fin p → ℝ) :
    residueMean p (fun a => c * f a) = c * residueMean p f := by
  simp only [residueMean, ← mul_sum]
  ring

lemma residueMean_const (p : ℕ) (hp : 0 < p) (c : ℝ) :
    residueMean p (fun _ => c) = c := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp [residueMean, hpR]

lemma residueMean_indicator (p : ℕ) (b : Fin p) :
    residueMean p (fun a => if a = b then (1 : ℝ) else 0) = 1 / p := by
  simp [residueMean]

lemma residueMean_off_diagonal (p : ℕ) (hp : 0 < p) (b : Fin p) (c : ℝ) :
    residueMean p (fun a => if a = b then 0 else c) = (1 - 1 / p) * c := by
  have he (a : Fin p) : (if a = b then (0 : ℝ) else c) =
      c - c * (if a = b then 1 else 0) := by split_ifs <;> ring
  simp_rw [he]
  rw [residueMean_sub, residueMean_const p hp, residueMean_mul, residueMean_indicator]
  ring

lemma residueMean_centered_square (p : ℕ) (hp : 0 < p) (f : Fin p → ℝ) :
    residueMean p (fun a => (f a - residueMean p f) ^ 2) =
      residueMean p (fun a => (f a) ^ 2) - (residueMean p f) ^ 2 := by
  have he (a : Fin p) : (f a - residueMean p f) ^ 2 =
      (f a) ^ 2 - (2 * residueMean p f) * f a + (residueMean p f) ^ 2 := by ring
  simp_rw [he]
  rw [residueMean_add, residueMean_sub, residueMean_mul, residueMean_const p hp]
  ring

noncomputable def classHits (S : Finset ℕ) (p : ℕ) (a : Fin p) : ℝ :=
  ∑ x ∈ S, if x % p = a.val then 1 else 0

def avoidClass (S : Finset ℕ) (p : ℕ) (a : Fin p) : Finset ℕ :=
  S.filter (fun x => x % p ≠ a.val)

noncomputable def remainingCount (S : Finset ℕ) (p : ℕ) (a : Fin p) : ℝ :=
  (avoidClass S p a).card

lemma classHits_nonneg (S : Finset ℕ) (p : ℕ) (a : Fin p) : 0 ≤ classHits S p a := by
  apply sum_nonneg
  intro x hx
  split_ifs <;> norm_num

lemma classHits_card (S : Finset ℕ) (p : ℕ) (a : Fin p) :
    classHits S p a = ((S.filter (fun x => x % p = a.val)).card : ℝ) := by
  simp only [classHits, sum_boole]

lemma remainingCount_eq (S : Finset ℕ) (p : ℕ) (a : Fin p) :
    remainingCount S p a = (S.card : ℝ) - classHits S p a := by
  have h := card_filter_add_card_filter_not (s := S) (fun x => x % p = a.val)
  have hh : ((S.filter (fun x => x % p = a.val)).card : ℝ) +
      ((S.filter (fun x => x % p ≠ a.val)).card : ℝ) = S.card := by exact_mod_cast h
  rw [classHits_card]
  dsimp only [remainingCount, avoidClass]
  linarith

lemma classHits_mean (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    residueMean p (classHits S p) = (S.card : ℝ) / p := by
  unfold residueMean classHits
  rw [sum_comm]
  simp only [GapAverages.coordinate_hit_sum p _ hp, sum_const, nsmul_eq_mul, mul_one]

lemma remainingCount_mean (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    residueMean p (remainingCount S p) = (1 - 1 / p) * S.card := by
  change residueMean p (fun a => remainingCount S p a) = _
  simp_rw [remainingCount_eq]
  rw [residueMean_sub, residueMean_const p hp, classHits_mean S p hp]
  ring

lemma classHits_avoided (S : Finset ℕ) (p : ℕ) (b : Fin p) :
    classHits (avoidClass S p b) p b = 0 := by
  apply sum_eq_zero
  intro x hx
  exact if_neg (mem_filter.mp hx).2

/-- Splitting off the old hit class leaves the old survivors. -/
lemma classHits_split (S : Finset ℕ) (p : ℕ) (a b : Fin p) :
    classHits S p a = classHits (avoidClass S p b) p a +
      if a = b then classHits S p b else 0 := by
  by_cases hab : a = b
  · subst a
    rw [if_pos rfl, classHits_avoided, zero_add]
  · rw [if_neg hab, add_zero]
    unfold classHits avoidClass
    rw [sum_filter]
    apply sum_congr rfl
    intro x hx
    by_cases hxa : x % p = a.val
    · have hxb : x % p ≠ b.val := fun hh => hab (Fin.ext (hxa.symm.trans hh))
      simp only [if_pos hxb, if_pos hxa]
    · simp [hxa]

/-- Resampling exposes private positions, except when the old residue is
chosen again, and deletes whichever old survivors the new residue hits. -/
theorem resampling_increment (S : Finset ℕ) (p : ℕ) (a b : Fin p) :
    remainingCount S p a - remainingCount S p b =
      (if a = b then 0 else classHits S p b) - classHits (avoidClass S p b) p a := by
  rw [remainingCount_eq, remainingCount_eq, classHits_split S p a b]
  split_ifs <;> ring

/-- A downward change is controlled by hits among the current survivors. -/
theorem downward_change_le (S : Finset ℕ) (p : ℕ) (a b : Fin p) :
    max (remainingCount S p b - remainingCount S p a) 0 ≤
      classHits (avoidClass S p b) p a := by
  have h := resampling_increment S p a b
  have hb := classHits_nonneg S p b
  have hu := classHits_nonneg (avoidClass S p b) p a
  apply max_le
  · split_ifs at h <;> linarith
  · exact hu

/-- An upward change instead involves the old private positions. -/
theorem upward_change_le (S : Finset ℕ) (p : ℕ) (a b : Fin p) :
    max (remainingCount S p a - remainingCount S p b) 0 ≤ classHits S p b := by
  have h := resampling_increment S p a b
  have hb := classHits_nonneg S p b
  have hu := classHits_nonneg (avoidClass S p b) p a
  apply max_le
  · split_ifs at h <;> linarith
  · exact hb

lemma increment_mean (S : Finset ℕ) (p : ℕ) (hp : 0 < p) (b : Fin p) :
    residueMean p (fun a => remainingCount S p a - remainingCount S p b) =
      (1 - 1 / p) * classHits S p b - (avoidClass S p b).card / p := by
  simp_rw [resampling_increment]
  rw [residueMean_sub, residueMean_off_diagonal p hp,
    classHits_mean (avoidClass S p b) p hp]

/-- Exact uncentered second moment. The mixed term is negative and is not
replaced by a triangle inequality. -/
theorem increment_second_moment (S : Finset ℕ) (p : ℕ) (hp : 0 < p) (b : Fin p) :
    residueMean p (fun a => (remainingCount S p a - remainingCount S p b) ^ 2) =
      (1 - 1 / p) * (classHits S p b) ^ 2 -
      2 * classHits S p b * ((avoidClass S p b).card : ℝ) / p +
      residueMean p (fun a => (classHits (avoidClass S p b) p a) ^ 2) := by
  have he (a : Fin p) : (remainingCount S p a - remainingCount S p b) ^ 2 =
      (if a = b then 0 else (classHits S p b) ^ 2) -
      (2 * classHits S p b) * classHits (avoidClass S p b) p a +
      (classHits (avoidClass S p b) p a) ^ 2 := by
    rw [resampling_increment]
    by_cases hab : a = b
    · subst a
      simp [classHits_avoided]
    · simp only [if_neg hab]
      ring
  simp_rw [he]
  rw [residueMean_add, residueMean_sub, residueMean_off_diagonal p hp,
    residueMean_mul, classHits_mean (avoidClass S p b) p hp]
  ring

/-- The exact centered variance separates the variance of current-survivor
class counts from the private-position correction. -/
theorem increment_variance (S : Finset ℕ) (p : ℕ) (hp : 0 < p) (b : Fin p) :
    residueMean p (fun a =>
      ((remainingCount S p a - remainingCount S p b) -
        residueMean p (fun c => remainingCount S p c - remainingCount S p b)) ^ 2) =
      residueMean p (fun a =>
        (classHits (avoidClass S p b) p a - ((avoidClass S p b).card : ℝ) / p) ^ 2) +
      (((p : ℝ) - 1) * (classHits S p b) ^ 2 -
        2 * classHits S p b * ((avoidClass S p b).card : ℝ)) / (p : ℝ) ^ 2 := by
  rw [residueMean_centered_square p hp, increment_second_moment S p hp b,
    increment_mean S p hp b]
  have he := residueMean_centered_square p hp (classHits (avoidClass S p b) p)
  rw [classHits_mean (avoidClass S p b) p hp] at he
  rw [he]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
  <;> ring

/-- At a covered phase all resampling variation comes from private positions. -/
theorem covered_resampling (S : Finset ℕ) (p : ℕ) (b : Fin p)
    (hzero : avoidClass S p b = ∅) (a : Fin p) :
    remainingCount S p a = if a = b then 0 else classHits S p b := by
  have h := resampling_increment S p a b
  have hb : remainingCount S p b = 0 := by simp [remainingCount, hzero]
  have hu : classHits (avoidClass S p b) p a = 0 := by simp [hzero, classHits]
  simpa only [hb, hu, sub_zero] using h

/-- Consequently the conditional second moment need not vanish when the
current survivor count is zero. -/
theorem covered_increment_second_moment (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (b : Fin p) (hzero : avoidClass S p b = ∅) :
    residueMean p (fun a => (remainingCount S p a - remainingCount S p b) ^ 2) =
      (1 - 1 / p) * (classHits S p b) ^ 2 := by
  rw [increment_second_moment S p hp b]
  simp [hzero, classHits, residueMean]

#print axioms resampling_increment
#print axioms downward_change_le
#print axioms upward_change_le
#print axioms increment_second_moment
#print axioms increment_variance
#print axioms covered_increment_second_moment
end Erdos970.Resampling
