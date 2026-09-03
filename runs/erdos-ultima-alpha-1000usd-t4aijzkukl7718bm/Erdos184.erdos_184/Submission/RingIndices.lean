import Submission.TriangleExclusion

/-! Index manipulations for cyclic cycle-contact families. -/
open SimpleGraph
namespace Erdos184Work.RingIndices
set_option maxHeartbeats 1000000

abbrev skipOne {n : ℕ} : Fin (n+3) → Fin (n+4) := (1 : Fin (n+4)).succAbove

lemma skipOne_zero (n : ℕ) : skipOne (0 : Fin (n+3)) = 0 := rfl
lemma skipOne_one (n : ℕ) : skipOne (1 : Fin (n+3)) = 2 := by simp [skipOne]
lemma skipOne_ne_one {n : ℕ} (i : Fin (n+3)) : skipOne i ≠ 1 := Fin.succAbove_ne _ _

lemma skipOne_injective (n : ℕ) : Function.Injective (@skipOne n) :=
  Fin.succAbove_right_injective

lemma skipOne_val {n : ℕ} (i : Fin (n+3)) :
    (skipOne i).val = if i.val = 0 then 0 else i.val + 1 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩
  · rfl
  · simp [skipOne]

lemma skipOne_add_one {n : ℕ} (i : Fin (n+3)) (hi : i ≠ 0) :
    skipOne (i+1) = skipOne i + 1 := by
  apply Fin.ext
  have hi0 : i.val ≠ 0 := by simpa using hi
  simp only [skipOne_val,Fin.val_add_eq_ite,Fin.val_one]
  split_ifs <;> omega

lemma skipOne_eq_zero_iff {n : ℕ} (i : Fin (n+3)) : skipOne i = 0 ↔ i = 0 := by
  rw [← skipOne_zero n, (skipOne_injective n).eq_iff]
lemma skipOne_eq_two_iff {n : ℕ} (i : Fin (n+3)) : skipOne i = 2 ↔ i = 1 := by
  rw [← skipOne_one n, (skipOne_injective n).eq_iff]

lemma next_ne (n : ℕ) (i : Fin (n+3)) : i + 1 ≠ i := by
  intro h
  have he : (1 : Fin (n+3)) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using h)
  exact Fin.zero_ne_one he.symm

#print axioms skipOne_add_one
end Erdos184Work.RingIndices
