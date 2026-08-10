import FormalConjectures.Util.ProblemImports

open Nat

/--
A273917: Number of ordered ways to write $n$ as $w^2 + 3x^2 + y^4 + z^5$, where $w$ is a positive integer and $x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun w =>
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if w > 0 ∧ w^2 + 3 * x^2 + y^4 + z^5 = n then 1 else 0


lemma a_pos_of_repr {n w x y z : ℕ} (hw : w > 0)
    (h : w^2 + 3 * x^2 + y^4 + z^5 = n) : a n > 0 := by
  dsimp [a]
  have hwle : w ≤ n := by
    calc
      w ≤ w^2 := Nat.le_pow (by norm_num : 0 < 2)
      _ ≤ w^2 + 3 * x^2 + y^4 + z^5 := by omega
      _ = n := h
  have hxle : x ≤ n := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · calc
        x ≤ x^2 := Nat.le_pow (by norm_num : 0 < 2)
        _ ≤ 3 * x^2 := by omega
        _ ≤ w^2 + 3 * x^2 + y^4 + z^5 := by omega
        _ = n := h
  have hyle : y ≤ n := by
    by_cases hy0 : y = 0
    · simp [hy0]
    · calc
        y ≤ y^4 := Nat.le_pow (by norm_num : 0 < 4)
        _ ≤ w^2 + 3 * x^2 + y^4 + z^5 := by omega
        _ = n := h
  have hzle : z ≤ n := by
    by_cases hz0 : z = 0
    · simp [hz0]
    · calc
        z ≤ z^5 := Nat.le_pow (by norm_num : 0 < 5)
        _ ≤ w^2 + 3 * x^2 + y^4 + z^5 := by omega
        _ = n := h
  apply Finset.sum_pos'
  · intro w' _
    apply Finset.sum_nonneg
    intro x' _
    apply Finset.sum_nonneg
    intro y' _
    apply Finset.sum_nonneg
    intro z' _
    split <;> omega
  · refine ⟨w, Finset.mem_range.mpr (Nat.lt_succ_of_le hwle), ?_⟩
    apply Finset.sum_pos'
    · intro x' _
      apply Finset.sum_nonneg
      intro y' _
      apply Finset.sum_nonneg
      intro z' _
      split <;> omega
    · refine ⟨x, Finset.mem_range.mpr (Nat.lt_succ_of_le hxle), ?_⟩
      apply Finset.sum_pos'
      · intro y' _
        apply Finset.sum_nonneg
        intro z' _
        split <;> omega
      · refine ⟨y, Finset.mem_range.mpr (Nat.lt_succ_of_le hyle), ?_⟩
        apply Finset.sum_pos'
        · intro z' _
          split <;> omega
        · refine ⟨z, Finset.mem_range.mpr (Nat.lt_succ_of_le hzle), ?_⟩
          simp [hw, h]




/--
Conjecture: a(n) > 0 for all n > 0.
This is part of a larger conjecture: "(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 3, 7, 11, 12, 15, 19, 24, 27, 31, 34, 35, 43, 46, 47, 56, 70, 71, 72, 87, 88, 115, 136, 137, 147, 167, 168, 178, 207, 235, 236, 267, 286, 297, 423, 537, 747, 762, 1017."
The claim A273917 Conjectures a(n) > 0 and (ii) verified up to 10^11 is also mentioned.
-/
theorem oeis_a273917_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := by
  sorry
