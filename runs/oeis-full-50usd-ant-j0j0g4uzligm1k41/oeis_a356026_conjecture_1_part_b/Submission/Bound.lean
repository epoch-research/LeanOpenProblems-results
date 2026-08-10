import FormalConjectures.Util.ProblemImports
open Nat

def KL_array : ℕ → ℕ → ℕ
| 0, _ => 0
| _, 0 => 0
| i, j =>
  if j ≥ 2 * i - 3 then
    i + j - 1
  else
    let i' := i - 1
    if j % 2 = 0 then
      KL_array i' (i + (j - 2) / 2)
    else
      KL_array i' (i - (j + 3) / 2)
termination_by i j => i

def a (n : ℕ) : ℕ := KL_array n n

-- equation lemma for the recursive (third) branch
theorem KL_eq (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    KL_array i j =
      if j ≥ 2 * i - 3 then i + j - 1
      else if j % 2 = 0 then KL_array (i-1) (i + (j - 2) / 2)
      else KL_array (i-1) (i - (j + 3) / 2) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hi
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hj
  simp only [Nat.zero_add] at *
  rw [KL_array]

-- Sharp structural bound: KL_array i j ≤ 3*i - 2 whenever 1 ≤ j ≤ 2*i - 1.
theorem KL_le : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → j ≤ 2 * i - 1 → KL_array i j ≤ 3 * i - 2 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro j hi hj hji
    rw [KL_eq i j hi hj]
    by_cases hbase : j ≥ 2 * i - 3
    · simp only [hbase, if_true]
      omega
    · simp only [hbase, if_false]
      -- here j < 2*i - 3, so i ≥ 2
      have hi2 : 2 ≤ i := by omega
      by_cases hpar : j % 2 = 0
      · simp only [hpar, if_true]
        have hlt : i - 1 < i := by omega
        apply IH (i-1) hlt (i + (j - 2) / 2)
        · omega
        · omega
        · -- next = i + (j-2)/2 ≤ 2*(i-1) - 1
          omega
      · simp only [hpar, if_false]
        have hlt : i - 1 < i := by omega
        apply IH (i-1) hlt (i - (j + 3) / 2)
        · omega
        · -- 1 ≤ i - (j+3)/2
          omega
        · omega
