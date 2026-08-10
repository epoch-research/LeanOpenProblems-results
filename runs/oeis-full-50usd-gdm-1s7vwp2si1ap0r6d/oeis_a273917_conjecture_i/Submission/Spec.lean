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

/--
Conjecture: a(n) > 0 for all n > 0.
This is part of a larger conjecture: "(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 3, 7, 11, 12, 15, 19, 24, 27, 31, 34, 35, 43, 46, 47, 56, 70, 71, 72, 87, 88, 115, 136, 137, 147, 167, 168, 178, 207, 235, 236, 267, 286, 297, 423, 537, 747, 762, 1017."
The claim A273917 Conjectures a(n) > 0 and (ii) verified up to 10^11 is also mentioned.
-/
theorem a_pos_of_exists_sol {n : ℕ} 
    (h : ∃ (w : ℕ) (x : ℕ) (y : ℕ) (z : ℕ), w > 0 ∧ w^2 + 3 * x^2 + y^4 + z^5 = n) : 
    a n > 0 := by
  rcases h with ⟨w, x, y, z, hw, heq⟩
  have hw_le_w2 : w ≤ w^2 := by
    rcases w with _|w
    · contradiction
    · simp [sq]
  have hw_le_n : w ≤ n := by
    omega
  have hw_mem : w ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    omega
  
  have hx_le_n : x ≤ n := by
    by_cases hx : x = 0
    · rw [hx]
      omega
    · have : 1 ≤ x := by omega
      have hx_le_3x2 : x ≤ 3 * x^2 := by
        simp [sq]
        nlinarith
      omega
  have hx_mem : x ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    omega

  have hy_le_n : y ≤ n := by
    by_cases hy : y = 0
    · rw [hy]
      omega
    · have hy_pos : 1 ≤ y := by omega
      have hy_le_y4 : y ≤ y^4 := le_self_pow hy_pos (by decide)
      omega
  have hy_mem : y ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    omega

  have hz_le_n : z ≤ n := by
    by_cases hz : z = 0
    · rw [hz]
      omega
    · have hz_pos : 1 ≤ z := by omega
      have hz_le_z5 : z ≤ z^5 := le_self_pow hz_pos (by decide)
      omega
  have hz_mem : z ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    omega

  -- Now we can use Finset.single_le_sum
  unfold a
  have h1 : 1 ≤ ∑ z ∈ Finset.range (n + 1), if w > 0 ∧ w^2 + 3 * x^2 + y^4 + z^5 = n then 1 else 0 := by
    have h_le := Finset.single_le_sum (f := fun z_1 => if w > 0 ∧ w^2 + 3 * x^2 + y^4 + z_1^5 = n then 1 else 0) (fun a _ => by dsimp; split_ifs <;> omega) hz_mem
    dsimp at h_le
    have h_term : (if w > 0 ∧ w^2 + 3 * x^2 + y^4 + z^5 = n then 1 else 0) = 1 := by
      split_ifs with h_if
      · rfl
      · exfalso
        exact h_if ⟨hw, heq⟩
    rw [h_term] at h_le
    exact h_le

  have h2 : 1 ≤ ∑ y_1 ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1), if w > 0 ∧ w^2 + 3 * x^2 + y_1^4 + z^5 = n then 1 else 0 := by
    have h_le := Finset.single_le_sum (f := fun y_1 => ∑ z ∈ Finset.range (n + 1), if w > 0 ∧ w^2 + 3 * x^2 + y_1^4 + z^5 = n then 1 else 0) (fun a _ => Finset.sum_nonneg (fun a _ => by split_ifs <;> omega)) hy_mem
    exact h1.trans h_le

  have h3 : 1 ≤ ∑ x_1 ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1), if w > 0 ∧ w^2 + 3 * x_1^2 + y^4 + z^5 = n then 1 else 0 := by
    have h_le := Finset.single_le_sum (f := fun x_1 => ∑ y ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1), if w > 0 ∧ w^2 + 3 * x_1^2 + y^4 + z^5 = n then 1 else 0) (fun a _ => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun a _ => by split_ifs <;> omega))) hx_mem
    exact h2.trans h_le

  have h4 : 1 ≤ ∑ w_1 ∈ Finset.range (n + 1), ∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1), if w_1 > 0 ∧ w_1^2 + 3 * x^2 + y^4 + z^5 = n then 1 else 0 := by
    have h_le := Finset.single_le_sum (f := fun w_1 => ∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1), if w_1 > 0 ∧ w_1^2 + 3 * x^2 + y^4 + z^5 = n then 1 else 0) (fun a _ => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun a _ => by split_ifs <;> omega)))) hw_mem
    exact h3.trans h_le

  omega

theorem oeis_a273917_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := sorry


