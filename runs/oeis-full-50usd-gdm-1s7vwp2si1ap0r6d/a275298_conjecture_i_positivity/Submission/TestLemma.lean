import FormalConjectures.Util.ProblemImports

open Nat Finset Set

-- Copy the A275298 definition and lemma
def A275298 (n : ℕ) : ℕ :=
  let bound := n + 1

  (range bound).sum fun w =>
    (range bound).sum fun x =>
      (range bound).sum fun y =>
        (range bound).sum fun z =>
          let sum_eq_n : Prop := w^3 + x^2 + y^2 + z^2 = n
          let x_minus_w_sq : Prop := x ≥ w ∧ (sqrt (x - w))^2 = x - w
          let ordering : Prop := y ≤ z ∧ w < z

          if sum_eq_n ∧ x_minus_w_sq ∧ ordering then
            1
          else
            0

lemma a275298_pos_of_exists (n : ℕ) (w x y z : ℕ)
  (hw : w < n + 1) (hx : x < n + 1) (hy : y < n + 1) (hz : z < n + 1)
  (h_sum : w^3 + x^2 + y^2 + z^2 = n)
  (h_x_minus_w_sq : x ≥ w ∧ (sqrt (x - w))^2 = x - w)
  (h_ordering : y ≤ z ∧ w < z) :
  A275298 n > 0 := by
  have hw_mem : w ∈ range (n + 1) := mem_range.mpr hw
  have hx_mem : x ∈ range (n + 1) := mem_range.mpr hx
  have hy_mem : y ∈ range (n + 1) := mem_range.mpr hy
  have hz_mem : z ∈ range (n + 1) := mem_range.mpr hz

  have h_term : (if (w^3 + x^2 + y^2 + z^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y ≤ z ∧ w < z) then 1 else 0) = 1 := by
    have h_cond : (w^3 + x^2 + y^2 + z^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y ≤ z ∧ w < z) := ⟨h_sum, h_x_minus_w_sq, h_ordering⟩
    exact if_pos h_cond

  have h_z_sum : 1 ≤ ∑ z' ∈ range (n + 1), if (w^3 + x^2 + y^2 + z'^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y ≤ z' ∧ w < z') then 1 else 0 := by
    have h_le : (if (w^3 + x^2 + y^2 + z^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y ≤ z ∧ w < z) then 1 else 0) ≤ ∑ z' ∈ range (n + 1), if (w^3 + x^2 + y^2 + z'^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y ≤ z' ∧ w < z') then 1 else 0 :=
      single_le_sum_of_canonicallyOrdered (f := fun z' => if (w^3 + x^2 + y^2 + z'^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y ≤ z' ∧ w < z') then 1 else 0) hz_mem
    rw [h_term] at h_le
    exact h_le

  have h_y_sum : 1 ≤ ∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w^3 + x^2 + y'^2 + z'^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0 := by
    have h_le : (∑ z' ∈ range (n + 1), if (w^3 + x^2 + y^2 + z'^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y ≤ z' ∧ w < z') then 1 else 0) ≤
      ∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w^3 + x^2 + y'^2 + z'^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0 :=
      single_le_sum_of_canonicallyOrdered (f := fun y' => ∑ z' ∈ range (n + 1), if (w^3 + x^2 + y'^2 + z'^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0) hy_mem
    exact le_trans h_z_sum h_le

  have h_x_sum : 1 ≤ ∑ x' ∈ range (n + 1), ∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w^3 + x'^2 + y'^2 + z'^2 = n) ∧ (x' ≥ w ∧ (sqrt (x' - w))^2 = x' - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0 := by
    have h_le : (∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w^3 + x^2 + y'^2 + z'^2 = n) ∧ (x ≥ w ∧ (sqrt (x - w))^2 = x - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0) ≤
      ∑ x' ∈ range (n + 1), ∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w^3 + x'^2 + y'^2 + z'^2 = n) ∧ (x' ≥ w ∧ (sqrt (x' - w))^2 = x' - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0 :=
      single_le_sum_of_canonicallyOrdered (f := fun x' => ∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w^3 + x'^2 + y'^2 + z'^2 = n) ∧ (x' ≥ w ∧ (sqrt (x' - w))^2 = x' - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0) hx_mem
    exact le_trans h_y_sum h_le

  have h_w_sum : 1 ≤ ∑ w' ∈ range (n + 1), ∑ x' ∈ range (n + 1), ∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w'^3 + x'^2 + y'^2 + z'^2 = n) ∧ (x' ≥ w' ∧ (sqrt (x' - w'))^2 = x' - w') ∧ (y' ≤ z' ∧ w' < z') then 1 else 0 := by
    have h_le : (∑ x' ∈ range (n + 1), ∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w^3 + x'^2 + y'^2 + z'^2 = n) ∧ (x' ≥ w ∧ (sqrt (x' - w))^2 = x' - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0) ≤
      ∑ w' ∈ range (n + 1), ∑ x' ∈ range (n + 1), ∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w'^3 + x'^2 + y'^2 + z'^2 = n) ∧ (x' ≥ w' ∧ (sqrt (x' - w'))^2 = x' - w') ∧ (y' ≤ z' ∧ w' < z') then 1 else 0 :=
      single_le_sum_of_canonicallyOrdered (f := fun w' => ∑ x' ∈ range (n + 1), ∑ y' ∈ range (n + 1), ∑ z' ∈ range (n + 1), if (w'^3 + x'^2 + y'^2 + z'^2 = n) ∧ (x' ≥ w' ∧ (sqrt (x' - w'))^2 = x' - w') ∧ (y' ≤ z' ∧ w' < z') then 1 else 0) hw_mem
    exact le_trans h_x_sum h_le

  exact h_w_sum

example : A275298 1 > 0 := by
  apply a275298_pos_of_exists 1 0 0 0 1
  · decide
  · decide
  · decide
  · decide
  · rfl
  · decide
  · decide

#eval A275298 2

