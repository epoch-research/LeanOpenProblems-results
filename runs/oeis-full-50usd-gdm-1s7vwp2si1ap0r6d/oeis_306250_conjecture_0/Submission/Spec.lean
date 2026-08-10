import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A306250: Number of ways to write $n$ as $x(3x+1) + y(3y-1) + z(3z+2) + w(3w-2)$,
where $x,y,z,w$ are nonnegative integers with $x \cdot y \cdot z = 0$.
-/
def A306250 (n : ℕ) : ℕ :=
  let T₁ (x : ℕ) : ℕ := x * (3 * x + 1)
  let T₂ (y : ℕ) : ℕ := y * (3 * y - 1)
  let T₃ (z : ℕ) : ℕ := z * (3 * z + 2)
  let T₄ (w : ℕ) : ℕ := w * (3 * w - 2)

  -- The search space for each variable is bounded by $n$.
  -- A more precise bound can be derived, but `n+1` is a safe upper limit for the range.
  -- For non-negative $x,y,z,w$, $T_i(v) \ge v$. If $T_i(v) \le n$, then $v \le n$.
  let R := range (n + 1)

  -- We compute the number of tuples $(x, y, z, w)$ satisfying the conditions using a sum of indicator functions.
  R.sum fun x =>
    R.sum fun y =>
      R.sum fun z =>
        R.sum fun w =>
          if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + T₄ w = n then
            1
          else
            0

open Nat Finset

def T₁ (x : ℕ) : ℕ := x * (3 * x + 1)
def T₂ (y : ℕ) : ℕ := y * (3 * y - 1)
def T₃ (z : ℕ) : ℕ := z * (3 * z + 2)
def T₄ (w : ℕ) : ℕ := w * (3 * w - 2)

theorem A306250_pos_of_exists (n : ℕ) (x y z w : ℕ)
    (hx : x ∈ range (n + 1)) (hy : y ∈ range (n + 1)) (hz : z ∈ range (n + 1)) (hw : w ∈ range (n + 1))
    (h_cond : (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + T₄ w = n) :
    A306250 n > 0 := by
  dsimp [A306250]
  have h1 : (if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + T₄ w = n then 1 else 0) ≤
    (range (n + 1)).sum (fun w_1 => if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + w_1 * (3 * w_1 - 2) = n then 1 else 0) := by
    have h_le := single_le_sum (f := fun w_1 => if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + w_1 * (3 * w_1 - 2) = n then 1 else 0) (hf := fun _ _ => Nat.zero_le _) hw
    exact h_le

  have h2 : (range (n + 1)).sum (fun w_1 => if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + w_1 * (3 * w_1 - 2) = n then 1 else 0) ≤
    (range (n + 1)).sum (fun z_1 => (range (n + 1)).sum (fun w_1 => if (x = 0 ∨ y = 0 ∨ z_1 = 0) ∧ T₁ x + T₂ y + z_1 * (3 * z_1 + 2) + w_1 * (3 * w_1 - 2) = n then 1 else 0)) := by
    have h_le := single_le_sum (f := fun z_1 => (range (n + 1)).sum (fun w_1 => if (x = 0 ∨ y = 0 ∨ z_1 = 0) ∧ T₁ x + T₂ y + z_1 * (3 * z_1 + 2) + w_1 * (3 * w_1 - 2) = n then 1 else 0)) (hf := fun _ _ => Nat.zero_le _) hz
    exact h_le

  have h3 : (range (n + 1)).sum (fun z_1 => (range (n + 1)).sum (fun w_1 => if (x = 0 ∨ y = 0 ∨ z_1 = 0) ∧ T₁ x + T₂ y + z_1 * (3 * z_1 + 2) + w_1 * (3 * w_1 - 2) = n then 1 else 0)) ≤
    (range (n + 1)).sum (fun y_1 => (range (n + 1)).sum (fun z_1 => (range (n + 1)).sum (fun w_1 => if (x = 0 ∨ y_1 = 0 ∨ z_1 = 0) ∧ T₁ x + y_1 * (3 * y_1 - 1) + z_1 * (3 * z_1 + 2) + w_1 * (3 * w_1 - 2) = n then 1 else 0))) := by
    have h_le := single_le_sum (f := fun y_1 => (range (n + 1)).sum (fun z_1 => (range (n + 1)).sum (fun w_1 => if (x = 0 ∨ y_1 = 0 ∨ z_1 = 0) ∧ T₁ x + y_1 * (3 * y_1 - 1) + z_1 * (3 * z_1 + 2) + w_1 * (3 * w_1 - 2) = n then 1 else 0))) (hf := fun _ _ => Nat.zero_le _) hy
    exact h_le

  have h4 : (range (n + 1)).sum (fun y_1 => (range (n + 1)).sum (fun z_1 => (range (n + 1)).sum (fun w_1 => if (x = 0 ∨ y_1 = 0 ∨ z_1 = 0) ∧ T₁ x + y_1 * (3 * y_1 - 1) + z_1 * (3 * z_1 + 2) + w_1 * (3 * w_1 - 2) = n then 1 else 0))) ≤ A306250 n := by
    have h_le := single_le_sum (f := fun x_1 => (range (n + 1)).sum (fun y_1 => (range (n + 1)).sum (fun z_1 => (range (n + 1)).sum (fun w_1 => if (x_1 = 0 ∨ y_1 = 0 ∨ z_1 = 0) ∧ x_1 * (3 * x_1 + 1) + y_1 * (3 * y_1 - 1) + z_1 * (3 * z_1 + 2) + w_1 * (3 * w_1 - 2) = n then 1 else 0)))) (hf := fun _ _ => Nat.zero_le _) hx
    exact h_le

  have h_total : (if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + T₄ w = n then 1 else 0) ≤ A306250 n :=
    h1.trans (h2.trans (h3.trans h4))

  have h_cond_true : (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + T₄ w = n := h_cond
  have h_if : (if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + T₄ w = n then 1 else 0) = 1 := if_pos h_cond_true

  have h_gt : A306250 n ≥ 1 := by
    rw [← h_if]
    exact h_total

  exact h_gt

/--
Conjecture: a(n) > 0 for any nonnegative integer n.
-/
theorem oeis_306250_conjecture_0 (n : ℕ) : A306250 n > 0 := answer(sorry)

