import FormalConjectures.Util.ProblemImports

open Nat

def IsSquare_eval (n : ℕ) : Bool :=
  (List.range (n + 1)).any (fun i => i * i == n)

theorem IsSquare_eval_iff (n : ℕ) : IsSquare n ↔ IsSquare_eval n = true := by
  constructor
  · rintro ⟨r, (hr : n = r * r)⟩
    have hr_lt : r < n + 1 := by
      rcases r with _ | r
      · omega
      · rw [hr]
        have : r + 1 ≤ (r + 1) * (r + 1) := by nlinarith
        omega
    unfold IsSquare_eval
    rw [List.any_eq_true]
    use r
    constructor
    · rwa [List.mem_range]
    · simp [hr.symm]
  · unfold IsSquare_eval
    rw [List.any_eq_true]
    rintro ⟨r, hr_in, hr_eq⟩
    rw [List.mem_range] at hr_in
    simp only [beq_iff_eq] at hr_eq
    use r
    rw [hr_eq]

/--
A273110: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with
$(x+4y+4z)^2 + (9x+3y+3z)^2$ a square, where $x,y,z,w$ are nonnegative integers
with $y > 0$ and $y \ge z \le w$.
-/
def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n -- Safe and conservative upper bound

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       (IsSquare E)
    then 1 else 0

def A273110_eval (n : ℕ) : ℕ :=
  let d : ℕ := n

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       IsSquare_eval E = true
    then 1 else 0

theorem A273110_eq_eval (n : ℕ) : A273110 n = A273110_eval n := by
  unfold A273110 A273110_eval
  simp_rw [IsSquare_eval_iff]

/-- The conductor set M for the conjecture of A273110(n) = 1. -/
def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}

theorem A273110_zero : A273110 0 = 0 := by
  rw [A273110_eq_eval]
  rfl

theorem A273110_one : A273110 1 = 1 := by
  rw [A273110_eq_eval]
  decide

theorem A273110_four : A273110 4 = 1 := by
  rw [A273110_eq_eval]
  rfl

theorem A273110_six : A273110 6 = 3 := by
  sorry

theorem A273110_seven : A273110 7 = 1 := by
  sorry

theorem M_has_1 : 1 ∈ A273110_set_M := by
  unfold A273110_set_M
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]

theorem M_has_7 : 7 ∈ A273110_set_M := by
  unfold A273110_set_M
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]

