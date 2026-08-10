import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
A275298: Number of ordered ways to write $n$ as $w^3 + x^2 + y^2 + z^2$ with $x - w$ a square,
where $x,y,z,w$ are nonnegative integers with $y \le z > w$.
-/
def A275298 (n : ℕ) : ℕ :=
  let bound := n + 1

  (range bound).sum fun w =>
    (range bound).sum fun x =>
      (range bound).sum fun y =>
        (range bound).sum fun z =>
          let sum_eq_n : Prop := w^3 + x^2 + y^2 + z^2 = n

          -- $x - w$ is a square. This requires $x \ge w$.
          -- We check $x \ge w$ explicitly, and then check if the natural number difference
          -- is a perfect square using Nat.sqrt.
          let x_minus_w_sq : Prop := x ≥ w ∧ (sqrt (x - w))^2 = x - w
          let ordering : Prop := y ≤ z ∧ w < z

          if sum_eq_n ∧ x_minus_w_sq ∧ ordering then
            1
          else
            0

-- The set of $n$ for which $A275298(n) = 1$.
def A275298_exceptional_one_values_list : List ℕ :=
  [1, 3, 4, 7, 8, 12, 16, 23, 24, 40, 47, 71, 167, 311, 599]

/-
Conjecture (i) from OEIS A275298:
(i) $A275298(n) > 0$ for all $n > 0$.
(ii) $A275298(n) = 1$ if and only if $n$ is in the set of exceptional values.
-/
/-- Reduction lemma: if there is a witness quadruple `(w, x, y, z)` lying in the
search range `range (n+1)` and satisfying all the defining conditions of `A275298`,
then `A275298 n > 0`. -/
theorem a275298_pos_of_witness (n : ℕ)
    (w x y z : ℕ) (hw : w < n + 1) (hx : x < n + 1) (hy : y < n + 1) (hz : z < n + 1)
    (hcond : (w ^ 3 + x ^ 2 + y ^ 2 + z ^ 2 = n) ∧
      (x ≥ w ∧ (sqrt (x - w)) ^ 2 = x - w) ∧ (y ≤ z ∧ w < z)) :
    A275298 n > 0 := by
  have key : (1 : ℕ) ≤ A275298 n := by
    unfold A275298
    calc (1 : ℕ)
        = (if (w ^ 3 + x ^ 2 + y ^ 2 + z ^ 2 = n) ∧
            (x ≥ w ∧ (sqrt (x - w)) ^ 2 = x - w) ∧ (y ≤ z ∧ w < z) then 1 else 0) := by
              rw [if_pos hcond]
      _ ≤ (range (n + 1)).sum fun z' =>
            if (w ^ 3 + x ^ 2 + y ^ 2 + z' ^ 2 = n) ∧
              (x ≥ w ∧ (sqrt (x - w)) ^ 2 = x - w) ∧ (y ≤ z' ∧ w < z') then 1 else 0 := by
            exact Finset.single_le_sum
              (f := fun z' => if (w ^ 3 + x ^ 2 + y ^ 2 + z' ^ 2 = n) ∧
                (x ≥ w ∧ (sqrt (x - w)) ^ 2 = x - w) ∧ (y ≤ z' ∧ w < z') then 1 else 0)
              (fun i _ => Nat.zero_le _) (mem_range.mpr hz)
      _ ≤ (range (n + 1)).sum fun y' => (range (n + 1)).sum fun z' =>
            if (w ^ 3 + x ^ 2 + y' ^ 2 + z' ^ 2 = n) ∧
              (x ≥ w ∧ (sqrt (x - w)) ^ 2 = x - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0 := by
            exact Finset.single_le_sum
              (f := fun y' => (range (n + 1)).sum fun z' =>
                if (w ^ 3 + x ^ 2 + y' ^ 2 + z' ^ 2 = n) ∧
                  (x ≥ w ∧ (sqrt (x - w)) ^ 2 = x - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0)
              (fun i _ => Nat.zero_le _) (mem_range.mpr hy)
      _ ≤ (range (n + 1)).sum fun x' => (range (n + 1)).sum fun y' => (range (n + 1)).sum fun z' =>
            if (w ^ 3 + x' ^ 2 + y' ^ 2 + z' ^ 2 = n) ∧
              (x' ≥ w ∧ (sqrt (x' - w)) ^ 2 = x' - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0 := by
            exact Finset.single_le_sum
              (f := fun x' => (range (n + 1)).sum fun y' => (range (n + 1)).sum fun z' =>
                if (w ^ 3 + x' ^ 2 + y' ^ 2 + z' ^ 2 = n) ∧
                  (x' ≥ w ∧ (sqrt (x' - w)) ^ 2 = x' - w) ∧ (y' ≤ z' ∧ w < z') then 1 else 0)
              (fun i _ => Nat.zero_le _) (mem_range.mpr hx)
      _ ≤ _ := by
            exact Finset.single_le_sum
              (f := fun w' => (range (n + 1)).sum fun x' => (range (n + 1)).sum fun y' =>
                (range (n + 1)).sum fun z' =>
                if (w' ^ 3 + x' ^ 2 + y' ^ 2 + z' ^ 2 = n) ∧
                  (x' ≥ w' ∧ (sqrt (x' - w')) ^ 2 = x' - w') ∧ (y' ≤ z' ∧ w' < z') then 1 else 0)
              (fun i _ => Nat.zero_le _) (mem_range.mpr hw)
  omega

/-- The arithmetic core (Zhi-Wei Sun's conjecture A275298(i)): every positive `n`
admits a representation `n = w³ + x² + y² + z²` with `x - w` a perfect square and
`y ≤ z`, `w < z`. -/
theorem a275298_exists_witness (n : ℕ) (hn : n > 0) :
    ∃ w x y z : ℕ, w < n + 1 ∧ x < n + 1 ∧ y < n + 1 ∧ z < n + 1 ∧
      (w ^ 3 + x ^ 2 + y ^ 2 + z ^ 2 = n) ∧
      (x ≥ w ∧ (sqrt (x - w)) ^ 2 = x - w) ∧ (y ≤ z ∧ w < z) := by
  sorry

theorem a275298_conjecture_i_positivity (n : ℕ) :
  n > 0 → A275298 n > 0 := by
  intro hn
  obtain ⟨w, x, y, z, hw, hx, hy, hz, hcond⟩ := a275298_exists_witness n hn
  exact a275298_pos_of_witness n w x y z hw hx hy hz hcond

-- Define the set of coefficient triples T
def A275298_conjecture_ii_triples : Finset (ℕ × ℕ × ℕ) :=
  List.toFinset [ (1, 1, 1), (2, 1, 1), (2, 1, 2), (2, 2, 2), (3, 1, 2) ]
