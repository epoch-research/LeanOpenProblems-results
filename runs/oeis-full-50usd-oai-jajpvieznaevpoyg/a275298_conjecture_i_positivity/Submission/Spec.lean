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

/--
Conjecture (i) from OEIS A275298:
(i) $A275298(n) > 0$ for all $n > 0$.
(ii) $A275298(n) = 1$ if and only if $n$ is in the set of exceptional values.
-/

theorem a275298_conjecture_i_positivity (n : ℕ) :
  n > 0 → A275298 n > 0 :=
by sorry

-- Define the set of coefficient triples T
def A275298_conjecture_ii_triples : Finset (ℕ × ℕ × ℕ) :=
  List.toFinset [ (1, 1, 1), (2, 1, 1), (2, 1, 2), (2, 2, 2), (3, 1, 2) ]
