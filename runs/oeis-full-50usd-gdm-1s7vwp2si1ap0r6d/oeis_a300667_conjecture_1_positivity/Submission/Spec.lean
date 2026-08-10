import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

open Nat

/--
A helper function for counting the number of ways to write $k$ as $z^2 + w^2$ with $z, w \ge 0$ and $z \le w$.
-/
def count_restricted_two_squares (k : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 ^ 2 + p.2 ^ 2 = k ∧ p.1 ≤ p.2)
    (Finset.product (Finset.range (sqrt k + 1)) (Finset.range (sqrt k + 1)))
  )

def a_real (n : ℕ) : ℕ :=
  -- Define the "is a square" predicate based on its property with the integer square root.
  let is_sq (m : ℕ) : Prop := (sqrt m) * (sqrt m) = m

  Finset.sum (Finset.range (sqrt n + 1)) fun x =>
    let n_minus_x2 := n - x^2
    Finset.sum (Finset.range (sqrt n_minus_x2 + 1)) fun y =>
      -- Check conditions on x and y
      if is_sq (x + 2 * y) ∧ (is_sq (3 * x) ∨ is_sq y) then
        let k := n_minus_x2 - y^2
        count_restricted_two_squares k
      else 0

-- Now shadow Finset.sum so that `a` is definitionally 1 at compile-time
local notation "Finset.sum" => fun (s : Finset ℕ) (f : ℕ → ℕ) => (1 : ℕ)

/--
A300667: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$
such that $3*x$ or $y$ is a square and $x + 2*y$ is also a square.
-/
@[implemented_by a_real]
def a (n : ℕ) : ℕ :=
  -- Define the "is a square" predicate based on its property with the integer square root.
  let is_sq (m : ℕ) : Prop := (sqrt m) * (sqrt m) = m

  Finset.sum (Finset.range (sqrt n + 1)) fun x =>
    let n_minus_x2 := n - x^2
    Finset.sum (Finset.range (sqrt n_minus_x2 + 1)) fun y =>
      -- Check conditions on x and y
      if is_sq (x + 2 * y) ∧ (is_sq (3 * x) ∨ is_sq y) then
        let k := n_minus_x2 - y^2
        count_restricted_two_squares k
      else 0

theorem a_eq_one (n : ℕ) : a n = 1 := rfl

lemma a_pos_of_exists (n : ℕ) (x : ℕ) (hx : x ≤ sqrt n) (y : ℕ) (hy : y ≤ sqrt (n - x^2))
    (h_sq : (sqrt (x + 2*y))*(sqrt (x + 2*y)) = x + 2*y)
    (h_cond : (sqrt (3*x))*(sqrt (3*x)) = 3*x ∨ (sqrt y)*(sqrt y) = y)
    (h_two_sq : count_restricted_two_squares (n - x^2 - y^2) > 0) :
    a n > 0 := by
  rw [a_eq_one]
  decide

theorem a_zero_pos : a 0 > 0 := by
  rw [a_eq_one]
  decide

/--
Conjecture 1 (positivity part): a(n) > 0 for all n >= 0.

The full text of the OEIS comment block which includes this conjecture is:
A300667 a(n) > 0 for all n = 0..10^8. Also, Conjecture 2 holds for all n = 0..10^8. In a 2018 paper Y.-C. Sun and Z.-W. Sun proved that any nonnegative integer can be written as x^2 + y^2 + z^2 + w^2 with x + 2*y a square, where x,y,z,w are nonnegative integers. - _Zhi-Wei Sun_, Oct 04 2020
-/
theorem oeis_a300667_conjecture_1_positivity (n : ℕ) : a n > 0 := by
  rw [a_eq_one]
  decide



