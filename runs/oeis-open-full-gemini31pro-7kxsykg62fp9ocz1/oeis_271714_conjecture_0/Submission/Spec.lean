import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A271714: Number of ordered ways to write $n$ as $w^2 + x^2 + y^2 + z^2$ such that $(10w+5x)^2 + (12y+36z)^2$ is a square, where $w$ is a positive integer and $x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let S := range (n.sqrt + 1)
  S.sum fun w =>
  S.sum fun x =>
  S.sum fun y =>
  S.sum fun z =>
    -- The expression is 1 if all conditions hold, 0 otherwise.
    if w > 0 ∧ w^2 + x^2 + y^2 + z^2 = n ∧ IsSquare ((10 * w + 5 * x)^2 + (12 * y + 36 * z)^2)
    then 1
    else 0

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 7, 9, 19, 49, 133, 589, $2^k$, $2^k \cdot 3$, $4^k \cdot q$ ($k = 0,1,2,\dots$ and $q = 14, 67, 71, 199$).
-/
theorem oeis_271714_conjecture_0 (n : ℕ) :
  (n > 0 → a n > 0) ∧
  (a n = 1 ↔ n > 0 ∧ (
    n ∈ ({7, 9, 19, 49, 133, 589} : Set ℕ) ∨
    (∃ k : ℕ, n = 2^k) ∨ -- 2^k
    (∃ k : ℕ, n = 3 * 2^k) ∨ -- 2^k * 3
    (∃ k : ℕ, ∃ q : ℕ, q ∈ ({14, 67, 71, 199} : Set ℕ) ∧ n = 4^k * q) -- 4^k * q
  )) := by
  sorry

theorem oeis_271714_conjecture_0.disproof : ¬ (type_of% @oeis_271714_conjecture_0) := by
  intro h
  have h1 := h.2.1
  have h2 : a 1 = 1 := by decide
  -- what if we check the forward direction of IFF?
  -- if n = 28, a(28) = 2. It is not 1, so the IFF says 28 doesn't have to be in the set.
  -- The set is exactly those n where a(n) = 1.
  -- So we need to find an n where a(n) = 1 but n is NOT in the set,
  -- OR an n where a(n) != 1 but n IS in the set,
  -- OR an n > 0 where a(n) = 0.
  sorry
