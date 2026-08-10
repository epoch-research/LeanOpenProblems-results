import FormalConjectures.Util.ProblemImports

/--
Number of ordered ways to write $n$ as $w^2 + x^3 + 2y^3 + 3z^3$, where $w, x, y$ and $z$ are nonnegative integers.
$$a(n) = \#\left\{(w, x, y, z) \in \mathbb{N}^4 \mid n = w^2 + x^3 + 2y^3 + 3z^3\right\}$$
-/
def A262824 (n : Nat) : Nat :=
  (Finset.range (n + 1)).sum fun w =>
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then 1 else 0

theorem oeis_262824_conjecture_i_and_ii :
  -- Part (i)
  (
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3) ∧
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3) ∧
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 5 * z ^ 3) ∧
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 6 * z ^ 3)
  ) ∧
  -- Part (ii)
  (
    -- P_1: w^2 + x^3 + 2*y^3 + z^4
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + z ^ 4) ∧
    -- P_2: w^2 + x^3 + 2*y^3 + 3*z^4
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 4) ∧
    -- P_3: w^2 + x^3 + 2*y^3 + 6*z^4
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 6 * z ^ 4) ∧
    -- P_4: 2*w^2 + x^3 + 4*y^3 + z^4
    (∀ n : Nat, ∃ w x y z : Nat, n = 2 * w ^ 2 + x ^ 3 + 4 * y ^ 3 + z ^ 4)
  ) := sorry














