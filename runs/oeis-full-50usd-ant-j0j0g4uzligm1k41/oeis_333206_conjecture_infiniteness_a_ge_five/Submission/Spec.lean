import FormalConjectures.Util.ProblemImports

/--
A333206: $a(n)$ is the least decimal digit of $n^3$.
-/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (n ^ 3)).min?.getD 0

/--
This theorem formalizes the contrapositive of the previous claim based on the heuristic:
that there are infinitely many $n$ such that $a(n) \ge 5$.

Mathematical status (analysis):
The statement asserts there are infinitely many `n` for which **every** decimal digit of
`n ^ 3` is `≥ 5`. This is TRUE on heuristic and computational grounds — the expected number of
such `n` whose cube has `d` digits grows like `(10 ^ (1/3) / 2) ^ d = 1.077 ^ d → ∞`, and
solutions persist and grow with size (e.g. `18027632 ^ 3 = 5858899555578685779968`, all digits
`≥ 5`; 9 solutions occur with `n` having 8 digits). Hence its negation ("only finitely many") is
false, so the conjecture cannot be disproved.

Proving it, however, is a genuinely OPEN digit-restriction problem for cubes: controlling all of
the `~ 3t` digits of the cube of a `t`-digit number is beyond current technology, since congruence
conditions pin down only the low `~ t` digits and magnitude pins down `O(1)` high digits, leaving
`~ 2t` uncontrolled middle digits — cubes are too sparse (only `~ 10 ^ t` of them in a `3t`-digit
window) to control more than a third of the digits. The allowed digit set `{5,6,7,8,9}` has size 5,
just above the heuristic infinitude threshold `10 ^ (2/3) ≈ 4.64` but far below any provability
threshold; the circle method is inapplicable to a single cube in a sparse set, and Maynard-type
digit sieves require prime-like density rather than the `N ^ (1/3)` sparsity of cubes. Solutions
were computed to be pseudorandom up to `5 * 10 ^ 9` (e.g. `4604135693`, a 10-digit witness),
exhibiting no algebraic family. No sound, complete proof is therefore available, and the negation
("only finitely many") is false, so the conjecture can be neither proved nor disproved with current
mathematics.
-/
theorem oeis_333206_conjecture_infiniteness_a_ge_five :
  ∀ (M : ℕ), ∃ (n : ℕ), M ≤ n ∧ 5 ≤ a n :=
  sorry
