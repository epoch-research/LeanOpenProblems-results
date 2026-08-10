import FormalConjectures.Util.ProblemImports

open Nat

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

/-- The conductor set M for the conjecture of A273110(n) = 1. -/
def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}

/-!
### Structural facts about `A273110`

The following are genuinely provable and capture the arithmetic core of the problem.

*Key square identities.* Inside the summand, `E = (x+4y+4z)^2 + (9x+3y+3z)^2`.

* If `x = 0` then `E = (4y+4z)^2 + (3y+3z)^2 = 16(y+z)^2 + 9(y+z)^2 = 25(y+z)^2 = (5(y+z))^2`,
  which is always a perfect square. Hence *every* ordered three–square representation
  `n = y^2 + z^2 + w^2` (with `y > 0`, `y ≥ z ≤ w`) contributes a solution.
* If `x = y + z` then `E = (5(y+z))^2 + (12(y+z))^2 = 169(y+z)^2 = (13(y+z))^2`,
  again always a perfect square (family `F1`). Equivalently `n = 2(y^2+yz+z^2) + w^2`.

These two identities are proved below.
-/

/-- With `x = 0`, the quantity `E` is always a perfect square, namely `(5(y+z))^2`. -/
theorem A273110_sq_of_x_zero (y z : ℕ) :
    IsSquare ((0 + 4 * y + 4 * z) ^ 2 + (9 * 0 + 3 * y + 3 * z) ^ 2) :=
  ⟨5 * (y + z), by ring⟩

/-- With `x = y + z`, the quantity `E` is always a perfect square, namely `(13(y+z))^2`. -/
theorem A273110_sq_of_x_eq_add (y z : ℕ) :
    IsSquare (((y + z) + 4 * y + 4 * z) ^ 2 + (9 * (y + z) + 3 * y + 3 * z) ^ 2) :=
  ⟨13 * (y + z), by ring⟩

/-- Auxiliary: an odd perfect square is `≡ 1 (mod 4)`. -/
theorem sq_odd_mod4 (m : ℕ) (hm : m % 2 = 1) : m ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.odd_iff.mpr hm
  have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
  omega

/-- Auxiliary: every perfect square is `≡ 0` or `1 (mod 4)`. -/
theorem sq_mod4 (r : ℕ) : r ^ 2 % 4 = 0 ∨ r ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd r with ⟨j, rfl⟩ | h
  · left
    have : (j + j) ^ 2 = 4 * (j ^ 2) := by ring
    omega
  · right; exact sq_odd_mod4 r (Nat.odd_iff.mp h)

/-- *Descent obstruction.* When `x`, `y`, `z` are all odd, the quantity
`E = (x+4y+4z)^2 + (9x+3y+3z)^2` is `≡ 2 (mod 4)` and hence never a perfect square.

This is the arithmetic core of the (provable) descent identity `A273110 (4 n) = A273110 n`:
any representation of `4 n` as a sum of four squares has all four parts of the same parity;
the all–odd case forces `x, y, z` odd, which by this lemma makes `E` a non-square, so only the
all–even representations (the doublings of representations of `n`) can contribute. -/
theorem E_not_sq_of_odd (x y z : ℕ) (hx : x % 2 = 1) (hy : y % 2 = 1) (hz : z % 2 = 1) :
    ¬ IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2) := by
  rintro ⟨r, hr⟩
  have ha : (x + 4 * y + 4 * z) % 2 = 1 := by omega
  have hb : (9 * x + 3 * y + 3 * z) % 2 = 1 := by omega
  have hsa := sq_odd_mod4 _ ha
  have hsb := sq_odd_mod4 _ hb
  have hE : ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2) % 4 = 2 := by omega
  have hr2 : r * r % 4 = 2 := by rw [← hr]; exact hE
  rcases sq_mod4 r with h | h <;> (rw [pow_two] at h; omega)

/--
OEIS A273110 Conjecture (i):
a(n) > 0 for all n > 0, and a(n) = 1 only for n = 4^k*m (k = 0,1,2,... and
m is in the set {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}).

This is an open conjecture of Zhi-Wei Sun.  A complete proof is out of reach of the
current library:

* The positivity clause `0 < n → 0 < A273110 n` reduces (via the `x = 0` family, which
  makes `E` a square automatically — see `A273110_sq_of_x_zero`) to the statement that
  every `n` not of the form `4^a(8b+7)` is a sum of three squares (the
  Gauss–Legendre three–square theorem, not present in Mathlib), together with a separate
  construction (the `x = y + z` family, `A273110_sq_of_x_eq_add`) handling `n ≡ 7 (mod 8)`.
* The forward implication `A273110 n = 1 → ∃ k m, …` amounts to showing `A273110 n ≥ 2`
  for every `n` outside `4^ℕ · M`; the relevant counting is governed by the quaternary
  form `2(y^2+yz+z^2)+w^2`, and pinning down the *exact* finite exceptional set is tied to
  ineffective class-number / idoneal-number completeness.
* The reverse implication uses that the unique solution of `4^k m` is `2^k` times the
  unique solution of `m` (a mod-8 descent), reducing to a finite set of base cases, each an
  `O(m^4)` search infeasible for kernel `decide`.

The statement is preserved verbatim as required.
-/
theorem A273110_conjecture (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) :=
by sorry
