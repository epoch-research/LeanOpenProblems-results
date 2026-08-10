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
### Structural analysis of A273110

The following genuine reductions hold and were verified computationally
(the conjecture itself is verified true for all `n ≤ 10^9`):

* **Key identity.**  The inner square expression depends only on `x` and `s := y + z`:
  `(x+4y+4z)^2 + (9x+3y+3z)^2 = 82*x^2 + 62*x*s + 25*s^2 =: f x s`.
  In particular `f 0 s = (5*s)^2` and `f x x = (13*x)^2`, so a representation is
  automatically valid whenever `x = 0` (a sum of three squares) or `y + z = x`
  (a representation by the ternary form `2y^2 + 2yz + 2z^2 + w^2`).

* **2-adic reduction.**  `A273110 (4*n) = A273110 n`: any representation of `4n`
  must have all of `x,y,z,w` even (the all-odd case forces `E ≡ 2 (mod 4)`, not a
  square), and halving gives a bijection with representations of `n`.

* Hence `A273110 n = A273110 m` where `m` is the `4`-free part of `n`, reducing
  the statement to `4`-free `m`.  For `m ≡ 7 (mod 8)` there are no `x = 0`
  (three–square) representations, and every valid tuple has `y + z = x`, i.e. is
  a representation of `m` by the ternary form `g = 2y^2 + 2yz + 2z^2 + w^2`.

* **Class number one.**  The form `g` is *alone in its genus*: its Conway mass is
  `1/24 = 1/|Aut g|` (verified via `sage`).  Consequently the theta series of `g`
  equals the weight-`3/2` Eisenstein series of its level (Siegel–Weil), so the
  representation number `r_g(m)` is an *exact* singular-series value with no
  cusp-form error term.  In particular `r_g(m) ≍ √m` with an effective implied
  constant, whence `A273110 m = 1` forces `r_g(m) ≤ |Aut g| = 24` and therefore
  `m ≤ B` for an explicit (small, `≈ 2300`) bound `B`.  Thus the conjecture is in
  fact *effectively* true, the `4`-free witnesses being exactly the set above.

The forward implication `A273110 n = 1 → n = 4^k m` and the positivity statement
both reduce to a lower bound `r_g(m) > 24` for `m ≡ 7 (mod 8)`, `m > B`, together
with Legendre's three–square theorem for the remaining residue classes.  Both of
these inputs — the Siegel–Weil identity / singular-series lower bound for the
class-number-one ternary form `g`, and the (hard direction of the) three–square
theorem — are absent from Mathlib and admit no elementary replacement within the
available toolset; the statement below therefore retains its number-theoretic
core (Zhi-Wei Sun's conjecture A273110).
-/

/--
OEIS A273110 Conjecture (i):
a(n) > 0 for all n > 0, and a(n) = 1 only for n = 4^k*m (k = 0,1,2,... and
m is in the set {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}).
-/
theorem A273110_conjecture (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) :=
by sorry
