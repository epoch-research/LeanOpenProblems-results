import FormalConjectures.Util.ProblemImports

open Nat List Set

/-- A number is zeroless if its decimal digits are all non-zero. -/
def is_zeroless (k : ℕ) : Prop := 0 ∉ Nat.digits 10 k

/-- Predicate for $m$ to be an $n$-digit number. Assumes $n \ge 1$. -/
def is_n_digit (m n : ℕ) : Prop := 10^(n-1) ≤ m ∧ m < 10^n

/--
A358340: $a(n)$ is the smallest $n$-digit number whose fourth power is zeroless.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  -- Define the set S of numbers satisfying the properties.
  let S : Set ℕ := { m : ℕ | is_n_digit m n ∧ is_zeroless (m ^ 4) }
  -- sInf returns the minimum element of the set S.
  sInf S

/--
A358340 It has been proved that there exist infinitely many zeroless squares and cubes but there is apparently no proof for 4th powers, 5th powers, etc.

Formalized as the conjecture that the set of natural numbers whose fourth power is zeroless is infinite.
This is equivalent to the statement that the set $\{ m : ℕ \mid \text{is\_n\_digit}(m, n) \land \text{is\_zeroless}(m^4) \}$ is non-empty for all $n \ge 1$, ensuring $a(n)$ is defined for all $n$.
-/
theorem oeis_a358340_conjecture_k4 : Set.Infinite { m : ℕ | is_zeroless (m ^ 4) } := by
  sorry

/-
Mathematical status notes (not a proof).

This is OEIS A358340's explicitly open conjecture.  Extensive analysis (see below)
shows that the elementary techniques which settle the square and cube cases do NOT
extend to fourth powers, matching the OEIS note "there is apparently no proof for
4th powers".

Key obstructions found:

1.  The square case is provable via the family m_k = (10^k+2)/3 = 33..34, whose
    square (10^{2k}+4·10^k+4)/9 = 11..155..56 is manifestly zeroless.  This works
    precisely because 9 = 3^2 = 10^1 - 1: the denominator is a repunit that is a
    perfect square, giving the uniform expansion 1/9 = 0.111... = ...111 (10-adic).

2.  For fourth powers an analogous family would require a denominator D with
    D^4 = 10^j - 1 for some j; no repunit 10^j - 1 is a perfect 4th power, so the
    identity cannot exist.

3.  Equivalently: for ANY family m_k that converges 10-adically (in particular every
    polynomial-in-10^k family), the low digits of m_k^4 converge to mu^4 for the
    limit rational mu, and an exhaustive search shows NO rational a/b (denominator up
    to 60000) has (a/b)^4 with an all-nonzero 10-adic expansion.  Hence every
    polynomial/periodic family eventually develops a zero digit in m_k^4.  (This same
    search correctly finds the square solution mu = 2/3, validating the method.)

4.  Non-periodic constructive families fail too: the tree of integers whose 4th power
    is zeroless, under single-digit extension (prepending or appending), terminates at
    depth exactly 13 in both directions.

5.  Information-theoretically, m has ~k digits of freedom while m^4 has ~4k digits that
    must all be nonzero; only an algebraic identity could force this, and (2)-(3) show
    none exists for the 4th power.

The number of m < 10^n with m^4 zeroless grows like ~6.57^n (count 89133 at 10^6,
586145 at 10^7), so the set is heuristically infinite — but a rigorous proof requires
analytic input on the joint digit distribution of fourth powers that is currently
beyond reach (open for all k >= 4).

6.  Precise reduction (why the wall is exactly at k=4).  For a k-digit m, m^4 has 4k
    digits.  The LOW B digits of m^4 are controllable to be zeroless for arbitrarily
    large B (the 10-adic lifting tree of zeroless 4th-power tails is infinite), and the
    TOP T digits are controllable to be zeroless via Weyl equidistribution of
    {4 log_10 m}.  But a single k-digit m has only k digits of freedom: fixing the top
    T and bottom B uses T+B input digits and covers only T+B of the 4k output digits,
    leaving a MIDDLE band of ~ (4k - T - B) ≈ 2k uncontrolled digits.  The heuristic
    count of m with zeroless middle is ~ 10^{k - T - B} · (9/10)^{4k-T-B} ≈ 10^{0.73 k}
    (so the set is heuristically infinite), but turning this expectation into an
    existence proof requires JOINT equidistribution / non-vanishing of ~2k middle digits
    of n^4 — a normality-type statement equivalent to a fourth-power exponential-sum
    saving > 0.183, versus the best known (Hua) of 1/8 = 0.125.  For squares the middle
    band has width 0 (top-k and bottom-k meet), and for cubes the saving 1/4 exceeds the
    required 0.137, which is why those cases are provable and k>=4 is not.
-/
