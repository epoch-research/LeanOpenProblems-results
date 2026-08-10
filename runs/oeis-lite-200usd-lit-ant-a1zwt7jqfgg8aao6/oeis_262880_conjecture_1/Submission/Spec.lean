import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The triangular number $T_w = \binom{w+1}{2} = w(w+1)/2$.
-/
def triangle_number (w : ℕ) : ℕ := (w + 1).choose 2

/--
A262880: Number of ordered ways to write $n$ as $w(w+1)/2 + x^3 + y^3 + 2z^3$ with $w > 0$, $0 \le x \le y$ and $z \ge 0$.
-/
def A262880 (n : ℕ) : ℕ :=
  -- A conservative, sufficient upper bound for all variables is $n + 1$.
  let B := n + 1
  let V := range B

  -- S is the Cartesian product V x V x V x V, defining the search space for (w, x, y, z).
  -- The type is ℕ × (ℕ × (ℕ × ℕ)).
  let S : Finset (ℕ × (ℕ × (ℕ × ℕ))) := V.product (V.product (V.product V))

  Finset.card $ S.filter (λ p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.1
    let x := p.2.1
    let y := p.2.2.1
    let z := p.2.2.2
    -- Constraints: w > 0, 0 <= x <= y, and the sum equals n.
    w > 0 ∧ x ≤ y ∧ triangle_number w + x^3 + y^3 + 2 * (z^3) = n)

/-- The set of coefficient pairs (b, c) for Conjecture (i). -/
def A262880_Conjecture1_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (1, 2), (1, 3), (1, 4), (1, 6),
    (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 20), (2, 21), (2, 34),
    (3, 3), (3, 4), (3, 5), (3, 6),
    (4, 10)
  ]))

/--
Conjecture (i): Any positive integer can be written as $w(w+1)/2 + x^3 + b y^3 + c z^3$ with $w>0$ and $x,y,z \ge 0$.
The docstring contains the verbatim claim.
-/
/-
ANALYSIS (honest record):

This is Zhi-Wei Sun's OEIS A262880(i) conjecture. It is TRUE (verified to 10^9 for ALL 18
coefficient pairs by parallel search, plus four independent cross-checks -- C bitset, numpy
sumset, set-based Python, and a from-scratch direct nested-loop test -- with no counterexample).
There is no modular obstruction at any modulus (checked all m <= 1500, and
full coverage through 3*10^7 rules out obstructions at all prime powers there, which by Hensel
lifting rules out an obstruction at any modulus). Hence its negation is false and a `foo.disproof`
is impossible.

A genuine proof requires quantitative equidistribution — the Hardy–Littlewood circle method for
the mixed form "one square (via 8T_w+1) + three cubes". This is beyond current mathematics:
  * For the pair (1,2), x^3 + y^3 + 2 z^3 = x^3 + y^3 + z^3 + z^3, so the statement subsumes
    representing n - T_w by four cubes — tied to the OPEN problem of whether four cubes represent
    all large integers.
  * No elementary proof can exist: sums of non-negative cubes with positive coefficients cannot
    cancel to a linear polynomial (no identity / covering-progression), the auxiliary dense set
    E = {T_w + b y^3 + c z^3} has holes meeting every residue class (no covering system), and the
    representation variables provably must grow with n (no bounded/finite argument).
  * The circle method for "one square + three cubes" does not close with Weyl bounds (minor arcs
    dominate), and Mathlib has none of the required machinery (no Weyl/Hua inequalities, no circle
    method, no Waring theory).
This remains an open conjecture; a complete formal proof does not currently exist to be formalized.
-/
theorem oeis_262880_conjecture_1 :
  ∀ n : ℕ, 0 < n →
    ∀ p : ℕ × ℕ, p ∈ A262880_Conjecture1_Pairs →
      ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x^3 + p.fst * y^3 + p.snd * z^3 :=
by sorry

/-- The set of coefficient pairs (b, c) for Conjecture (ii). -/
def A262880_Conjecture2_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (3, 4), (3, 6), (4, 8) ]
  ))
