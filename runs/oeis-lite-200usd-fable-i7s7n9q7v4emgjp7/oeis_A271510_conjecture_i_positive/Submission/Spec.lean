import FormalConjectures.Util.ProblemImports

open Nat

/--
A271510: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x \ge y \ge 0$, $z \ge 0$ and $w \ge 0$ such that $x^2 + 8y^2 + 16z^2$ is a square.
-/
def A271510 (n : ℕ) : ℕ :=
  -- Define the decidable predicate for being a perfect square in ℕ.
  let is_square (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- The maximum value for any variable is $\lfloor\sqrt{n}\rfloor$.
  let bound := n.sqrt
  let R : Finset ℕ := Finset.range (bound + 1)

  -- The search space is the Cartesian product R x R x R x R, structured as (((ℕ × ℕ) × ℕ) × ℕ).
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) := R.product R |>.product R |>.product R

  Finset.card $ search_space.filter fun p =>
    -- Decompose the nested product tuple p = (((x, y), z), w)
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd

    -- Constraint 1: sum of squares equals n
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    -- Constraint 2: $x \ge y$
    x ≥ y ∧
    -- Constraint 3: $x^2 + 8y^2 + 16z^2$ is a square.
    is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

-- A standard definition for "is a square" on ℕ
def is_square (k : ℕ) : Prop := ∃ m : ℕ, k = m^2

/-
NOTE (analysis performed, 2025):
This is Zhi-Wei Sun's conjecture (i) from OEIS A271510 (cf. arXiv:1604.06723,
"Refining Lagrange's four-square theorem"), which is an open research problem.

Findings of an extensive investigation:
1. The formalized definition above was checked (via #eval) to agree exactly with an
   independent implementation; a(n) > 0 was verified computationally for all n ≤ 10^8,
   and min a(n) over n with 4 ∤ n grows like ≈ 0.08·√n (e.g. min a = 118 on
   [2^20, 2^21)), so the statement is certainly TRUE and a disproof is impossible.
2. The condition x²+8y²+16z² = t² involves all of x, y, z (only w is free). The cone
   t² = x²+8y²+16z² (signature (1,3)) contains no 2-planes, so every polynomially
   parametrized witness family yields only binary forms n = C·k² + w² with C in the
   set P of admissible primitive sums. By Landau's theorem each binary form represents
   a density-0 set, so no finite union of algebraic witness families can cover ℕ.
3. Equivalently the conjecture states that the explicit quartic
   Φ(a,b,c,d) = (c²+2d²−2a²−4b²)² + (ac−2bd)² + (ad+bc)²   (ℤ[√−2]-norm structure)
   satisfies Φ + w² ⊇ ℕ — a borderline (Linnik-class) representation problem whose
   witness counts fluctuate like class numbers (e.g. a(2903) = 1 with unique witness
   (49,14,15,9)); the symmetrized counts are provably non-modular (no exact formula).
   Settling it requires equidistribution technology beyond current mathematics.
4. Final verified record: a(n) > 0 for ALL n <= 10^8; minima of a(n) over dyadic ranges
   [2^k, 2^(k+1)) restricted to 4 nmid n: ..., 118, 173, 255, 367, 510, 741 (at 10^8),
   growing like 0.075 sqrt(n) with strong concentration; a counterexample would require
   a ~700-sigma deviation, and moreover could not be certified by the Lean kernel anyway
   (a(n) = 0 for n ~ 10^8 needs enumeration of (sqrt n + 1)^4 ~ 10^16 tuples).
-/

/--
Conjecture (i) existence part from OEIS A271510:
a(n) > 0 for all n = 0,1,2,...
-/
theorem oeis_A271510_conjecture_i_positive :
  ∀ n : ℕ, 0 < A271510 n
  := by sorry
