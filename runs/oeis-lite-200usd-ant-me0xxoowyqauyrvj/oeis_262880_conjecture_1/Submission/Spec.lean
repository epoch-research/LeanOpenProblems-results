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
theorem oeis_262880_conjecture_1 :
  ∀ n : ℕ, 0 < n →
    ∀ p : ℕ × ℕ, p ∈ A262880_Conjecture1_Pairs →
      ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x^3 + p.fst * y^3 + p.snd * z^3 :=
by
  intro n hn p hp
  -- Reduce membership to the explicit disjunction over the 18 coefficient pairs.
  simp only [A262880_Conjecture1_Pairs, List.toFinset_cons, List.toFinset_nil,
    Finset.mem_insert] at hp
  -- The remaining goal, for each fixed pair (b,c), is the universal representation
  -- n = w(w+1)/2 + x^3 + b y^3 + c z^3.  This is Zhi-Wei Sun's OPEN conjecture A262880(i):
  -- true (verified numerically well beyond 10^8) but unproven, lying at the threshold of
  -- the circle method (one quadratic plus three cubic variables, analogous to the open
  -- problem G(3)=4).  No elementary/identity proof and no finite witness reduction exists.
  sorry

/-- The set of coefficient pairs (b, c) for Conjecture (ii). -/
def A262880_Conjecture2_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (3, 4), (3, 6), (4, 8) ]
  ))
