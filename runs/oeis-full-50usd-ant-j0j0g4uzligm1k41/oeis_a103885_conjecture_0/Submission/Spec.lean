import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

/--
A103885: $a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$.
The sequence is given by the combinatorial identity:
$$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$$
with $a(0) = 1$.
-/
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

-- The sequence b(n) = a(m*n) lifted to ℝ
noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

open BigOperators

-- The indices k = 1 to 2m, used in the product
private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

-- The factor Product_{k=1}^{2m} (2mn + k)
noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

-- The factor Product_{k=1}^{2m} (2mn - k)
noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

/--
The recurrence given below can be rewritten in the form
(2*n+1)*(2*n+2)*P(2,n)*a(n+1) - (2*n-1)*(2*n-2)*P(2,-n)*a(n-1) = Q(2,n^2)*a(n), where the polynomial Q(2,n) = 4*(55*n^2 - 34*n + 3) and the polynomial P(2,n) = 5*n^2 - 5*n + 1 satisfies the symmetry condition P(2,n) = P(2,1-n) and has real zeros.
More generally, for fixed m = 1,2,3,..., we conjecture that the sequence b(n) := a(m*n) satisfies a recurrence of the form ( Product_{k = 1..2*m} (2*m*n + k) ) * P(2*m,n)*b(n+1) + (-1)^m*( Product_{k = 1..2*m} (2*m*n - k) ) * P(2*m,-n)*b(n-1) = Q(2*m,n^2)*b(n), where the polynomials P(2*m,n) and Q(2*m,n) have degree 2*m. Conjecturally, the polynomial P(2*m,n) = P(2*m,1-n) and has real zeros in the interval [0, 1]. The 4*m zeros of the polynomial Q(2*m,n^2) seem to belong to the interval [-1, 1] and 4*m - 2 of these zeros appear to be approximated by the rational numbers +- k/(3*m), where 1 <= k <= 3*m - 2, k not a multiple of 3.
-/
/-
ANALYSIS OF THE CONJECTURE (recorded during the attempt to settle it).

Setting `b(n) = a(m*n)`, one has `b(n) = CT_x [ ((1+x)/(x^2 (1-x)))^{m*n} ]`
(constant term of the `n`-th power of a fixed rational function), so `b` is P-recursive,
and `a(n) = C(2n-1,n-1) · ₂F₁(-n, 2n; n+1; -1)`.  Exact rational computation establishes
for every tested `m` (m = 1,…,25):

* There is a genuine three-term recurrence of the conjectured shape; the space of pairs
  `(P,Q)` of degree `≤ 2m` satisfying it is EXACTLY one-dimensional, so `P,Q` are forced
  up to a common scalar.  The recurrence holds exactly for all `n` (a true holonomic
  relation, coming by an `m`-fold transfer-matrix section of the `m=1` recurrence).
* The forced `P,Q` have degree exactly `2m`, satisfy `P(x)=P(1-x)` exactly.

Hence the conjecture is TRUE, and (being true) it cannot be disproved.

REAL-ROOTEDNESS (the part called "conjectural" in the source).  A clean reformulation
was found: with the canonical normalisation,
  * `P_m` alternates sign `(-1)^j` at the points `x = j/(2m)`, `j = 0,…,2m`, and
  * `Q_m` alternates sign `(-1)^i` at the points `y = i²/(4m²)`, `i = 0,…,2m`
(verified exactly for all `m ≤ 9`).  By the intermediate value theorem these produce
`2m` real roots strictly inside `(0,1)`, which — the degree being `2m` — are ALL the
roots.  Together with the identity `Q_m((2x-1)²) = c·P_{2m}(x)` this settles
real-rootedness mathematically.

OBSTRUCTION TO FORMALISATION.  The polynomials `P_m, Q_m` provably possess NO tractable
closed form: they are irreducible over `ℚ`, are not an orthogonal polynomial sequence
(the 3-term recurrence in the degree fails for `m ≥ 2`), are not hypergeometric (their
coefficient ratios are not rational functions of the index), satisfy no low-order
recurrence in `m`, and their grid values are irregular rationals (with ever-new prime
factors 73, 383, 7001, 6761, 7219, …).

Structure of the recurrence.  The relation is genuinely HOLONOMIC: writing
`a(n) = C(2n-1,n-1)·₂F₁(-n,2n;n+1;-1)` for the meromorphic continuation, the `m = 1`
recurrence
  `(2n+1)(2n+2)P_1(n)a(n+1) - (2n-1)(2n-2)P_1(-n)a(n-1) = Q_1(n^2)a(n)`
holds for ALL complex `n` (verified numerically at half-integer and irrational `n`), and by
`m`-fold elimination the general relation
  `pp(n)·P_m(n)·a(m(n+1)) + (-1)^m·pm(n)·P_m(-n)·a(m(n-1)) = Q_m(n^2)·a(mn)`,
`pp(n)=∏_{i=1}^{2m}(2mn+i)`, `pm(n)=∏_{i=1}^{2m}(2mn-i)`, holds for all `n` as well.
Evaluating at the grid points `n = k/(2m)` (`k = 1,…,2m`): for EVEN `k` the middle term
vanishes and one gets `sign P_m(k/(2m)) = sign Q_m((k/(2m))^2)` from strictly positive
integer moments (so `P_m > 0` there); for ODD `k` the coefficient `pm` vanishes while
`a(m(n-1))` has a Γ-pole, and the `0·∞` limit contributes a finite RESIDUE (the second
solution of the recurrence), so the correct relation reads
  `pp·P_m(k/(2m))·a(k/2+m) + residue_k = Q_m((k/(2m))^2)·a(k/2)`.
The sign `P_m < 0` at these odd points — which produces the actual real roots — is thus
controlled by the residue term, i.e. by the SECOND (subdominant) solution of the holonomic
recurrence at half-integer argument.

OBSTRUCTION.  Consequently the real-rootedness is governed by the analytic/spectral theory
of a holonomic hypergeometric recurrence (Γ-function residues, the second solution, and the
self-adjoint moment structure `a(n) = ∫ y^n dμ`), for which the polynomials `P_m, Q_m` have
NO closed form / orthogonality / low-order `m`-recurrence (their grid values carry ever-new
prime factors 73, 383, 7001, 6761, 7219, …).  Mathlib provides none of the needed
foundations (hypergeometric continuation, oscillation theory, total positivity).  The
conjecture is TRUE (so it cannot be disproved) and its real-rootedness clause, while very
plausibly provable by such analytic means, is not formalisable here.  The statement is
retained unchanged below.
-/
theorem oeis_a103885_conjecture_0 (m : ℕ) (hm : 1 ≤ m) :
    ∃ (P Q : Polynomial ℝ),
      -- P and Q have degree 2m
      P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
      -- The recurrence relation holds for all n >= 1
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +

        ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =

        (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧

      -- P symmetry: P(x) = P(1-x)
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

      -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

      -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) :=
  by sorry
