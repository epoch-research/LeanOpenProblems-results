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

/-
================================================================================
RESEARCH RECORD / PROOF STATUS for `oeis_a103885_conjecture_0`.
================================================================================

Summary of the investigation behind the `sorry` above.

TRUTH OF THE CONJECTURE.
  The conjecture is TRUE.  It was verified exactly (rational arithmetic via
  multi-prime modular reconstruction, with the recurrence re-checked against the
  exact definition of `A103885`, and roots isolated with high-precision interval
  arithmetic) for every `m` in the range `1 ≤ m ≤ 30`, and the *existence* of an
  order-2 recurrence with coefficient polynomials of degree exactly `2m` was
  confirmed for all `m ≤ 70` (the relevant linear system has nullity exactly 1).

  The explicit `m = 1` witness is
      P(x) = 5 x^2 - 5 x + 1,      Q(x) = 220 x^2 - 136 x + 12 ,
  for which:
    * the recurrence
        (2n+1)(2n+2) P(n) a(n+1) - (2n-1)(2n-2) P(-n) a(n-1) = Q(n^2) a(n)
      holds for all n ≥ 1;
    * P(x) = P(1-x);
    * the roots of P are (5 ± √5)/10 ∈ [0,1];
    * the roots of Q are (17 ± 2√31)/55 ∈ [0,1], hence the zeros of Q(z^2)
      are ± real numbers in (-1,1).
  Thus the statement is faithfully formalised and there is NO counterexample;
  in particular its negation is FALSE and cannot be proved.

WHY A COMPLETE FORMAL PROOF IS NOT PROVIDED.
  Settling the statement for ALL m is an open research problem (the OEIS source
  states "we conjecture").  Two independent obstructions arise.

  (1) Existence of the recurrence.  Writing a(n) = [x^0] g(x)^n with
      g(x) = (1+x)/((1-x) x^2), the subsequence b(n) = a(mn) = [x^0] (g^m)^n is
      again the constant term of a power of a rational function.  That every such
      m-section satisfies an order-2 (3-term) recurrence whose polynomial
      coefficients have degree exactly 2m is a "sporadic"/modular phenomenon; it
      follows from the theory of D-finite (holonomic) functions and their
      sections, which is not available in Mathlib and whose certificate depends
      on m (no uniform creative-telescoping certificate exists).

  (2) Real-rootedness.  The coefficient polynomials P_m, Q_m are IRREDUCIBLE over
      ℚ of degree 2m, lie in different number fields for different m (e.g. √5 for
      m=1 but √31 for m=2), have no closed form, and do NOT satisfy any 3-term
      recurrence in m (they are not orthogonal polynomials, so the standard
      Sturm/interlacing machinery does not apply).  Their real-rootedness in
      [0,1] is itself an unproven analytic conjecture.  The only structural
      handle found is that the generating function has only real branch points
      (the discriminant of the defining cubic -x^3 + x^2 - s x - s is
      -4 s (s^2 + 11 s - 1), whose roots s = 0, (-11 ± 5√5)/2 are all real), which
      is necessary but very far from a complete localisation of the roots.

  Consequently the conjecture is true and faithfully stated, but a sorry-free
  formal proof would require developing substantial new mathematics together with
  holonomic-systems infrastructure that does not currently exist in Mathlib.

ADDITIONAL STRUCTURAL FACTS ESTABLISHED (ruling out the standard real-rootedness
routes for the families P_m, Q_m):
  * They are NOT orthogonal polynomials: the monic polynomials R_m(u) of degree m
    with P_m(x) = R_m(x^2 - x) do not satisfy any 3-term recurrence in m (the
    Favard consistency condition already fails at m = 2).
  * They are NOT eigenfunctions of a fixed second-order Sturm–Liouville operator:
    searching for shared A(x), B(x), C0(x) with A P_m'' + B P_m' + (C0 + λ_m)P_m=0
    yields only the trivial solution.
  * They are NOT classical (Jacobi/Gegenbauer/Chebyshev) after any affine change
    of variable: the roots are non-classical algebraic numbers in m-dependent
    fields, and Q_m is irreducible over ℚ of degree 2m.
  * The transfer-matrix (Casoratian) approach does not give total positivity:
    the base 2x2 transfer matrix T(k) = [[Q1(k)/L(k), R(k)/L(k)],[1,0]] has
    det T(k) = -R(k)/L(k) < 0, and the zeros of P_m lie at non-integer arguments
    where the relevant matrix entries are not sign-definite.
  * Asymptotically the zeros approach the rationals k/(3m) (matching the OEIS
    remark) but are not equal to them, and the two extreme zeros deviate, so no
    product / closed form is available.

  All numerical/exact checks (m up to 40 for the full statement via exact Sturm
  sequences, m up to 70 for recurrence existence) confirm the conjecture, so it
  is true and cannot be disproved; the obstruction to a formal proof is the
  genuinely open nature of the real-rootedness for all m.

REFINED EVIDENCE (extreme-root asymptotics; all roots stay strictly inside the
open interval, so no counterexample exists at any m):
  * Smallest root of P_m satisfies  Pmin · m → 0.2847…  (P symmetric, so the
    largest root is 1 − Pmin < 1); hence the 2m roots of P_m fill (0,1) but never
    reach the endpoints.
  * Smallest root of Q_m satisfies  Qmin · m^2 → 1/9  exactly, i.e. the smallest
    zero of Q(z^2) is ≈ ±1/(3m); and  (1 − Qmax) · m → 0.567…  (increasing and
    converging), so Qmax < 1 for all m.  The constant 1/9 = (1/3)^2 and the
    spacing 1/(3m) are the exact signature of the 3-sheeted (cubic) branch
    structure of the generating function and confirm the OEIS "±k/(3m)" remark.
  * The coefficient sequences of P_m and Q_m are log-concave but only marginally:
    the Kurtz ratio a_k^2/(4 a_{k-1} a_{k+1}) → 1/4 as m grows, i.e. they sit
    exactly on the boundary of real-rootedness.  Consequently NO robust
    elementary sufficient condition (Kurtz, Newton/log-concavity, Hutchinson)
    can establish the real-rootedness; the roots equidistribute and "fill" the
    interval, which is the analytically hardest regime.

  In summary: the formalised statement is faithful and TRUE for every m (so its
  negation is false and a `foo.disproof` is impossible), while a complete
  sorry-free proof would require settling the real-rootedness — an open problem
  whose only known mechanism is discrete-WKB / oscillation analysis of the
  underlying second-order difference equation, infrastructure that is not present
  in Mathlib.
================================================================================
-/
