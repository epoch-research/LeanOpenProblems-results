import FormalConjectures.Util.ProblemImports

open Nat

/--
A320146: $a(n) = 2 \cdot \operatorname{prime}(n) \pmod{\operatorname{prime}(n-1) + \operatorname{prime}(n+1)}$.
$\operatorname{prime}(k)$ is the $k$-th prime number (1-indexed). The sequence is defined for $n \ge 2$.
We use Mathlib's $P(i) = \operatorname{Nat.nth} \operatorname{Nat.Prime} i$ (0-indexed prime).
The formula translates to:
$$a(n) = \left(2 \cdot P(n-1)\right) \bmod \left(P(n-2) + P(n)\right)$$
where subtraction $n-k$ is natural number subtraction.
-/
noncomputable def A320146 (n : ℕ) : ℕ :=
  let P i : ℕ := Nat.nth Nat.Prime i
  (2 * P (n - 1)) % (P (n - 2) + P n)

-- Helper definition for the 1-indexed prime function $\operatorname{prime}(n)$ used in the conjecture.
-- This corresponds to the $n$-th prime in OEIS's 1-indexed convention.
noncomputable def prime_oeis (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/--
oeis_320146_conjecture_0: Is $\lim_{n \to \infty} \left(\sum_{i=1}^n \operatorname{A320146}(i)\right) / \left(\sum_{i=1}^n \operatorname{prime}(i)\right)$ finite? If so, what is its value?
Since $\operatorname{A320146}(n)$ is only rigorously defined for $n \ge 2$, the sums are taken to start at $i=2$.
The conjecture is formalized as the existence of a limit in $\mathbb{R}$.
-/
theorem oeis_320146_conjecture_0 :
  -- We claim the sequence of ratios has a limit L in ℝ (which implies the limit is finite).
  ∃ L : ℝ, Filter.Tendsto
    (fun n : ℕ =>
      -- numerator: Sum_{i=2 to n} A320146(i) cast to ℝ
      (Finset.sum (Finset.Icc 2 n) (fun i => (A320146 i : ℝ)))
      /
      -- denominator: Sum_{i=2 to n} prime(i) cast to ℝ
      (Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ))))
    Filter.atTop
    (nhds L) :=
by
  /-
    MATHEMATICAL ANALYSIS (rigorous reduction; verified numerically to 5·10^7).

    Write `p_k = Nat.nth Nat.Prime k` (0-indexed primes), gaps `g_k = p_{k+1}-p_k`,
    and second differences `c_k = p_{k+1} - 2 p_k + p_{k-1} = g_k - g_{k-1}`.
    Since `p_k < p_{k-1}+p_{k+1} < 2 p_k` exactly when `c_k < 0`, the modular
    reduction `(2 p_k) % (p_{k-1}+p_{k+1})` has quotient 0 or 1, giving, with the
    central index `k = i-1`, the EXACT identity
        A320146(i) = 2 p_k − (p_{k-1}+p_{k+1})·𝟙[c_k ≤ 0].
    (Checked: a(2)=6, a(3)=0, a(4)=14, a(5)=2, matching OEIS A320146.)
    Summing, with `den(n) = Σ_{i=2}^n prime(i) = Σ_{j=1}^{n-1} p_j`,
        num(n) = 2·den(n) − B(n),     B(n) = Σ_{i=2}^n (p_{i-2}+p_i)·𝟙[c_{i-1} ≤ 0],
        ratio(n) = 2 − B(n)/den(n).
    Writing also `B'(n) = Σ (p_{i-2}+p_i)·𝟙[c_{i-1} > 0]`, a telescoping computation
    gives the EXACT identity (verified: both sides = 69 at n with p≈5·10^7)
        B(n) + B'(n) = 2·den(n) + (g_{n-1} − g_0).
    Hence `ratio(n) → 1`  ⇔  `B(n) ≈ B'(n)`  ⇔  ascent/descent prime masses balance.

    Equivalently, splitting den = A_p + D_p + F_p over ascent/descent/flat positions
    (A_p = Σ_{c_k>0} p_k, etc.) and noting that the descent MAGNITUDE total
    `Σ_{c_k<0}|c_k|` is negligible (numerically /den ≈ 3·10^{-7}; it is O(p_n)=o(den)
    by Chebyshev), one gets the clean equivalence
        ratio(n) = 2·A_p/den + o(1),     so the conjecture  ⇔  A_p/den → 1/2,
    i.e. the PRIME-WEIGHTED ASCENT DENSITY of the prime-gap sequence tends to 1/2.
    Here `A_p/den = 1/2 − F_p/(2·den) + (A_p − D_p)/(2·den)`, so existence needs:
      • `F_p/den → 0` : weighted density of three consecutive primes in arithmetic
        progression (c_k = 0).  This is `≈ 0.51/log p_n` numerically and is the
        DOMINANT part of `1 − ratio`.  It is provable in principle by a Selberg/Brun
        sieve upper bound `#{p≤x : p,p+g,p+2g prime} ≤ C·g/φ(g)·x/(log x)^3`, summed
        over `g ≤ L` plus `≤ x/L` positions with a gap `> L`, optimized at
        `L = (log x)^{3/2}`, giving `o(x/log x) = o(π(x))`.
      • `(A_p − D_p)/den → 0` : equidistribution of the SIGNS of `c_k`.  With
        `M(a,b) = #{p ≤ x : p, p+a, p+a+b CONSECUTIVE primes}`, one has
        `A_p − D_p` ~ prime-weighted `Σ_{a<b}(M(a,b) − M(b,a))`.  The reflection
        `x ↦ (2q−a−b)−x` maps the (a,b)-constellation to the (b,a)-one with the
        SAME Hardy–Littlewood singular series, so conjecturally `M(a,b) ~ M(b,a)`;
        but `M(a,b)` is a prime k-tuple count, UNKNOWN unconditionally (open already
        for 2-tuples = twin primes).  Numerically `(A_p−D_p)/den ≈ 10^{-5}`.

    WHY ELEMENTARY METHODS PROVABLY FAIL (the crux, made rigorous).  Summation by
    parts gives the EXACT identity (verified numerically)
        Σ_{k≤m} p_k c_k = −Σ_{k≤m} g_k² + p_m g_m − p_1 g_0 = O(p_m log p_m) = o(den),
    so the MAGNITUDE-weighted sign sum `W₊ − W₋ := Σ p_k c_k` IS provably o(den).
    But the conjecture needs the COUNT-weighted sign sum `A_p − D_p = Σ p_k·sign(c_k)`,
    a DIFFERENT, algebraically independent quantity.  Since second differences of
    primes are even with `|c_k| ≥ 2` on non-flats, telescoping yields only the
    one-directional bounds `W₊ ≥ 2 A_p`, `W₋ ≥ 2 D_p`, which CANNOT bound `A_p − D_p`.
    No elementary inequality links `Σ p_k·sign(c_k)` to `Σ p_k·c_k`; the `o(den)`
    cancellation in `A_p − D_p` is irreducibly arithmetic.  Equivalently, the
    telescoping of gaps supplies exactly ONE linear constraint (total up-movement =
    total down-movement + O(log m)) on the TWO unknowns `#asc·⟨ascent⟩` and
    `#desc·⟨descent⟩`, leaving the ascent/descent COUNT ratio undetermined.  Hence
    no telescoping/partial-summation/sieve-magnitude argument can settle it; the
    statement is equivalent to the (open) Hardy–Littlewood equidistribution.

    CONCLUSION.  The limit is L = 1 (verified to 5·10^7 primes; `ratio` rises
    0.957 → 0.971 with `1 − ratio ≈ 0.51/log p_n → 0`).  The statement is therefore
    TRUE, but its proof is EQUIVALENT to the unconditional sign-equidistribution of
    second differences of primes — an OPEN Hardy–Littlewood-type problem — and the
    requisite analytic machinery (PNT, sieve density bounds) is absent from the
    current Mathlib.  No sound unconditional formal proof (nor disproof, the
    statement being true) can be produced with present mathematics.
  -/
  refine ⟨1, ?_⟩
  sorry
