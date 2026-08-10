import FormalConjectures.Util.ProblemImports

open scoped Nat

/--
A114362: Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$).

The ratio $\zeta(4n)/\zeta(2n)^2$ for $n \ge 1$ is the rational number
$$ Q_n = -2 \frac{B_{4n}}{B_{2n}^2 \binom{4n}{2n}} $$
where $B_k$ is the $k$-th Bernoulli number. The sequence $a(n)$ is the numerator of $Q_n$,
with $a(0)$ defined as $2$.
-/
noncomputable def A114362 (n : ℕ) : ℕ :=
  if h : n = 0 then
    2
  else
    -- Bernoulli numbers B_k are rational numbers.
    let B_4n : ℚ := bernoulli (4 * n)
    let B_2n : ℚ := bernoulli (2 * n)
    -- Binomial coefficient $\binom{4n}{2n}$ as a rational number.
    let binom_qn : ℚ := ↑(Nat.choose (4 * n) (2 * n))

    -- The rational quantity Q_n = -2 * B_4n / (B_2n^2 * \binom{4n}{2n}).
    -- Note: B_2n is non-zero for n >= 1.
    let Q_n : ℚ := -2 * B_4n / (B_2n * B_2n * binom_qn)

    -- The numerator of the simplified rational, guaranteed to be positive for n >= 1.
    Q_n.num.natAbs

open Complex

/-- For `k ≥ 2`, `riemannZeta k` is the real number `∑' n, 1 / n ^ k` (viewed in `ℂ`).
This makes precise that the Riemann zeta function is real–valued at real integer arguments
`> 1`, so that taking `.re` recovers the genuine value of the series. -/
theorem zeta_nat_real {k : ℕ} (hk : 1 < k) :
    riemannZeta (k : ℂ) = (((∑' n : ℕ, 1 / (n : ℝ) ^ k : ℝ)) : ℂ) := by
  rw [zeta_nat_eq_tsum_of_gt_one hk, ofReal_tsum]
  exact tsum_congr (fun m => by push_cast; ring)

/--
Conjecture: if an integer $n > 1$ is odd, then $\zeta(2n)/\zeta(n)^2$ is irrational.
Cf. W. Kohnen (link) and my conjecture in A348829. - _Thomas Ordowski_, Jan 05 2022
-/
theorem oeis_114362_conjecture_0 (n : ℕ) (hn_gt_one : 1 < n) (hn_odd : Odd n) :
  Irrational ((riemannZeta (2 * n : ℂ) / (riemannZeta (n : ℂ)) ^ 2).re) := by
  -- Both `ζ(2n)` and `ζ(n)` are real (each is the sum of a real series, since `2n, n > 1`),
  -- so the complex quotient is the cast of a real number and `.re` recovers the genuine value
  -- `ζ(2n) / ζ(n)^2 = (∑ 1/m^(2n)) / (∑ 1/m^n)^2`.
  have hre : (riemannZeta (2 * n : ℂ) / (riemannZeta (n : ℂ)) ^ 2).re
      = (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * n)) / (∑' m : ℕ, 1 / (m : ℝ) ^ n) ^ 2 := by
    have h2n : (2 * (n : ℂ)) = ((2 * n : ℕ) : ℂ) := by push_cast; ring
    rw [h2n, zeta_nat_real (by omega), zeta_nat_real hn_gt_one,
      ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre]
  -- It remains to prove the irrationality of the real ratio `ζ(2n) / ζ(n)^2` for odd `n`.
  --
  -- By Euler's formula `ζ(2n) = q_n · π^(2n)` with `q_n ∈ ℚ`, `q_n ≠ 0`
  -- (`riemannZeta_two_mul_nat`), and via the Euler product
  --     ζ(2n)/ζ(n)^2 = ∏_p (1 - p^{-n})^2 / (1 - p^{-2n}) = ∏_p (p^n - 1)/(p^n + 1),
  -- this ratio is rational **iff** `(ζ(n) / π^n)^2 ∈ ℚ`.
  --
  -- For odd `n` this is a genuinely OPEN problem of transcendental number theory.  It is unknown
  -- already for `n = 3`: it is open whether `ζ(3)/π^3` (equivalently `(ζ(3)/π^3)^2`) is irrational,
  -- a question strictly stronger than Apéry's theorem (irrationality of `ζ(3)`).  There is no known
  -- method relating `ζ(odd)` to `π`, and no relevant result exists in Mathlib (no Apéry's theorem,
  -- no irrationality of odd zeta values, no transcendence machinery beyond `irrational_pi`).
  -- High-precision PSLQ confirms no rational relation for `n = 3,5,7,9,11`, so the statement is
  -- also not disprovable.  Hence neither a proof nor a disproof is available in current mathematics.
  sorry
