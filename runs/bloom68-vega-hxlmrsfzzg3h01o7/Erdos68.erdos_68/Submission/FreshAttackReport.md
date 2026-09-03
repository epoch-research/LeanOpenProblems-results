# Independent attack on the real factorial-minus-one series

## Outcome

No proof or disproof of the irrationality of

\[
S=\sum_{n=2}^{\infty}\frac1{n!-1}
\]

was obtained. The results below are complete arguments, not assumptions of the missing irrationality statement. They give an exact arithmetic reformulation and rule out several natural constructions. No numerical approximation to S is used as evidence. The original `Submission/Spec.lean` was not edited or imported. No prior `/tmp/erdos68*` reports were consulted.

`FreshAttack.lean` and `FreshCertificates.lean` compile under Lean 4.27.0. Neither contains `sorry`, `admit`, or a new axiom. `FreshAudit.lean` checks their key dependencies: only `propext`, `Classical.choice`, and `Quot.sound`. In particular, none depends on the two placeholders in Spec. The finite denominator computations use `decide +kernel`, not `native_decide`.

## 1. Analytic control and all basic denominators

Write
\[
a_n=n!-1,\qquad P_N=\sum_{n=2}^N\frac1{a_n},\qquad R_N=S-P_N.
\]
For every n >= 2, n! >= 2, so a_n >= 1. Every reciprocal in S is therefore ordinary division by a strictly positive real number. Moreover
\[
a_{n+1}=(n+1)a_n+n>(n+1)a_n.
\]
Thus the positive summands are bounded by a geometric series with ratio 1/3, proving summability. In particular the `tsum` in the target is an ordinary convergent real sum, not the default value of a divergent `tsum`.

For N >= 3, the following strict bounds hold:
\[
\boxed{\frac1{N+1}<N!R_N<\frac1N.}\tag{1}
\]
The lower bound follows already from the first omitted summand. For the upper bound, successive terms after that first summand have ratio at most 1/(N+2), so
\[
R_N\le\frac{N+2}{N+1}\frac1{(N+1)!-1}.
\]
Multiplying by N! gives a bound strictly less than 1/N precisely when N! > N+1, which holds for N >= 3. All denominators in these comparisons are positive. Also R_N > 0, so no tail-based linear form can vanish.

These facts are fully proved in Lean: `denominator_pos`, `summable_term`, `series_eq_partialSum_add_tail`, `tail_pos`, `scaled_tail_lower`, and `scaled_tail_upper`. Lean's index n corresponds to N=n+1 here.

## 2. Why the natural integer linear forms fail

### Ordinary factorial scaling is not integral

The finite arithmetic is already decisive:
\[
P_4=\frac{143}{115},\qquad 4!P_4=\frac{3432}{115}\notin\mathbb Z.
\]
So the small quantity N! R_N from (1) is not automatically an integer if S is rational. The obstruction is the finite prefix, not nonvanishing or the tail estimate.

### The true termwise common denominator makes the tail too large

Let L_N=lcm(a_2,...,a_N). Consecutive denominators are coprime: a_N=N a_{N-1}+N-1, so a common divisor divides N-1. It then divides both (N-1)! and (N-1)!-1, hence is 1. Consequently
\[
L_N\ge a_{N-1}a_N.
\]
For N >= 3,
\[
L_NR_N>\frac{a_{N-1}a_N}{a_{N+1}}
>\frac{(N-1)!-1}{N+2}.
\tag{2}
\]
The last inequality is equivalent to N! > N+1 after canceling positive factors. The right side exceeds 1 for N >= 5, and tends to infinity. Thus the familiar contradiction `0 < b L_N R_N < 1` cannot work for large N: the expression is already greater than b.

The Lean theorem is slightly more general: any positive integer D divisible by the last two term denominators satisfies the displayed lower bound. See `consecutive_denominators_coprime`, `clearing_two_denominators_lower_bound`, and `clearing_two_denominators_tail_gt_one`.

This statement concerns denominators clearing each summand. It does NOT automatically apply to the reduced denominator Q_N of P_N.

### Reduced denominators really do cancel

The assertion Q_N=L_N is false. Exact Python integer/Fraction arithmetic, independently checked by the Lean kernel, gives
\[
\boxed{L_{137}=139 Q_{137},\qquad139\nmid Q_{137}.}\tag{3}
\]
The reason can be seen without displaying the huge integers. Among 2 <= n <= 137, exactly n=69,122,137 have 139 | n!-1. They all have valuation exactly one, since
\[
\frac{69!-1}{139}\equiv6,\quad
\frac{122!-1}{139}\equiv49,\quad
\frac{137!-1}{139}\equiv73\pmod{139}.
\]
The three quotients are nonzero modulo the prime 139, while
\[
6\cdot49+6\cdot73+49\cdot73=139\cdot31.
\]
Hence the three normalized reciprocal residues sum to zero. Their combined rational contribution has no factor 139 left in its reduced denominator; all other summands are already 139-integral.

The stronger complete equality (3), not just the modular explanation, is verified by `FreshFactorialCertificates.exact_lcm_cancellation`. `denominator_loses_139` separately checks the nondivisibility. This is a counterexample to a denominator hypothesis, not computational evidence of irrationality.

## 3. A genuine accelerated approximation and its obstruction

The exact geometric identity, for f=n! >= 2 and K >= 0, is
\[
\frac1{f-1}=\sum_{j=1}^{K}\frac1{f^j}
 +\frac1{f^K(f-1)}.
\tag{4}
\]
Its remainder is strictly positive; f^K and f-1 are nonzero. Both assertions are fully proved in Lean (`finite_geometric_expansion` and `finite_geometric_remainder_pos`).

I tried using exact initial terms and then this accelerated expansion. For N >= 5, M >= N+1, K >= 1 define the rational approximation
\[
B_{N,M,K}=P_N+\sum_{n=N+1}^M\sum_{j=1}^{K}\frac1{(n!)^j}.
\]
Its error is exactly
\[
S-B_{N,M,K}
=\sum_{n=N+1}^M\frac1{(n!)^K(n!-1)}+R_M>0.
\]
A valid positive integer clearing denominator is
\[
D=L_N(M!)^K.
\]
Indeed a_n divides L_N for the initial terms, and (n!)^j divides (M!)^K for n <= M and j <= K. But the first geometric remainder alone gives
\[
D(S-B_{N,M,K})
>\frac{L_N}{(N+1)!-1}>1.
\]
The first inequality uses (M!)^K >= ((N+1)!)^K; the second follows from the same coprime-consecutive-denominator estimate behind (2). Increasing K shrinks the unscaled error but this clearing denominator grows too quickly. This rules out this particular positive rectangular approximation with this multiplier, not every optimized or signed approximation.

Rearranging (4) over both indices also writes S as an infinite sum of factorial-power series. Irrationality of the individual columns does not imply irrationality of their infinite sum. No such implication is used here.

## 4. Exact remaining arithmetic obstacle: a fully proved equivalence

Put
\[
A_N=N!P_N,\qquad r_N=\{A_N\}.
\]
For N >= 3 define the narrow window
\[
W_N:\quad 1-\frac1N<r_N<1-\frac1{N+1}.
\]
Then
\[
\boxed{S\in\mathbb Q\iff W_N\text{ holds for every sufficiently large }N.}\tag{5}
\]

**Forward implication.** If S=a/b with b>0, then b | N! for N >= b. Hence N!S is an integer. By (1), A_N equals that integer minus a number strictly between 1/(N+1) and 1/N, giving W_N.

**Converse.** Assume all sufficiently large N satisfy W_N. Let
\[
z_N=\lfloor A_N\rfloor+1\in\mathbb Z.
\]
Combining W_N with (1) gives
\[
|N!S-z_N|<\frac1{N(N+1)}.
\]
Therefore the integer z_{N+1}-(N+1)z_N has absolute value less than
\[
\frac1N+\frac1{(N+1)(N+2)}<1.
\]
It must be zero. Thus z_N/N! is eventually a single rational q. The preceding error bound and N! tending to infinity imply S=q.

Consequently irrationality is exactly equivalent to the existence of arbitrarily large N outside these windows. This is completely formalized in `irrational_iff_arbitrarily_large_window_failures`; `original_series_criterion` states the equivalence with the identical real `tsum` expression in Spec. The unproved goal is

```lean
∀ N : ℕ, ∃ n ≥ N, ¬ FreshFactorialAttack.InRationalityWindow n
```

The indexing of this Lean predicate is N=n+1 in the mathematical display. There is no assumed theorem asserting that goal in the files.

The obstacle can even be phrased using integers alone. Let
\[
B_N=\prod_{n=2}^N a_n>0,\quad C_N=\sum_{n=2}^N B_N/a_n\in\mathbb Z,
\quad u_N=(N!C_N)\bmod B_N.
\]
Each quotient B_N/a_n is an exact integer, and r_N=u_N/B_N. A completion would prove that for arbitrarily large N,
\[
N u_N\le(N-1)B_N\quad\text{or}\quad(N+1)u_N\ge N B_N.
\]
I have no proof of this infinitude. It is a precise equivalent reformulation, not an established new hypothesis from which irrationality is being asserted.

## 5. Source checks and reproducibility

The attack did not stop at, or rely on, an open-problem label. The sources inspected included:

* `/corpus/src/0705.4299/0705.4299.tex` (abstract factorials): its defining divisibility and integral generalized-binomial hypotheses fail for n!-1.
* `/corpus/src/2101.05257/main.tex` (formalized Erdős--Straus criteria): the direct conversion to a Cantor series with bases a_n and numerators product(a_2,...,a_{n-1}) fails the required small-numerator hypothesis. In fact its ratio to a_{n-1}a_n is product(a_2,...,a_{n-2})/a_n, bounded below for large n by (n-3)!/[4n(n-1)], so it does not tend to zero.
* `/corpus/src/0807.1376` (divisibility-based irrationality criteria): the required chain of denominators also fails.

No conclusion above depends on trusting an unverified assertion in those sources.

Run from `/workspace/leanproject`:

```sh
lake env lean Submission/FreshAttack.lean
lake env lean Submission/FreshCertificates.lean
python3 Submission/fresh_verify.py
```

The Python script uses only exact integers and `fractions.Fraction`, and explicitly does not infer irrationality from finite computations. `FreshAudit.lean` imports the compiled modules and prints their axioms. The compiled `.olean` files were placed in `.lake/build/lib/lean/Submission/`.

**Bottom line:** summability, strict tails, the termwise-clearing obstruction, the actual denominator cancellation, and the exact irrationality criterion are proved. The necessary infinitude of finite-sum window failures is not proved, so the original irrationality theorem remains unresolved by this attack.
