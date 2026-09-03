# Exact squarefree-window positivity criterion — not a settlement

`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
No sufficient signed positivity estimate or irrational counterexample was
obtained. No incomplete proof was submitted.

## Verified addition

File: `Submission/SquarefreePairWindow.lean`
Namespace: `Erdos972SquarefreePairWindow`.

Let g(n)=floor(alpha*n), and let P_t(m,n) be the existing two-scale pair
minorant. Define

    squarefreeWindow(alpha,B,N)
        = {n : B<n<=N, n and g(n) both squarefree},

    squarefreeWindowMinorant(t,alpha,B,N)
        = sum over squarefreeWindow(alpha,B,N) of P_t(n,g(n)).

The sum is SIGNED. Its non-prime terms are not silently dropped.

### Positive support

`pairMinorant_primePower_pos` proves that P_t(m,n)>0 for every t>0 when
both m,n are prime powers, without any logarithmic-window restriction.

`pairMinorant_pos_iff` proves that, when both t*log(m) and t*log(n) are
at most 1/4, positive support is EXACTLY pairs of prime powers.
Other terms may be negative; this is not an identity of full supports.

### Finite certificates and an exact reformulation

`prime_pair_of_squarefreeWindow_pos` proves, for alpha>=1 and

    t>0, t*log(g(N))<=1/4,

that positivity of squarefreeWindowMinorant supplies a genuine prime pair
B<p<=N. Squarefreeness excludes proper prime powers, so there is no need
to overcome a growing prime-power error budget.

`squarefreeWindowMinorant_tendsto` establishes the t->0+ limit with B,N
FIXED:

    (32/63) * sum over squarefreeWindow(alpha,B,N) Lambda(n)*Lambda(g(n)).

Using only this finite-sum limit, `positive_squarefreeWindow_iff` proves

    (exists valid t>0 with squarefreeWindowMinorant(t,alpha,B,N)>0)
        iff
    (exists prime pair B<p<=N).

`infinite_primeSet_iff_positive_squarefreeWindows` consequently proves the
exact equivalence between prime-pair infinitude and such positivity for
some finite N and valid t beyond every B. This criterion requires neither
linear growth nor reciprocal-weighted divergence. It is an exact
REFORMULATION, not an unconditional positivity theorem.

All five printed principal axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. The file compiles without errors and
contains no `sorry`. The temporary signature-check file was removed.

## Remaining gap

The existing positive squarefree-input/prime-output mean does not imply
this signed positivity: squarefree composite inputs remain possible.
The fixed-positive-parameter mean results likewise do not give a mean in
the finite validity window. No exchange of these limits is justified here.

The original universal irrational-slope conjecture is still unresolved.
