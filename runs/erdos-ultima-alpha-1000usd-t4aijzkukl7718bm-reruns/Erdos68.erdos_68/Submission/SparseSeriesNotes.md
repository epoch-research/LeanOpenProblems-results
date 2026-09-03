# Sparse-power-series investigation (not a proof of Erdős 68)

For the original denominators d_n=(n+2)!-1, put

    F(z) = sum_{n>=0} z^{d_n}/d_n.

The series converges absolutely on the closed unit disk, F(1)=alpha, and,
inside the disk,

    F'(z) = sum_{n>=0} z^{d_n-1}.

Thus F' has coefficients in {0,1}. If zeta has finite order m, then
zeta^{d_n}=zeta^{-1} whenever n+2>=m. Consequently

    F(zeta) = zeta^{-1} alpha
      + sum_{n+2<m} (zeta^{d_n}-zeta^{-1})/d_n.

If alpha were rational, all these boundary values would be algebraic.
This is not itself a contradiction.

## Why these properties are insufficient

Here is a different, explicitly defined sequence with the same eventual
factorial congruences and a rational reciprocal sum. This is NOT a
counterexample to the original conjecture: its denominators are different.

Set r_0=1/4. For n>=1, recursively let

    M_n = n!,
    d_n = M_n * (floor((1/r_{n-1}+1)/M_n)+1) - 1,
    r_n = r_{n-1} - 1/d_n.

The floor inequalities give

    1/r_{n-1} < d_n <= 1/r_{n-1} + n!.

In particular, every r_n is positive and rational, and

    0 < r_n < n! * r_{n-1}^2.

Induction gives

    r_{n-1} <= 1/(2*(n+1)!).

The initial case n=1 is equality. For the induction step,

    r_n < 1/(4*(n+1)^2*n!) <= 1/(2*(n+2)!),

where the last inequality is n+2 <= 2*(n+1). Hence r_n tends to zero,
and the telescoping definition of r_n proves

    sum_{n>=1} 1/d_n = 1/4.

Also d_n+1 is divisible by n!, by construction. The denominators are
strictly increasing: the upper bound on d_n gives

    r_{n-1}*d_n <= 1+n!*r_{n-1}
                    <= 1+1/(2*(n+1)) < 2.

Thus r_n < 1/d_n, so d_{n+1} > 1/r_n > d_n.

The first denominators are 5, 21, 425, and 35711.

For this constructed sequence, G(z)=sum z^{d_n}/d_n converges absolutely
on the closed unit disk, G' has coefficients in {0,1}, and G(1)=1/4.
At every root of unity zeta, the terms eventually have phase zeta^{-1},
so G(zeta) is algebraic by the same finite-correction identity as above.

Therefore integer coefficients of the derivative, sparsity, the eventual
congruences d_n=-1 mod m for every fixed m, and algebraic boundary values
at roots of unity do not suffice to prove irrationality. Any successful
argument for the original series must use more precise structure, such
as its exact factorial denominators or their exact recurrence.

## Status

These are exploratory mathematical notes, not Lean-verified lemmas and
not a solution of the original conjecture. Submission/Spec.lean remains
unchanged.
