# Rational-tail recurrence investigation (not a proof)

Use indices n >= 2, and put

    d_n = n! - 1,
    S_n = sum_{k=2}^n 1/d_k,
    r_n = alpha - S_n,
    D_n = product_{k=2}^n d_k.

The exact denominator recurrence is

    d_{n+1} = (n+1)d_n + n.

Assuming alpha = p/q, with q > 0, gives an integer

    T_n = p D_n - q sum_{k=2}^n (D_n/d_k) = q D_n r_n.

Here D_n/d_k is an integer. The resulting exact recurrence is

    T_{n+1} = d_{n+1} T_n - q D_n.

Eliminating D_n gives the second-order homogeneous recurrence

    T_{n+1} = (d_{n+1}+d_n) T_n - d_n^2 T_{n-1}.

These are the same continuant recurrences behind Euler's generalized
continued fraction. They do not supply new rational approximations.

## Why this is not an integer-descent argument

The tail satisfies

    1/d_{n+1} < r_n <= ((n+2)/(n+1)) / d_{n+1}.

For the upper bound, every subsequent term is at most 1/(n+2) times
its predecessor; the denominator recurrence gives the strict ratio bound.
Consequently, under rationality,

    q D_n/d_{n+1} < T_n <= q D_n ((n+2)/(n+1))/d_{n+1}.

In particular T_n is of order q D_n/(n+1)!, not of order q/(n+1)!.
The product D_n is much larger than a single factorial. Also

    T_n/T_{n-1} = d_n r_n/r_{n-1}
                ~ d_n/(n+1),

so these cleared numerators grow rapidly. Small real tails therefore do
not yield small positive integers, or a descending sequence of integers.
Passing to reduced numerators would require new gcd estimates and has
not supplied a descent either.

## Status

No complete proof or disproof follows from this investigation.
Submission/Spec.lean remains unchanged. The verified no-return lemmas
are in Submission/Development.lean; infinitely many carry changes remain
unproved.
