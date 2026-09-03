# Sublinear row tails (verified auxiliary progress, not a settlement)

`RowRemainderBounds.lean` proves a stronger bound for the existing rowwise
factorial expansion. It does not prove or disprove Erdős 68; `Spec.lean` is
unchanged.

Write

    alpha = sum_(k>=2) 1/(k!-1),
    F_n = sum_(k=2)^n floor(n!/(k!-1)),
    T_n = n!*alpha-F_n,
    c_n = F_n-n F_(n-1)  (n>=1).

## New verified results

* `rowTail_sublinear`: T_n/(n+1) tends to zero.
* `rowTail_div_self_tendsto`: T_n/n tends to zero (the value at n=0 is harmless).
* `rowCoeff_residue_of_rational`: if alpha=q is rational, n>=3, and q.den<n,

      (c_n mod n)/n = 1-T_n/n.

* `rowCoeff_residue_tendsto_one_of_rational`: under that rationality
  hypothesis, the normalized least nonnegative residues (c_n mod n)/n tend
  to 1.

Both principal printed axiom checks contain only `propext`, `Classical.choice`,
and `Quot.sound`. The file compiles and its olean has been built.

**No failure of this necessary residue limit has been proved.** In particular,
this is not an irrationality proof, and no congruence for c_n is asserted.

## Elementary proof of sublinearity

Put x_(n,k)=frac(n!/(k!-1)). If j*k<=n, multinomial divisibility gives
(k!)^j | n!. Removing an integer geometric prefix yields

    0 <= x_(n,k) <= n!/((k!)^j (k!-1)).

For positive fixed J,L, assume

    n >= 2^[L*(J^2+1)].

If 2<=k<=n, k>floor(n/J), and

    (floor(n/k)+1)*k-n > floor(n/L),

then `factorial_power_large` and `row_fraction_small` give

    n!*2^n <= (k!)^(floor(n/k)+1),
    x_(n,k) <= 2/2^n.

The factorial inequality uses the already proved block-multinomial bound

    (C*k)! <= 2^(C^2*k) (k!)^C

and the lower bound

    (C*k)! >= n! (n+1)^(C*k-n).

There are at most floor(n/J)+1 small rows k<=floor(n/J). Among the other
rows, at most J*(floor(n/L)+1) fail the gap condition. For this count, map an
exceptional k to the pair

    (floor(n/k), (floor(n/k)+1)*k-n).

This is an injection into {0,...,J-1} times {0,...,floor(n/L)}.

Each exceptional row contributes less than 1. Adding the original omitted
tail, whose scaled size is at most 3/(n+1), gives the verified estimate

    T_n/(n+1) <= 1/J + J/L
                 + (J+1)/(n+1) + 2/2^n + 3/(n+1)^2.

Taking L=J^2, then choosing J arbitrarily large, proves the limit.

The exceptional bands are essential: it is not valid to claim a uniformly
small fractional remainder for every k proportional to n. Rows just before
multiples n=j*k require the separate counting argument.

## Rational residue identity

If q.den<n, then n!*q is an integer multiple of n. Rationality makes T_n an
integer; the earlier bound 0<T_n<n-1 makes n-T_n the least nonnegative residue
of F_n modulo n. Since c_n=F_n-n F_(n-1), it has the same residue. Dividing by
n and applying sublinearity proves the necessary limit above.

Excluding that limit for the actual c_n would be a new arithmetic step. It
has not been obtained, and none of the results in this file settles the target.
