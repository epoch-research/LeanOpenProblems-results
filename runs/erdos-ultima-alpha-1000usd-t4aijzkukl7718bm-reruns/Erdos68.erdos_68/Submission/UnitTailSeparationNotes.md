# First-unit tail separation (auxiliary; not a solution)

`Submission/UnitTailSeparation.lean` now compiles successfully. Its olean was
built, and both printed theorem axiom checks list only `propext`,
`Classical.choice`, and `Quot.sound`.

## Verified statements

For an integer sequence t, put

    I_n = 1/n + t_(n+1)/(n(n+1)).

If n divides t_(n+1)-t_n+1 on an interval [a,a+L), the previously verified
identity gives

    D = sum_(n=a)^(a+L-1) I_n
      = t_a/a - t_(a+L)/(a+L) + z,

where z is an integer. The new lemma `increment_at_unit` proves that the
first unit recurrence

    t_(a+1) = (a+1)t_a - 1

implies

    I_a = t_a/a + 1/(a+1).

Thus, with nonnegative tails and L>0, D>t_a/a, and hence z>0.
If also D+t_(a+L)/(a+L)<1, then z<1, a contradiction. This is
`no_small_increment_return`.

The second theorem, `no_close_unit_returns`, packages sufficient finite
bounds. For positive natural a,L and natural H, it rules out simultaneous:

* 0 <= t_(a+i) <= H for every i<=L+1;
* the predecessor congruences on [a,a+L);
* unit recurrences at a and a+L;
* a*L + (L+1)*H + 1 < a^2.

Indeed,

    D <= L*(1/a + H/a^2),
    t_(a+L)/(a+L) <= (H+1)/a^2.

Their sum is less than one by the displayed size condition. Unlike the
older `no_close_small_returns`, no lower bound on L beyond positivity is
needed: the exact first unit recurrence supplies the strict lower bound.
H is a local bound and may depend on the chosen interval.

## Limitation

No application to the original series has been obtained. Its Lambert
representation has the needed arithmetic properties but tails too large
for this condition. The rowwise floor representation has small tails but
no established eventual transfer of the congruences or prime-unit values.
Cancelling a fixed finite set of Lambert rows does not supply the needed
tail bounds, and the existing shift operators do not by themselves preserve
the unit-coefficient hypotheses.

The conjecture in `Submission/Spec.lean` is unchanged and still contains its
original `sorry`. No proof or disproof has been submitted.
