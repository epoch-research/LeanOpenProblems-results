# Direct-series Padé specialization: factorial divisibility

Verified auxiliary arithmetic, NOT a proof or disproof of Erdos 68.
Spec.lean is unchanged with its original sorry. No settlement has been
submitted.

`DirectPadeSpecialization.lean` compiles without warnings and has a built
olean. Its principal axiom audits use only propext, Classical.choice, and
Quot.sound. The file has no proof holes and uses no numerical premises.

## General weighted-relation theorem

Let L>=2, let n_i>=L, and let w_i be integers. If

    sum_i w_i/(n_i!-1)=0,

then

    L! divides sum_i w_i.

For each i, write n_i!=L!*a_i with integral a_i. The zero relation gives

    sum_i w_i = L!*sum_i w_i*a_i/(n_i!-1).

Every n_i!-1 is coprime to L!, and this remains true of the reduced
denominator of the rational sum on the right. An integer equal to L!
times such a rational number must be divisible by L!. This is proved
using reduced rational denominators and integer coprimality, not an
unjustified reduction of arbitrary rational numbers modulo L!.

The theorem is `factorial_dvd_weight_sum`.

## Exact Padé specialization

Define the formal power series

    F(z)=sum_(n>=2) z^n/(n!-1).

The Lean definition uses the same coefficient formula also at n=0,1,
where division by zero gives zero; both initial coefficients are separately
verified to be zero.

For Q in Z[z], write m=natDegree Q. If N>=m+2 and

    sum_(j=0)^m Q_j/((N-j)!-1)=0,

then

    (N-m)! divides Q(1).

This needs only the SINGLE indicated coefficient equation. It does not
require all preceding coefficients to vanish.

`pade_factorial_dvd_specialization` gives the formal-power-series version:
if P is a rational polynomial of degree less than N and the coefficient
at z^N of Q*F-P is zero, the displayed divisibility follows.

`pade_factorial_dvd_of_degree_bounds` packages a common degree bound M:
if deg P,deg Q<=M and N>=M+2, then (N-M)! divides Q(1).

## Height consequence and rational-input clearing

If Q(1)!=0 and every integer coefficient has absolute value at most H,
then

    (N-m)! <= (m+1)*H.

Consequently, a smaller height budget forces Q(1)=0. The formal declarations
are `specialization_height_bound` and `specialization_zero_of_small_height`.

For a rational q with den(q)<=N-m, the same divisibility already clears
q's denominator. Thus, for any integer b,

    Q(1)*q-b

is an integer (`rational_form_integer`). This theorem asserts neither
nonvanishing nor smallness.

## What this does NOT establish

The result concerns the integer polynomial Q BEFORE reducing the final
specialized coefficient pair. If a common factor is removed from Q(1) and
P(1), the new retained coefficient need not retain the same factorial
divisibility. P(1) itself need not be integral when P has rational
coefficients. Neither issue can be ignored in an irrationality argument.

No bound for a small integral P(1), no nonzero-value theorem, and no growing
family with errors tending to zero is constructed. In particular, this is
not a proof that Padé approximants diverge p-adically at z=1; coefficient
congruences alone do not establish such a limiting assertion. It is also
not an impossibility theorem for all direct-series Padé methods.

The earlier direct Padé experiments had large primitive errors beyond their
first cases. The new theorem does not replace those finite observations
with an asymptotic error bound or settle the conjecture.

No new numerical search was run. All compilation and axiom checks are
complete, and no process remains pending.
