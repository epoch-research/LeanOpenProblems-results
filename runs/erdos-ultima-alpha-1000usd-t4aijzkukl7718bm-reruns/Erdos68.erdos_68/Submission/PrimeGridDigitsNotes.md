# Distributed factorial-grid corrections

Verified auxiliary arithmetic, NOT a proof or disproof of Erdos 68.
Submission/Spec.lean remains unchanged with its original sorry. No settlement
has been obtained or submitted.

PrimeGridDigits.lean compiles without warnings and has a built olean. The
printed principal axiom audits use only propext, Classical.choice, and
Quot.sound. There are no proof holes or numerical premises.

## Exact mixed-radix representation

Let p_i be any nondecreasing natural sequence, N_i=p_i!, and
r_i=N_(i+1)/N_i. For a rational correction x put

    F_i=floor(N_i*x),
    z_0=F_0,
    z_(i+1)=F_(i+1)-r_i*F_i.

The file proves, for every i,

    0<=z_(i+1)<r_i,
    sum_(i=0)^m z_i/N_i = F_m/N_m.

If N_m*x is integral, the last sum is exactly x. The first digit is NOT
asserted to lie in a radix interval; its exact floor bounds are

    N_0*x-1 < z_0 <= N_0*x.

For x>=0 all digits are nonnegative. If N_j*x<1, every digit through j
is zero. In the exact-grid case the sum of the individual absolute
boundary changes |z_i/N_i| is exactly x.

Principal declarations:

* digit_succ_bounds
* sum_digits_exact
* first_digit_bounds
* digits_nonneg
* early_digits_zero
* absolute_boundary_cost.

## Distributed prime correction

When the selected p_i are primes, use the operation

    C(f)=sum_(i=0)^m z_i*(f(p_i)-f(p_i-1)).

For the actual Lambert prefixes S_n, their unit prime coefficients give

    C(S)=x,     C(constant)=0.

Every geometric row d<p_0 has identical values at p_i and p_i-1, so C
vanishes on every such row. Thus this distributes the earlier exact
boundary lift over several prime increments and preserves all earlier
row-annihilation constraints. The main theorem is lambert_correction.

The digit bound replaces the single endpoint coefficient p_m!*x by a
first coarse-grid digit and later digits bounded by factorial ratios.
No assertion about the asymptotic sizes of prime gaps is required or
proved here. Repeated primes, giving radix one and zero subsequent digit,
are allowed by the general monotonicity hypotheses.

## Remaining gap

This construction does not give a small nonzero integer form for alpha.
Correcting boundary B to an integer b still changes the full form by
exactly -(b-B). Distributing that correction does not make b-B smaller,
and neither the exact representation nor the digit bounds exclude
A*alpha-b=0 under a rationality hypothesis.

The operation preserves rows at the selected finite indices; it does NOT
clear every translated output phase in an analytic nonvanishing window.
The initial annihilator and the locations of its support must also be
accounted for. In particular, an error bound valid only at late indices
cannot be applied to arbitrary earlier prime corrections. The zero-digit
lemma identifies when early corrections vanish, but no compatible infinite
choice closing all these requirements has been proved.

No numerical search was run. Reviews of modular lifting, prime increments,
and lattice nonvanishing supplied no complete original-conjecture argument.
The compilation log is /tmp/prime_grid_digits.log. No computation or
compilation remains pending. Spec.lean retains its original statement,
import, and sorry.
