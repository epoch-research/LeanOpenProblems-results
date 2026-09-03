# Growing heights and the unresolved cross-scale estimate

## Status

The conjecture in Spec.lean is still unresolved. This continuation produced
no new Lean theorem and did not change Spec.lean. In particular, none of the
observations below is asserted to prove or disprove the conjecture.

## Quantitative review of the available range-independent family

The range-independent finite-field family genuinely permits its maximum
level to grow with the prime. Its hypotheses put the maximum level below
a fixed multiple of p (depending on precision), while its minimum level
is fixed before p. Consequently, a fixed-height-range restriction is NOT
an intrinsic limitation of all the existing finite-field family results.
The bounded monotone operator theorem is weaker in this respect than the
underlying range-independent family.

This does not by itself permit the required inverse-square-root profile
to be rounded down to a fixed natural cutoff. The spatial estimates used
in the operator proof have an error relative to the FULL mixed mean, not
to the mean inside the endpoint interval. For heights w about sqrt(M/n),
the full mixed mean is about (M/n) log M. Applying the existing interval
bound therefore gives an error budget of order

    eta (M/n) log M,

not eta log n. With the more accurate height normalization

    w^2 about M log(n+2) / ((n+1) log M),

the same issue appears as an error budget of order

    eta M log(n+2) / (n+1).

These are scaling observations about the currently available upper bounds,
not lower bounds on the actual error of every possible realization. They
must not be turned into an impossibility theorem for the conjecture.

The unshifted literal curve encoding also has the separately proved empty
initial row, described in LiteralTemplateLimitProgress.md. That theorem
applies only to its stated unshifted encoding, not to arbitrary translations
or arbitrary candidate sets.

## Compatibility review

The following remain different requirements:

* a single finite operator is causal in its input profile;
* its mixed estimates hold for every pair of admissible profiles;
* operators selected at different moduli agree on an existing natural prefix;
* estimates hold on every target above thresholds chosen before the final
  finite cutoff.

Only the first two are supplied by JointMonotoneProfileOperatorExplore.lean.
No inference establishing the latter two was found in this continuation.

Several possible alternatives were considered, but none supplied a proof:
changing the field while retaining an old prefix; replacing fields by nested
prime-power rings; and repairing the small-tolerance exceptions of the
infinite probabilistic construction. In particular, the known
sub-square-root completion hypothesis is still not met by the existing
power-saving exceptional-set theorem.

## Next genuine requirement

A proof still needs a new cross-scale construction, spatial estimates useful
at the required small local means together with compatible prefixes, a
stronger infinite correction mechanism, or a universal contradiction.
The review above is not a substitute for any of these.
