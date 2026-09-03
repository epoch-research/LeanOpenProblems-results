# Integer factorial coefficients after division by 1-z

This is auxiliary verified work, not a settlement of Erdős 68. Spec.lean is
unchanged with its original sorry. No complete proof or disproof was submitted.

## General verified result

`FactorialDividedDifference.lean` compiles without warnings and has a built
olean. Both printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound.

Let u_n be any integer sequence and a,b arbitrary integers. Define

    G_0=a-b*u_0,
    G_(n+1)=(n+1)*G_n-b*u_(n+1).

The G_n are integers by construction. `quotientCoeff_formula` proves,
over any characteristic-zero field,

    G_n/n! = a-b*sum_(k=0)^n u_k/k!.

For F(z)=sum u_n*z^n/n! and G(z)=sum G_n*z^n/n!, the theorem
`formal_quotient_identity` verifies the formal power-series identity

    (1-z)G(z)=a-bF(z).

This holds for EVERY a,b. In particular, the factorial-scaled integrality
of the quotient does not require F(1)=a/b and gives no contradiction to a
hypothetical rational value.

If sum u_n/n!=x in R, `normalized_coeff_limit` proves

    G_n/n! -> a-b*x.

Consequently `normalized_coeff_zero_iff` identifies the missing cancellation:

    G_n/n! -> 0  iff  a=b*x.

There is no assumption of a nonzero b in these two general statements.
The analytic interpretation of pole cancellation at z=1 is explanatory here;
the verified statements are the formal identity and coefficient limits.

## Application to the Lambert coefficients

The existing FactorialLambert file supplies u_n=a_n and the convergent sum
x=alpha. Under b*alpha=a, the G_n are positive factorial-scaled tails, but
they grow factorially times an exponential, rather than tending to zero.
For example, the d=2 Lambert row alone gives an eventual large integer
contribution. Thus integrality of G_n is not an integer-between-zero-and-one
argument. Dividing the analytic function once does not establish rationality
of its derivative at one or permit a second endpoint cancellation.

The previously verified prime-block congruences are still available for the
forcing coefficients a_n. Their first-band consequences for G_n do not give
a size contradiction at the available factorial-scale bound. No stronger
arithmetic exclusion was obtained in this pass.

## Other mathematical review in this pass

The boundary-lattice route was reconsidered with larger starting indices and
prime-band transfers to factorial-power columns. If an integer relation in
a_n/n! is supported on H<n<=T, primes p with T/2<p<=H allow replacement of
a_n by 1 modulo p after multiplication by T!. This uses the already verified
first-band congruence. It yields divisibility of the corresponding exponential
column form, not an immediate contradiction or a small nonzero form.

Using more prime blocks can involve higher factorial-power columns. Their
multinomial factors can sometimes be removed without losing the block prime,
but a bound sufficient to eliminate every possible zero-form relation was
not found. In particular, no bound on the necessary projected successive
minima or on a nonzero cleared boundary pair has been proved. These remarks
are mathematical review, not additional Lean declarations.

There was no new numerical search. No computation is pending. The original
conjecture remains unproved and undisproved in this workspace.
