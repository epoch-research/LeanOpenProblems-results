# Square-root-scale roughness of scaled partial-sum denominators

This is verified auxiliary arithmetic, NOT a settlement of Erdos 68.
`Submission/Spec.lean` remains unchanged with its original `sorry`.
No proof or disproof of the original conjecture has been obtained or submitted.

## Stronger bound

Let

    X_n = (n+1)! * sum_(k=0)^(n-1) 1/((k+2)!-1),

regarded as a rational number in lowest terms. The new file
`QuadraticDenominatorRoughness.lean` proves:

* If p is prime and p^2<=n+1, then p does not divide den(X_n).
* Consequently every prime divisor p of den(X_n) satisfies n+1<p^2.
* If B^2<=n+1, then gcd(B!,den(X_n))=1.
* In particular gcd(floor(sqrt(n+1))!,den(X_n))=1.

The earlier file `ScaledDenominatorRoughness.lean` established factorial
coprimality under the sufficient threshold B!<=n+1. The new square threshold
is substantially smaller for large B. This is an unconditional statement
about the exact original rational partial sums, with all cancellations allowed.

## Proof mechanism

Consider the individual scaled row n!/(m!-1), with m>=2, and a prime p
such that p^2<=n.

If p<=m, then p is coprime to m!-1, and so cannot appear in the reduced
denominator of the scaled row.

If m<p, then

    0<m!-1<p^p,
    p^p divides (p^2)! divides n!.

The factorial divisibility follows from p|p! and (p!)^p|(p*p)! by
multinomial integrality. Suppose p survived in the row's reduced denominator.
Writing the reduced numerator as u and denominator as v, we have

    |u|*(m!-1)=n!*v,   gcd(|u|,v)=1.

Since p|v, the number |u| is coprime to p^p. Therefore p^p would divide
m!-1, contradicting its strict size bound. This proof uses no valuation
estimates or external computation.

Coprimality survives finite rational sums because the reduced denominator
of a sum divides the product of the summand denominators.

## Rational tails

For an arbitrary rational q with den(q)<=n+1, the earlier exact identity

    den((n+1)!*q-X_n)=den(X_n)

transfers the stronger factorial-coprimality bound to that difference. This
statement does not require q to equal the target sum.

Main declarations:

* quotient_num_den_relation
* not_dvd_den_of_power
* self_power_dvd_square_factorial
* scaled_row_den_coprime_prime
* scaledSumQ_den_coprime_prime
* prime_factor_square_gt
* scaledSumQ_den_coprime_factorial
* scaledSumQ_den_coprime_sqrt_factorial
* rational_tail_den_coprime_factorial

The file compiles without warnings and has a built olean. Its four printed
principal axiom audits list only propext, Classical.choice, and Quot.sound.

## Remaining gap

This gives a stronger roughness condition, not the upper denominator bound
or nonvanishing integer form needed for irrationality. Rational numbers with
large rough denominators can be positive and small, including of order 1/n.
For example, for n>=3,

    ((n-1)!-1)/(n!-1)

is positive, has reduced denominator coprime to n!, and its product with n
tends to one. This example is elementary explanatory analysis here, not a
new Lean theorem or an example of the original exact tail recurrence.

No argument converts the new roughness bound into infinitely many changes
of the original carry or GCD approximants. The conjecture remains unproved
and undisproved in this workspace.

A renewed reference retrieval also failed: a direct DNS-over-HTTPS request
to 1.1.1.1 timed out. No external paper or claimed resolution was retrieved.
