# A combined modulus for omitted Lambert columns

Verified auxiliary arithmetic for the ORIGINAL Lambert coefficients, not a
settlement of Erdős 68. `Submission/Spec.lean` is unchanged and still has its
original `sorry`. No proof or disproof has been submitted.

`CombinedColumnModulus.lean` compiles without warnings, has a built olean, and
all seven printed principal axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.

## Definitions

For natural T,J put

    Q(T,j)=(floor(T/j)!)^j,
    D(T,J)=lcm_(J<j<=T) Q(T,j),
    M(T,J)=T!/D(T,J).

The lcm of the empty family is one. Each Q(T,j) divides T!, by multinomial
factorial divisibility. Consequently D divides T!, M is a positive integer,
and M*D=T! exactly. D is a common denominator, not an asserted reduced
denominator of a particular rational sum.

Let a_n be the original Lambert coefficient and a_(n,<=J) its restriction
to block counts n/d<=J, as in `LambertBlockPowerCongruence.lowBlockCoeff`.

## Verified congruence and signed sums

For every n<=T,

    (T!/n!)*a_n = (T!/n!)*a_(n,<=J)   modulo M(T,J).

Indeed, an omitted summand has j=n/d>J and d<=floor(T/j), so its denominator
(d!)^j divides Q(T,j), hence D. Its T!-scaled value is therefore a multiple
of M. The proof uses exact integer division, not a real or p-adic limiting
argument.

The congruence extends to arbitrary finite signed integer weights. If a full
scaled weighted coefficient form is divisible by M, its low-column form is
also divisible by M. No assertion that either form is zero is made.

If p is prime and T<(J+1)*p, then D is coprime to p. Thus EVERY p-power
dividing T! also divides M. This aggregates the large-prime powers into one
modulus while retaining any additional small-prime factors.

A Lean-verified exact example is

    D(12,2)=41472,
    M(12,2)=11550=2*3*5^2*7*11.

The factors 2 and 3 are below the large-prime cutoff 12/(2+1)=4. No external
numerical computation is needed for this instance.

## Maximality and a necessary size check

For every m dividing T!, the file proves

    m divides M(T,J)
      iff m divides T!/Q(T,j) for every J<j<=T.

Thus M is the largest modulus obtainable by requiring divisibility of all
these individually cleared column quotients. This is NOT maximality for
an actual weighted sum, where further cancellation may occur.

When J<T, the first omitted column alone gives the verified upper bound

    M(T,J) <= T!/(floor(T/(J+1))!)^(J+1).

One cannot ignore this denominator and treat the aggregation as providing
an unrestricted extra factorial-sized modulus.

## Principal declarations

* `scaled_coefficient_congruence`
* `factorial_prime_power_dvd_modulus`
* `weighted_difference_divisible`
* `low_form_divisible`
* `maximal_modulus`
* `modulus_le_first_column_quotient`
* `exact_modulus_example`

## Missing application

The new divisibility statement has not been combined with an adequate
normalized size bound or a quantitative rank/nonvanishing theorem for the
boundary-clearing lattice. In particular, neither divisibility nor a
nonzero weight vector proves that the form's value at the target is nonzero.
The earlier small-or-zero construction still has that gap.

A review of simultaneous low-column determinants, factorial recurrences,
and the costs of cancelling rows and columns supplied no complete new
irrationality argument. Those informal considerations have not been
promoted to asymptotic theorems. No computation is running or awaiting audit.
The temporary API-check file was removed. The original conjecture remains
unproved and undisproved in this workspace.
