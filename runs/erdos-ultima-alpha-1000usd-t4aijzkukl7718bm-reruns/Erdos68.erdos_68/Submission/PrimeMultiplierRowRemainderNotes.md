# Prime rows at fixed even multiples of p-1

This is new verified auxiliary arithmetic, NOT a proof or disproof of
Erdős 68. `Spec.lean` remains unchanged with its original `sorry`.

`PrimeMultiplierRowRemainder.lean` compiles without warnings, has a built
olean, and contains no proof holes. All five printed principal axiom
audits list only `propext`, `Classical.choice`, and `Quot.sound`.

## Arithmetic numerator

For p prime, 0<j<=p, define

    C(p,j) = p*(j*(p-1))!/(p!)^j.

The division is proved exact. Indeed `(p-1)!^j` divides `(j*(p-1))!`, and
`p^(j-1)` also divides that factorial because `(j-1)*p<=j*(p-1)`.
These two divisors are coprime. Multiplying their product by p gives the
required factorial-power divisor.

For 0<j<p, `numerator_cast` proves

    C(p,j) == (-1)^(j-1) (mod p).

Let U=(p*j)!/(p!)^j. The existing multinomial prime-scaling congruence gives
U==j! modulo p. The new exact identity is

    U = C(p,j)*j*(p*j-1).descFactorial(j-1).

The descending product is `(-1)^(j-1)*(j-1)!` modulo p. Since p does not
divide j!, cancellation gives the displayed congruence. This uses no
unproved estimate for factorial residues.

## Exact fractional-part formula

For p prime, positive even j<p, and C(p,j)<p!-1, `row_formula` proves

    fract((j*(p-1))!/(p!-1))
      = 1-1/p + (j*(p-1))!/[(p!)^j*(p!-1)].

The final correction is strictly between zero and 1/p. The first j-1
geometric terms form an integer by multinomial divisibility. The next
term is C(p,j)/p, whose fractional part is exactly 1-1/p, and the
remaining geometric tail is the displayed correction.

The size hypothesis is eventually true for every fixed positive j:

    C(p,j) <= (2^(j^2+1))^p,

and factorial growth eventually dominates twice this exponential.
Consequently `eventually_row_formula` supplies the formula for every
sufficiently large prime, for each fixed positive even j.

## Consequences for the actual rowwise remainder

For the full original sum alpha, put

    T_n=n!*alpha-sum_(k=2)^n floor(n!/(k!-1)).

`tail_gt_one_sub_inv` gives T_(j*(p-1))>1-1/p under the same hypotheses.
`frequently_tail_gt` proves that for every fixed positive even j, every
real c<1, and every N, there is a prime p with

    N<=j*(p-1),  c<T_(j*(p-1)).

This extends the previously verified j=2 subsequence.

`finite_prime_rows_lower` proves the additive version. If a finite set s
of primes all give applicable even-multiplier rows at the SAME index n,
then

    sum_(p in s) (1-1/p) < T_n.

The strict inequality retains the positive omitted tail of the full target.
The file does NOT assert the existence of arbitrarily large simultaneous
prime configurations.

## Remaining gap

Rationality of alpha would make T_n a positive integer eventually. Neither
the single-row lower bounds nor the finite additive bound contradict that.
No infinite nonintegrality, GCD defect, carry-residue violation, or small
nonzero integer-form sequence has been proved here.

The original conjecture is still unresolved in this workspace. No proof
or disproof was submitted, and no computation or compilation is pending.
