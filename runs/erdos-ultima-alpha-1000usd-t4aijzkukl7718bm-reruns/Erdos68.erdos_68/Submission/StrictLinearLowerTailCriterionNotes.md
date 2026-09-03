# A strict linear lower-tail criterion

This is verified auxiliary progress, not a settlement of Erdős 68.
`Submission/Spec.lean` remains unchanged with its original sorry. No proof
or disproof of that conjecture has been submitted.

Both `StrictLinearLowerTailCriterion.lean` and
`StrictLinearLowerTailExamples.lean` compile, have built oleans, and contain
no holes. Their printed principal axiom audits use only propext,
Classical.choice, and Quot.sound.

## Local theorem

Let t_n be integers, let p>0, L>=2 and H>=0 be natural numbers, and suppose:

    t_p = p*t_(p-1)-1,
    t_(p+L) = (p+L)*t_(p+L-1)-1,
    n divides t_(n+1)-t_n+1  for p<=n<p+L,
    -2n < t_n <= H          for p<=n<=p+L.

Then the size condition

    L*H + p*L + 2*L^2 + L < p^2

is impossible. This is `no_close_unit_returns` in the new namespace.

### Proof mechanism

Set s_0=t_(p-1)+1 and

    s_(i+1)=s_i+(t_(p+i+1)-t_(p+i)+1)/(p+i),
    S_i=sum_(j=1)^i s_j.

The quotients are integers by the congruence. Induction proves

    t_(p+i)+(p+i)+1=(p+i)*s_i-S_i.

The first unit recurrence and the strict lower bound imply s_0>=0.
If S_i>=0 and s_(i+1)<=-1, the identity implies

    t_(p+i+1)<=-2(p+i+1),

a contradiction. Hence all s_i and S_i in the interval are nonnegative.
The upper bound yields

    p*S_L <= L*(H+p+L+1+S_L).

The size condition implies S_L<p+L. The final unit recurrence gives
(p+L)|S_L, hence S_L=0. All s_i for 1<=i<=L therefore vanish.
Because L>=2, the identities at L-1 and L contradict the last unit
recurrence.

## Global criterion

`irrational_of_local_tails_and_unit_pairs` applies this obstruction to
integer factorial-series coefficients, with the local bounds holding on
arbitrarily large chosen unit-index intervals.

The theorem `irrational_of_sqrt_tails_prime_coefficients` proves that

    sum c_n/n!

is irrational if, eventually,

    n divides c_(n+1)-1,
    c_p=1 at every prime p,
    -2n < T_n <= C*n*(floor(sqrt(n))+1),

where T_n is the factorial-scaled tail. It uses the existing close-prime-pair
lemma and an explicit local bound with H=8*C*a*floor(sqrt(a)), p=a+1.
The primes are sufficiently large to be odd, so their positive gap is at
least two.

This improves the earlier fixed-negative-lower-bound criterion. It does
not impose coefficient nonnegativity, and no representation of the original
series satisfying all these hypotheses is known.

## Verified sharpness examples for the local statement

`adjacent_unit_exception` uses p=10, L=1, H=0 and

    t_9=0, t_10=-1, t_11=-12.

The congruence, strict lower bound, unit recurrences, and size inequality
all hold. Thus L>=2 cannot simply be replaced by L>0.

`non_strict_lower_exception` uses p=10, L=4, H=0 and

    t_9=-1, t_10=-11, t_11=-22, t_12=-12, t_13=-1, t_14=-15.

All local conditions hold with -2n<=t_n instead of -2n<t_n. Equality occurs
at n=11. Thus the strict lower bound is essential for this local theorem.
These are finite auxiliary counterexamples, not disproofs of the original
conjecture or of any asserted global prime-coefficient statement.

## Remaining problem

The Lambert representation has the required arithmetic but excessively
large tails. The rowwise-floor representation has sublinear positive tails
but lacks the required congruences and prime coefficients. The new lower
bound does not remove this application gap. An infinite argument for the
exact original series remains necessary.
