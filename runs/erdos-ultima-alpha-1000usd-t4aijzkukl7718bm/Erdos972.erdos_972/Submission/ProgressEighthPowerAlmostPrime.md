# Flexible lower-sieve margin: 12288 output factors

The original conjecture remains unresolved. `Submission/Spec.lean` is
unchanged, with its original `sorry`. No prime-pair theorem or irrational
counterexample is claimed.

## FlexibleLowerSieve.lean

Namespace: `Erdos972FlexibleLowerSieve`.

The capped finite lower sieve now retains an arbitrary positive margin
parameter `A`. Under its explicit divisor-row, nonnegativity, and cap
hypotheses, it proves

    lowerMain(R,Z) >= 1/(A*G(R)),
    E <= N/(8*A*v),  R^3*Z <= v
      ==> rough weight >= N/(4*A*C*G(R)),

where `C>0` caps the Selberg majorant on rough outputs. The logarithmic
version replaces the last denominator by

    12*A*C*(1+log(R+1)).

No error is discarded: reducing the main-term fraction requires the
correspondingly stronger error budget.

The existing bounds `primeCost(Z) <= (5/4)log Z` eventually and
`G(Z^8) >= 4 log Z` imply

    lowerMain(Z^8,Z) >= 1/(16*G(Z^8))

at every sufficiently large `Z`. This permits an eighth power in place of
the old sixteenth power.

## EighthPowerAlmostPrime.lean

Namespace: `Erdos972EighthPowerAlmostPrime`.

Define `wideRoot(u)=root32(root64(u))`. Then

    Z <= wideRoot(u) <-> Z^2048 <= u.

For `Z=wideRoot(u)` and `R=Z^8`,

    R^3*Z = Z^25 <= Z^32 <= root64(u).

The exact successor-root estimate gives

    u < (Z+1)^2048,
    floor(alpha*p) < (Z+1)^12289

when `alpha<=Z` and `p<=u^6`. If the positive output is coprime to `Z!`,
every prime factor, including repetitions, is at least `Z+1`. Hence the
output has at most **12288** prime factors counted with multiplicity.

The scale proof fixes every eventual threshold first, then uses ONE
`exists_small_prime_prefix_rows` selector with epsilon `1/64`. Its budget
`2*root64(u)*E <= u^6/64` gives precisely the required
`E <= u^6/(128*root64(u))`. Both the sieve rows and the quantitative
proper-prime-power correction are retained.

With the fixed positive constant

    eighthConstant = 192*majorantCap(12288),

it proves, at arbitrarily large actual irrational scales,

    rough prime-input weight >= u^6/[eighthConstant*(1+log(u+1))],

and a counting lower bound

    #{p<=u^6 : p prime, Omega(floor(alpha*p))<=12288}
      >= u^6/[6*eighthConstant*(1+log(u+1))^2].

`exists_prime_almostPrime_beyond` and
`infinite_prime_almostPrime_inputs` establish the corresponding infinitude
for every irrational `alpha>1`.

## Verification and remaining gap

Both files compile. The principal printed axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. No new axiom or source
proof hole was added.

This is a genuine improvement in roughness radius and in the almost-prime
factor bound, from 24576 to 12288. It does not extend the arithmetic
prime-input divisor-row level, estimate the missing signed correlation,
or certify primality of the output. The original task is not completed,
and no incomplete proof was submitted.
