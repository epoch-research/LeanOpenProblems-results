# Sharper Selberg normalization and 6144-factor output theorem

The original conjecture remains unresolved. `Submission/Spec.lean` is
unchanged and still contains its original `sorry`. No prime-pair theorem
or irrational counterexample is asserted.

## SharpSieveMassLower.lean

Namespace: `Erdos972SharpSieveMassLower`.

The new theorem is the exact elementary bound

    (harmonic R : Real) <= sieveMass R,

improving the former factor-two bound. Consequently

    log(R+1) <= sieveMass R.

The proof groups each positive integer by its squarefree radical, the
product of its distinct prime factors. For squarefree `d`, the reciprocal
sum over any finite collection of multiples of `d` having no prime factors
outside `d.primeFactors` is at most `1/totient(d)`. This is obtained from
the convergent finite-prime Euler product for reciprocal smooth numbers.
Every integer `n<=R` has radical at most `R`, so summing the fiber bounds
gives exactly `sum_{d<=R} mu(d)^2/totient(d)`.

Principal declarations:

- `hasSum_factored_reciprocal`
- `reciprocal_multiples_factored_bound`
- `radical_fiber_reciprocal_bound`
- `harmonic_le_sieveMass`
- `log_le_sieveMass`

This argument uses no prime number theorem or new distribution estimate.

## FourthPowerAlmostPrime.lean

Namespace: `Erdos972FourthPowerAlmostPrime`.

The sharper mass bound gives `G(Z^4) >= 4 log Z`. Combining it with the
existing eventual `primeCost(Z) <= (5/4)log Z` proves

    lowerMain(Z^4,Z) >= 1/(16*G(Z^4)).

The flexible-margin lower sieve therefore applies with `R=Z^4`, using
the same `1/16` margin and the same stronger row-error budget as the
previous eighth-power version.

Define `quarterRoot(u)` by four square roots of `root64(u)`. Then

    Z <= quarterRoot(u) <-> Z^1024 <= u.

At `Z=quarterRoot(u)`,

    R^3*Z = Z^13 <= Z^16 <= root64(u).

The exact successor-root inequality gives, for `alpha<=Z` and `p<=u^6`,

    floor(alpha*p) < (Z+1)^6145.

On outputs coprime to `Z!`, each prime factor with multiplicity is at least
`Z+1`. The output-factor count is therefore at most **6144**.

The file proves for every irrational `alpha>1`:

- a positive logarithmic-order genuine prime-input / rough-output weight
  at arbitrarily large actual scales;
- the associated cardinality lower bound for outputs with at most 6144
  prime factors;
- prime inputs beyond every threshold with this factor bound;
- infinitude of those inputs.

All eventual thresholds precede a single common good-row selector. The
row error includes proper prime powers and satisfies the required bound
`E <= u^6/(128*root64(u))`. The new positive constant is

    fourthConstant = 192*majorantCap(6144).

## Verification and limits

Both files compile. All principal printed axiom audits list only
`propext`, `Classical.choice`, and `Quot.sound`. Neither new file contains
`sorry`, `admit`, or an added axiom.

The strongest proved factor bound is now 6144, improving 12288. This is
still not one. The work does not extend the prime-input divisor-row level
or estimate the missing signed correlation. It is not a settlement of the
original conjecture, and no incomplete proof was submitted.
