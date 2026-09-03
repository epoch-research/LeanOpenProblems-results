# Actual signed dilation comparison — original conjecture still unresolved

New file: `PrimeOutputDilationReduction.lean`, namespace
`Erdos972PrimeOutputDilationReduction`. It compiles and depends only on the
permitted axioms, as shown by the principal declaration audits.

## Finite algebra and retained errors

- `exists_large_prime_harmonicMass_above`: the finite prime amplifier can
  have arbitrarily large reciprocal mass while excluding any prescribed
  initial prime range.
- `moebius_prime_dilation_error`:

      |mu(p*m)+mu(m)| <= 2 * 1_{p|m},  for prime p.

- `square_row_reindex` translates the exceptional p|m terms exactly into
  p^2-divisible original inputs.
- `signed_row_dilation_error`: for any nonnegative input weight a,

      |sum_{n<=N,p|n} a(n)mu(n)
        + sum_{m<=N/p} a(p*m)mu(m)|
        <= 2 sum_{n<=N,p^2|n} a(n).

- `output_signed_dilation_error` and `sum_output_dilation_error` apply this
  to the actual output Mangoldt weight.
- `reciprocal_square_sum_le` and `dilation_error_budget` bound the total
  square-divisibility error using the actual divisor rows. It is not dropped.

## Unconditional selected-scale result

Define

    M(alpha,N) = sum_{1<=n<=N} mu(n) Lambda(floor(alpha*n)).

`exists_prime_dilation_comparison` proves: for every alpha>1 irrational and
positive epsilon, there is a fixed finite prime set P, H=sum_{p in P}1/p>0,
such that at arbitrarily large selected cutoffs N,

    |M(alpha,N) + (1/H) sum_{p in P} M(alpha*p, floor(N/p))|
       <= epsilon*N.

The amplifier is selected before N. The existing prime-output rows on a
common irrational good scale control both the weighted replacement error
and the square-divisibility error. This result has no unproved distribution
hypothesis in its statement.

## Remaining limitation

The comparison does NOT prove cancellation of the signed sums on either
side. Nor does a qualitative bounded-source Mobius comparison directly
provide the prime-input Mangoldt correlation required by the conjecture.
No sufficient new lower bound or irrational counterexample was found.
Spec.lean remains unchanged with its original sorry, and no incomplete
proof was resubmitted.
