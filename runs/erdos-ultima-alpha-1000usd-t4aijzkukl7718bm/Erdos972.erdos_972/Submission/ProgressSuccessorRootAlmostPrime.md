# Successor-root improvement: 24576 output factors

The original conjecture is still unresolved. `Submission/Spec.lean` is
unchanged and retains its original `sorry`. This is a stronger almost-prime
result, not a proof or a disproof of prime-pair infinitude.

## New file

`Submission/SuccessorRootAlmostPrime.lean`

Namespace: `Erdos972SuccessorRootAlmostPrime`.

The old proof replaced the exact root bound

    u < (fastRoot(u)+1)^4096

by `u <= fastRoot(u)^8192`, losing a factor of two in the exponent.
The new proof retains the successor. For `Z=fastRoot(u)`, `alpha <= Z`,
and `p <= u^6`, it proves

    floor(alpha*p) < (Z+1)^24577.

If the output is positive and coprime to `Z!`, every factor in its prime
factor list is at least `Z+1`, including repeated factors. Consequently
its factor-list length is strictly less than 24577, hence at most 24576.

## Verified results

- `factor_length_of_successor_bound`: the generic strict successor-power
  estimate, with multiplicity retained.
- `floor_output_successor_bound`: the exact-scale output size estimate.
- `rough_output_factor_bound`: combines these for actual rough outputs.
- `exists_prime_almostPrime_card_scale`: the existing logarithmic-order
  lower bound, now for at most 24576 output factors.
- `frequently_many_prime_almostPrime_pairs`: there is a positive constant
  `c` such that for every `B`, some `N>B` satisfies

      #{p<=N : p prime, Omega(floor(alpha*p)) <= 24576}
        >= c*N/(1+log(N+1))^2.

- `exists_prime_almostPrime_beyond` and
  `infinite_prime_almostPrime_inputs`: infinitude for every irrational
  `alpha>1` with the sharper bound.

The existing positive constant `roughConstant` is retained; its older
49153-factor majorant cap is still a valid bound. No claim is made that
this counting constant has been optimized.

## Verification and limitations

The file compiles. All four principal printed axiom audits list only
`propext`, `Classical.choice`, and `Quot.sound`. No source holes or new
axioms are present.

This improves the previously proved 49153-factor weakening. It does not
improve the arithmetic divisor-row level, break the sieve parity
obstruction, or replace the required factor bound by one. No completed
proof of the original conjecture has been submitted.
