# Prime-output dilation calculation — conjecture remains unresolved

Spec.lean is unchanged and still contains its original sorry. No sufficient
prime-pair lower bound or irrational counterexample was found in this phase.
No proof was submitted.

## New verified finite arithmetic

PrimeOutputDilates.lean, namespace Erdos972PrimeOutputDilates, imports only
FormalConjecturesUtil.

- floor_nat_mul_decompose: for x>=0 and a natural k, with m=floor(x),

      floor(k*x) = k*m + floor(k*(x-m)).

- prime_dilates_patterns: if floor(2*x) and floor(3*x) are prime and exceed
  2 and 3 respectively, their values and windows are one of

      (2*m+1, 3*m+1),   m+1/2 <= x < m+2/3;
      (2*m+1, 3*m+2),   m+2/3 <= x < m+1.

- prime_dilates_determinant: the corresponding integer determinant is

      3*floor(2*x) - 2*floor(3*x) = 1 or -1.

- prime_dilates_iff: for m>=2 and 0<=t<1, simultaneous primality of
  floor(2*(m+t)) and floor(3*(m+t)) is equivalent to primality of 2*m+1
  together with precisely the appropriate prime affine output and window
  above. This includes the converse, not just necessary conditions.

- infinite_affine_pairs_of_infinite_dilates: for alpha>=1, infinitude of
  natural n with both floor(2*alpha*n) and floor(3*alpha*n) prime implies
  infinitude of m with 2*m+1 prime and at least one of 3*m+1,3*m+2 prime.
  The antecedent is a hypothesis; no such infinitude is proved here.

All four principal theorems compile and print only propext,
Classical.choice, and Quot.sound in their axiom audits.

## Interpretation

This calculation identifies genuine two-prime affine patterns inside the
output-dilation correlations. Irrationality of alpha does not, by itself,
turn these correlations into the already proved one-prime row estimates.
Neither a positive asymptotic nor a vanishing centered correlation was
proved. The preceding generic unbounded dilation obstructions are still
relevant, but the present result is a separate exact floor calculation.

Further review of a Selberg-type symmetry identity across rationally related
slopes did not yield a usable propagation of exceptional slopes or a
correlation lower bound. No unproved symmetry or limit exchange was used.
A reference fetch again failed with DNS resolution failure; no new claim
about the external literature status is made.
