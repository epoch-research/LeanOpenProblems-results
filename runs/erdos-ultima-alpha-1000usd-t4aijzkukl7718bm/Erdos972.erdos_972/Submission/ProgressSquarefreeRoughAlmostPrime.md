# Squarefree rough almost-prime outputs — verified, not a settlement

`Submission/Spec.lean` remains unchanged with its original `sorry`.
No complete proof or irrational counterexample has been found or submitted.

## New file

`Submission/SquarefreeRoughAlmostPrime.lean`
Namespace `Erdos972SquarefreeRoughAlmostPrime`.

The file compiles without errors or warnings. All seven principal printed
axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`.

## Removing every repeated prime factor

Let W(alpha,Z,N) be the logarithmic prime-input weight whose output is
coprime to Z!, and let W_sf be the same weight with squarefree output.
For alpha>=1 and 0<Z<=N, the file proves

    W(alpha,Z,N) - W_sf(alpha,Z,N)
      <= log(N) * floor(alpha*N) / Z.

This uses `MappedSquarefreeDivisorExpansion.mapped_squarefree_tail`.
On an output coprime to Z!, the square-divisor truncation through Z is
exactly 1, since no 1<d<=Z can have d^2 dividing that output. The output cap
is retained: it is floor(alpha*N), not N.

The proof also establishes, for every fixed C>0 and natural k,

    C * (1+log(u+1))^k / quarterRoot(u) -> 0.

At N=u^6 and Z=quarterRoot(u), the repeated-factor loss is therefore at
most half of the existing logarithmic-order lower bound, eventually.
The error threshold is selected BEFORE the actual good-scale selector.
There is no intersection of separately existential scales.

## Actual quantitative results

For irrational alpha>1, at arbitrarily large actual scales N=u^6,

    W_sf(alpha,quarterRoot(u),u^6)
      >= u^6 / [2 * fourthConstant * (1+log(u+1))].

Consequently,

    #{p<=u^6 : p prime, floor(alpha*p) squarefree,
                 Omega(floor(alpha*p)) <= 6144}
      >= u^6 / [12 * fourthConstant * (1+log(u+1))^2].

Here `fourthConstant` is the same constant from `FourthPowerAlmostPrime`.
Thus all nonsquarefree outputs are removed at a factor-two cost, without
worsening the factor count bound. The corresponding input set is infinite.

## Fixed-count refinement

`exists_fixed_squarefree_rough_count` proves that one fixed k in [1,6144]
works for every input threshold B and roughness threshold Z: some prime
p>B has squarefree output, exactly k factors, and output coprime to Z!.

`fixed_squarefree_composite_count_of_finite` proves that a counterexample
to the original conjecture would admit such a fixed k in [2,6144], with
every output prime divisor exceeding Z. Squarefreeness now excludes all
proper prime powers, and the factors counted with multiplicity are distinct.

This strengthens `FixedRoughFactorCount`, which did not assert squarefreeness.
It does NOT eliminate squarefree composites or force the count to be one.

## Principal declarations

* `squarefree_rough_weight_loss`
* `quarterRoot_log_div_tendsto`
* `exists_squarefree_rough_log_scale`
* `exists_squarefree_rough_almostPrime_beyond`
* `infinite_prime_squarefree_almostPrime_inputs`
* `exists_fixed_squarefree_rough_count`
* `fixed_squarefree_composite_count_of_finite`
* `exists_squarefree_almostPrime_card_scale`

## Remaining gap

The original prime-output conclusion is still unproved. In particular,
squarefree semiprimes with large prime factors are not excluded by these
estimates. No argument has been found that reduces the fixed factor count
while retaining the prescribed slope, or supplies the missing signed
prime-pair correlation lower bound.

Verification command:

    lake env lean -o .lake/build/lib/lean/Submission/SquarefreeRoughAlmostPrime.olean Submission/SquarefreeRoughAlmostPrime.lean
