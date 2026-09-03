# Uniform quadratic-residue density and exact modular certificates

This does NOT settle Erdős 773. Spec.lean is unchanged and still has its
sole admission for 0<epsilon<=1/3. No proof submission has been made.

`QuadraticResidueDensityLower.lean` imports the clean elementary modular
sieve and divisor-bound modules, not Spec.lean. It compiles without errors
or warnings, has a built .olean, and its eleven printed axiom audits use
only propext, Classical.choice, and Quot.sound.

## Uniform finite bound for every positive modulus

Let R(q) count square residues modulo q, and let rho(q)=R(q)/q. Then

    q <= 2*tau(q)*R(q),
    1 <= 2*tau(q)*rho(q).

Here tau(q)=q.divisors.card. No primality, oddness, squarefreeness, or
prime-power hypothesis is used.

Proof ingredients:

* `linear_zero_card`: the kernel of multiplication by a in ZMod q has
  cardinality gcd(q,a), using the Mathlib cyclic additive-group theorem.
* `linear_fiber_card`: every other fiber has at most that cardinality.
* `multiples_card`: among canonical residues, at most q/d have values
  divisible by d, for d dividing q.
* `sum_gcd_bound`: sum_x gcd(q,x.val) <= q*tau(q).
* `zero_products_bound`: at most q*tau(q) residue pairs satisfy xy=0.
* `square_energy_bound`: at most 2*q*tau(q) pairs satisfy x^2=y^2.
  The map (x,y)->(x-y,x+y) lands in the zero-product pairs and has fibers
  of size at most gcd(q,2)<=2, including at even moduli.
* `energy_cauchy`: q^2 <= R(q) * number_of_square_collision_pairs.
* `residue_card_lower`, `residue_density_lower` combine these estimates.

This count concerns congruent SINGLE squares, not equal sums of two
integer squares. Do not confuse the energy here with the original
four-root collision hypergraph.

## Uniform subpower consequence

Combining the finite estimate with the existing divisor bound gives
`density_subpower`:

    for every delta>0, there is C>0 such that
    1 <= C*q^delta*rho(q) for every positive q.

`density_uniform` strengthens the quantifiers to a common threshold:
for every epsilon>0, eventually in N,

    for EVERY 0<q<=N^2, N^(-epsilon) <= rho(q).

Thus the threshold is not allowed to depend on q.

## All the exact modular cardinality inequalities remain feasible

The existing upper-bound method proves that an actual Sidon square set of
cardinality M must satisfy, for each positive q,

    M^2 <= R(q)*(M + 2*floor(N^2/q) + 1).              (*)

`all_moduli_accept_subpower_card` proves that for every epsilon>0, eventually
in N, the REAL value M=N^(1-epsilon) satisfies (*) for ALL positive q.
There is no restriction to polynomially bounded q in this conclusion.

For q<=N^2, use the uniform density lower bound and

    N^2 <= q*(2*floor(N^2/q)+1).

For q>=N^2, the distinct squares of 0,...,N-1 are already distinct
canonical residues, giving R(q)>=N (`small_squares_card`).

`integer_cardinality_model` additionally proves:

    for every epsilon>0, eventually in N, there exists an INTEGER m with
    N^(1-epsilon) <= m <= N
    satisfying (*) simultaneously for every positive q.

The integer is a ceiling of a slightly larger power, chosen with a common
threshold for all q. The elementary `downward_feasible` lemma justifies
rounding within the allowed interval of a quadratic inequality.

## Exact scope

This is a limitation of the full FAMILY of the existing numerical modular
cardinality inequalities: those inequalities alone are compatible with
near-linear integer cardinalities, even with the modulus optimized freely.

It is NOT a Sidon-set construction, a converse to the modular upper bound,
an assertion that every such feasible integer is realizable, or a proof of
the original conjecture. It also does not obstruct stronger sieve methods
that retain information beyond these scalar inequalities. No actual
original lower exponent or original-conjecture disproof was obtained.

The original definitions were rechecked: maxSidonSubsetCard is exactly the
supremum of card over the Sidon subsets in the powerset, and IsSidon has the
usual unordered-pair uniqueness condition. No definitional mismatch was
found.

Logs:

    /tmp/quadratic-residue-density-lower.log
    /tmp/spec-density-lower-check.log
