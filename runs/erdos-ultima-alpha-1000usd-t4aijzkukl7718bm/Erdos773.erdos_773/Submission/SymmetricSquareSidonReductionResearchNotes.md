# Reflection-symmetric reduction for the unrestricted square-Sidon problem

The original conjecture remains UNSETTLED. Spec.lean was not edited and
still has its one sorry for 0 < epsilon < 1/3. No incomplete proof was
submitted.

## Verified module

`SymmetricSquareSidonReduction.lean` imports only FormalConjecturesUtil.
It builds without warnings or admissions, and its five principal axiom
audits use only propext, Classical.choice, and Quot.sound.

Namespace: `Erdos773.SymmetricSquareSidonReduction`.

The predicate `Symmetric s A` means that every a in A satisfies a<=s and
s-a is also in A. Thus the reflection center is s/2; natural subtraction
is explicitly protected by the upper bound.

## Finite extraction

For an ARBITRARY A subset [1,N], put

    symmetricPart(A,s) = {a in A : a<=s and s-a in A}.

Ordered root pairs (including diagonals) with sum s are in bijection with
this symmetric part. Partitioning all ordered pairs by their sum yields

    |A|^2 = sum_{s=1}^{2N} |symmetricPart(A,s)|.

Consequently `exists_large_symmetric_part`, for N>0, gives s in [1,2N]
and B subset A such that B is symmetric about s/2 and

    |A|^2 <= 2N |B|.

`extract_symmetric_sidon` retains actual square-Sidonness by containment.
No fullness, residue-distribution, or interval hypothesis on A beyond
A subset [1,N] is used.

## Exact near-linear equivalence

`near_linear_iff_symmetric` proves equivalence of the original quantified
near-linear proposition with the same eventual exponent target for actual
reflection-symmetric root sets.

The forward implication takes a maximizing root set (proved to exist in
`maximizing_roots`) at exponent loss epsilon/4, then applies extraction.
The inequality gives |B| >= (1/2) N^(1-epsilon/2); eventually
N^(epsilon/2)>=2 absorbs the factor one half. The converse uses the
symmetric set directly as a witness for the ordinary Sidon maximum.

Neither side of this equivalence is proved. In particular this is not a
new near-linear construction.

## Conditional upper-bound transfer

`uniform_symmetric_bound_transfers` proves that a bound |B|<=K for EVERY
symmetric Sidon root set inside [1,N], at EVERY center s in [1,2N], implies
|A|^2<=2NK for every original Sidon root set A.

`symmetric_power_bound_transfers` gives the real-valued version:

    (forall such symmetric B, |B|<=C N^alpha)
       ==> M(N)^2 <= 2C N^(alpha+1).

`not_near_linear_of_symmetric_power_upper` proves that an eventual bound
of this kind with fixed alpha<1 would negate the original proposition.
Its upper-bound assumption remains explicit and UNPROVED. The proof takes
original exponent loss (1-alpha)/4 and uses the divergent power
N^((1-alpha)/2) to contradict the squared maximum bound.

This is a potential restricted upper-bound target, not an actual disproof.
Symmetry alone has not supplied such an upper bound. No original exponent
above two thirds was obtained.

## Logs and final-file state

- /tmp/symmetric-square-reduction.log
- /tmp/symmetric-square-reduction-build.log

Spec.lean remains at SHA-256
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
Its sole admission remains at line 17287.
