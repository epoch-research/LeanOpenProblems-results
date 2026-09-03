# Uniform residue density and modular-inequality compatibility

This does not settle Erdős 773. The conjecture in `Spec.lean` is unchanged.

`ResidueDensityLower.lean` has three audited main results:

1. For every eta>0 there exists C>0 such that, for every positive modulus q,

       1 <= C * quadraticResidueDensity(q) * q^eta.

   The proof counts pairs of roots in [1,q] with congruent squares. Ordered
   increasing pairs are covered by the square-difference representations of
   q*k for 1<=k<=q. The divisor bound controls this count by C*q^(1+eta),
   and Cauchy--Schwarz gives the lower bound on residue density.

2. For every K,epsilon>0, eventually in N, uniformly over all positive q
   with q<=N^K,

       quadraticResidueDensity(q) >= N^(-epsilon).

3. For every fixed epsilon>0, eventually in N, simultaneously for EVERY
   positive q, the hypothetical number x=N^(1-epsilon) satisfies

       x^2 <= r(q) * (x + 2*floor(N^2/q) + 1),

   where r(q) is the number of quadratic residues modulo q. For q<=N^2,
   this follows from (2) and 2*q*floor(N^2/q)>=N^2. For q>N^2, the first
   N positive squares are distinct residues, so r(q)>=N>=x.

The third theorem is explicitly a consistency check for a family of
NECESSARY cardinality inequalities, not a Sidon construction. It proves
neither the desired bound on the actual maximum nor its negation. It does
not exclude stronger modular methods using information discarded by those
inequalities.

The module builds cleanly. All three printed audits contain only propext,
Classical.choice, and Quot.sound. Log: /tmp/residue-density-lower.log.
The temporary API-check module was removed.
