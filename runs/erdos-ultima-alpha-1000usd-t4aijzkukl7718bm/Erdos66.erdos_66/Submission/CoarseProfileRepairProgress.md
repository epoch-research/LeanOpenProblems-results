# Fixed finite profile repair via coarse projection

## Original task status

Erdős 66 is not settled. `Submission/Spec.lean` remains unchanged, including
its original `sorry`. No proof or disproof has been submitted.

## Checked results

`CoarseCountingExplore.lean` defines a finite/infinite mixed count and proves

    r_(A union F)(n) = r_A(n) + 2 mixed(A,F,n) + r_F(n)

when A and F are disjoint. It defines the coarse projection

    coarse(A,M) = {floor(a/M) : a in A}.

For positive M, a representative-pair injection proves

    r_coarse(q) <= sum_{q*M <= z < (q+2)*M} r_A(z).

Thus r_A(z)<=K+C log(z+2) implies the explicit envelope

    r_coarse(q) <= 2M(K+C log(2M)) + 2MC log(q+2).

For tensor(M,P,S), with S contained in [0,M), the mixed counts satisfy

    mixed(A,tensor,n)
      <= |S| (mixed(coarse,P,n/M) + mixed(coarse,P,n/M-1)).

The predecessor term is retained even at quotient zero; this is harmless
for an upper bound. Coarse disjointness implies fine disjointness.

`CoarseProfileRepairExplore.lean` combines these estimates with the existing
localized repair theorem. Exact self and union counts at its coarse center
force the coarse mixed count there to vanish. Away from the center, the
union error budget bounds both the self and mixed components.

The quantitative lifting lemma incurs at most the factor 3|S|. The main
`eventually_fixed_profile_repair` fixes M,S,D,epsilon,K,C, with M>0,
all s in S below M, all s+t<M, D,K,C>=0, and epsilon>0. For EVERY sufficiently
large coarse center q, uniformly over sets A obeying the envelope and
integers m<=D log(q), it constructs F with:

- |F|=2m|S|;
- F disjoint from A;
- q*M<=4a and 3a<=(2q+6)M for a in F;
- at EVERY fine target n, after subtracting the designated profile

      if n/M=q then 2m r_S(n%M) else 0,

  the increment r_(A union F)(n)-r_A(n) lies between zero and
  epsilon log(n+2).

The proof uses coarse tolerance delta=epsilon/(3|S|+1).
Both files compile and have built oleans. `CoarseProfileRepairAxiomCheck.lean`
audits the principal theorems; only propext, Classical.choice, Quot.sound
occur.

## What this does not establish

The template S and width M are fixed BEFORE the sufficiently-large center
is chosen. The threshold depends on them. In particular the theorem cannot
be directly applied to the isolated annular packets of
`IsolatedAnnularPacketExplore.lean`, whose low templates grow with their
location. Nor does it cover the gaps between repair blocks or supply a base
with summably weighted deficits.

This resolves the previously proposed fixed-template coarse-repair step,
not the scale-transition problem or the original conjecture.
