# Exact fixed-block replication of logarithmic limits

## Original task status

The conjecture is still neither proved nor disproved. `Submission/Spec.lean`
is unchanged and retains its original `sorry`. No proof submission was made.

## New checked file

`BlockReplicationLimitExplore.lean` compiles without warnings and has a current
olean. Its thirteen declarations (including the two definitions) are audited
in `BlockReplicationLimitAudit.lean`; the saved log uses only the permitted
axioms.

For M>0 define

    replicate(M,A) = {n : floor(n/M) belongs to A}.

The exact ordinary-integer formulas are

    r_replicate((q+1)M+t)
      = (t+1) r_A(q+1) + (M-t-1) r_A(q),  0<=t<M,

and, for every q>=0,

    r_replicate(qM+M-1) = M r_A(q).

Thus there is an entire residue subsequence on which no averaging occurs.

The principal result is

    r_replicate(n)/log n -> M*c
       iff
    r_A(n)/log n -> c.

The forward direction follows by dividing the exact last-digit subsequence;
the reverse direction uses the two carry terms and a checked finite-residue
limit lemma. No residue-wise equidistribution of A, disjoint-translate
assumption, or statistical independence is needed.

## Consequence and limitation

Fixed full-block replication amplifies an existing coefficient, but cannot
create convergence from a nonconvergent input. It does not normalize the
coefficient while reducing its relative fluctuations. This diagnoses the
specific replication operator, not all smoothing operations and not all
possible witnesses to the conjecture.

The broader reviews in this continuation did not produce an all-scale
construction or a universal contradiction. In particular the proposed Sidon
extraction is already refuted for bounded sum caps by SidonGridExplore, and
the growing-memory digit approach has no actual construction here. The main
finite-to-infinite and Boolean-rounding gaps remain unresolved.
