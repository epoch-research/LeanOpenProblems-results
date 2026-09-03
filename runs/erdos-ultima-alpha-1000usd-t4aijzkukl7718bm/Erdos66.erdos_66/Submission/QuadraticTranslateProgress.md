# Collision-free quadratic-translate anchor

## Original task status

The conjecture in Submission/Spec.lean remains unproved and undisproved.
The original import, statement, and sorry are unchanged. No main proof is
submitted. SHA256 remains

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## New verified finite construction

For an arbitrary finite U in an odd finite field F of order p, define

    B(U) = {(u+k^2,k) : u in U, k in F}.

Unlike the intercept curves u+k^2/u, these curves are disjoint. Exactly:

    (x,0) in B(U) iff x in U,
    |B(U)| = p |U|.

No translation, nonzero-label, opposite-label, or field-size assumptions
are needed. One explicit map U -> B(U) works for all parameter sets jointly.
At every plane target (q,t), its actual mixed set count is

    r_(B(U),B(V))(q,t)
      = |U||V| + chi(2) sum_(u in U,v in V) chi(q-t^2/2-u-v).

The already available quadratic-character correlation identity gives

    sum_x [sum_(v in V) chi(x-v)]^2 = p|V|-|V|^2.

Cauchy-Schwarz therefore proves

    [sum_(u in U,v in V) chi(q-u-v)]^2
      <= |U|(p|V|-|V|^2) <= p|U||V|.

Consequently, for EVERY U,V and EVERY target,

    |r_(B(U),B(V))(z)-|U||V|| <= sqrt(p|U||V|).

In particular the self-error is at most sqrt(p)|U|. These are actual
set counts, with no collision correction and no exceptional target.

The natural encoding x.val+p*y.val preserves arbitrary old membership and
ordinary sumRep below p exactly. No full field count is identified with an
ordinary count above p.

## Checked high-density usefulness

For any hypothetical witness A,c of the original conjecture:

    N/count(A,N)^2 -> 0,
    sqrt(N)/count(A,N) -> 0.

Thus for every epsilon>0, at all sufficiently large prime p, ALL complete
plane counts of B(prefixParameters(A,p)) differ from count(A,p)^2 by at
most epsilon*count(A,p)^2.

This closes the previous finite high-density collision issue by changing
the curve family, rather than improving the cubic incidence certificate.
It does NOT assert that the old cubic certificate became stronger.
For small parameter sets h << sqrt(p), the new bound is uninformative;
the earlier intercept construction remains useful in different regimes.

## Mass and infinite-construction limitation

The full lift has p*count(A,p) points below p^2. If contained in A, it forces

    p*count(A,p) <= count(A,p^2).

The previously checked counting profile forbids this at all sufficiently
large p. This is verified for the new lift in
`eventually_no_full_quadratic_lift`. It is a restriction on retaining the
ENTIRE lift, not a disproof of the conjecture or an exclusion of thinning.

The complete plane mean count(A,p)^2 is of order p log p, not log(p^2).
Thus solving the finite high-density flatness issue does not solve the
mean/mass mismatch, row-dependent tapering, ordinary carries, or changing-
scale compatibility. None of those missing steps is claimed here.

## Files and verification

All three production files compile without warnings and have current oleans:

* PaleyBilinearExplore.lean
* QuadraticTranslateAnchorExplore.lean
* QuadraticTranslateScaleExplore.lean

QuadraticTranslateAudit.lean audits 28 declarations. Its saved log reports
only propext, Classical.choice, and Quot.sound. The production files have no
sorries or added axioms. PaleyChecks.lean and AnchorScaleChecks.lean are
scratch API checks, not production dependencies; the former has an
intentional failed name check.

No main proof or exact-negation theorem is ready for submission.
